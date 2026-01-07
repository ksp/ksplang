use smallvec::{smallvec, SmallVec};
use rustc_hash::{FxHashMap as HashMap};

use crate::compiler::{
    cfg::{BasicBlock, GraphBuilder},
    ops::{BeforeOrAfter, BlockId, InstrId, OpEffect, OptInstr, OptOp, ValueId}, utils::{Annotations, union_range},
};

/// Hoists common instructions from following blocks of the specified predecessor block.
/// Returns true if any hoisting was performed.
pub fn hoist_up(g: &mut GraphBuilder, predecessor: BlockId) -> bool {
    let pred_block = g.block_(predecessor);

    let mut successors = pred_block.following_blocks();
    successors.sort();
    successors.dedup();
    let successors = successors;

    if successors.len() < 2 {
        return false; // TODO: merge?
    }

    for &succ_id in &successors {
        let succ_block = g.block_(succ_id);
        if g.conf.should_log(10) {
            println!("  Attempting hoisting from {succ_block}");
        }
        //   can't safely           would not be productive
        if !succ_block.is_sealed || succ_block.incoming_jumps.len() > 1 {
            return false;
        }
    }

    if g.conf.should_log(10) {
        println!("Running hoisting for {predecessor}: {successors:?}");
        println!("  Attempting hoisting into {pred_block}");
    }

    let mut hoisted_any = false;
    'main: loop {
        let mut candidate_instr = get_common_instructions(g, &successors);

        if candidate_instr.is_empty() {
            break;
        }

        candidate_instr.sort_by_cached_key(|(_, _, ids)| *ids.iter().max().unwrap());

        'candidate: for (op, inputs, instr_ids) in candidate_instr.iter() {
            assert_eq!(instr_ids.len(), successors.len(), "common instruction must exist in every successor block");
            if matches!(op, OptOp::Jump(_, _)) { continue }

            let mut aggregated_effect = OpEffect::None;
            let mut program_position = None;
            let mut ksplang_ops_increment = None;

            for iid in instr_ids.iter() {
                let block = g.block_(iid.0);
                let instr = &block.instructions[&iid.1];
                assert_eq!(&instr.op, op);

                if !can_hoist_from_block(g, block, iid.1, instr) {
                    continue 'candidate;
                }

                if matches!(op, OptOp::Checkpoint) && (
                    program_position.is_some_and(|p| p != instr.program_position) ||
                    ksplang_ops_increment.is_some_and(|p| p != instr.ksp_instr_count))
                {
                    // all checkpoints must point to the same location
                    continue 'candidate;
                }
                aggregated_effect = OpEffect::worse_of(aggregated_effect, instr.effect);
                program_position = Some(instr.program_position);
                ksplang_ops_increment = Some(instr.ksp_instr_count);
            }

            let Some(insert_pos) = choose_insert_position(g, predecessor) else {
                continue;
            };

            let new_iid = g.make_instr_id_at(insert_pos, |_| false).unwrap();
            assert!(!g.block_(predecessor).instructions.contains_key(&new_iid.1));

            let new_out = if op.has_output() {
                let output_values: Vec<ValueId> =
                    instr_ids.iter().map(|id| g.get_instruction_(*id).out).filter(ValueId::is_computed).collect();
                if output_values.is_empty() {
                    ValueId(0)
                } else {
                    let range = output_values.iter().map(|val| g.val_info_(*val).range.clone())
                        .reduce(|a, b| union_range(a, b)).unwrap();
                    let out_info = g.new_value();
                    out_info.range = range;
                    out_info.set_assigned_at(new_iid, op, inputs);
                    let new_out = out_info.id;
                    g.replace_values(output_values.iter().map(|v| (*v, new_out)).collect());
                    // TODO: copy all assumes or is it invalid?
                    new_out
               }
            } else {
                ValueId(0)
            };

            let hoisted_instr = OptInstr {
                id: new_iid,
                op: op.clone(),
                inputs: inputs.clone(),
                out: new_out,
                program_position: program_position.unwrap_or(usize::MAX),
                ksp_instr_count: ksplang_ops_increment.map_or(u32::MAX, |ctr| ctr + g.block_(predecessor).ksplang_instr_count),
                effect: aggregated_effect,
                annot: Annotations::default()
            };

            g.block_mut_(predecessor).instructions
                .insert(new_iid.instr_ix(), hoisted_instr.clone());

            for iid in instr_ids.iter() {
                let block = g.block_mut_(iid.block_id());
                let instr = block.instructions.remove(&iid.instr_ix()).unwrap();
                // remove from value-numbering to avoid crash on re-use
                if let Some(vn) = g.value_index.get_mut(&(instr.op, instr.inputs)) {
                    vn.retain(|x| x.1 != *iid);
                }
            }

            if g.conf.should_log(5) {
                println!("Hoisted {hoisted_instr} ({program_position:?}, {ksplang_ops_increment:?})");
            }

            hoisted_any = true;

            if hoisted_instr.op.is_terminal() {
                // remove all following instructions, mark following as unreachable
                let block = g.block_mut_(predecessor);
                block.outgoing_jumps.clear();
                block.instructions.split_off(&(hoisted_instr.id.1 + 1));
                for &f in &successors {
                    let b = g.block_mut_(f);
                    b.is_reachable = false;
                    assert!(1 >= b.incoming_jumps.len());
                    b.incoming_jumps.clear();
                }
            }
            continue 'main;
        }
        break;
    }

    hoisted_any
}

/// Find instructions that appear in all blocks, grouped by (op, inputs).
/// Returns Vec of (op, inputs, Vec of InstrIds from each block)
fn get_common_instructions(
    g: &GraphBuilder,
    blocks: &[BlockId]
) -> Vec<(OptOp<ValueId>, SmallVec<[ValueId; 4]>, SmallVec<[InstrId; 4]>)> {
    assert!(!blocks.is_empty());

    // find smallest block
    let starter_block = blocks.iter()
        .enumerate()
        .min_by_key(|&(_, &block_id)| g.block_(block_id).instructions.len())
        .map(|(idx, _)| idx)
        .unwrap();

    // Map: (op, inputs) -> SmallVec of Option<InstrIds> (one per block)
    let mut instruction_map: HashMap<(OptOp<ValueId>, SmallVec<[ValueId; 4]>), SmallVec<[Option<u32>; 4]>> = HashMap::default();

    let smallest_block = g.block_(blocks[starter_block]);
    for (_instr_idx, instr) in smallest_block.instructions.iter() {
        let key = (instr.op.clone(), instr.inputs.clone());
        instruction_map.insert(key, smallvec![None; blocks.len()]);
    }

    for (ix, &block_id) in blocks.iter().enumerate() {
        let block = g.block_(block_id);
        for (&instr_idx, instr) in block.instructions.iter() {
            let key = (instr.op.clone(), instr.inputs.clone());

            if let Some(entry) = instruction_map.get_mut(&key) {
                entry[ix].get_or_insert(instr_idx);
            }
        }
    }

    println!("DBG {:?}", instruction_map);

    // filter instructions that appear in ALL blocks
    instruction_map.into_iter()
        .filter_map(|((op, inputs), instr_indices)| {
            let res: Option<SmallVec<[InstrId; _]>> =
                instr_indices.into_iter().enumerate()
                    .map(|(ix, instr)| instr.map(|instr| InstrId(blocks[ix], instr)))
                    .collect();
            res.map(|instr_indices| (op, inputs, instr_indices))
        })
        .collect()
}

fn choose_insert_position(
    g: &GraphBuilder,
    predecessor: BlockId,
) -> Option<BeforeOrAfter<InstrId>> {
    let pred_block = g.block_(predecessor);

    let anchor = pred_block
        .instructions
        .iter().rev()
        .filter(|(_ix, instr)| !matches!(instr.op, OptOp::Jump(..)))
        .map(|(&ix, _)| ix)
        .next()
        .unwrap_or(0);

    Some(BeforeOrAfter::After(InstrId(predecessor, anchor)))
}

fn can_hoist_from_block(
    g: &GraphBuilder,
    block: &BasicBlock,
    instr_idx: u32,
    instr: &OptInstr,
) -> bool {
    if !matches!(instr.op, OptOp::Checkpoint) && instr.op.worst_case_effect() == OpEffect::None {
        return true
    }

    let mut prior_checkpoint = false;
    let mut prior_effect = false;
    for (_, prior) in block.instructions.range(..instr_idx) {
        prior_effect = prior_effect || prior.effect != OpEffect::None;
        prior_checkpoint = prior_checkpoint || matches!(prior.op, OptOp::Checkpoint);
    }

    if !prior_effect && !prior_checkpoint {
        return true
    }
    if matches!(instr.op, OptOp::KsplangOpsIncrement(_)) {
        return !prior_checkpoint
    }
    if matches!(instr.op, OptOp::Checkpoint) {
        return !prior_checkpoint && !prior_effect
    }
    if !matches!(instr.effect, OpEffect::None | OpEffect::MayFail) {
        return !prior_effect && !prior_checkpoint
    }


    // check the effect at start of the block
    //  - we need to be sure that the effect wasn't just masked by a preceeding
    //  - even though we move it into the previous block, checking start of the current block is sufficient
    //    For example:
    //      if (a != 0) { StackWrite(0, a); b / a } else { b / a }
    //    We can safely hoist (b / a), because:
    //      in block1: it cannot have an effect
    //      in block2: it's the first instruction, so moving the effect before branch does not change anything
    let op_ranges: Vec<_> = instr.inputs.iter().map(|&v| g.val_range_at(v, InstrId(block.id, 0))).collect();
    let effect_hoisted = instr.op.effect_based_on_ranges(&op_ranges);
    // println!("Judged {}  : {op_ranges:?}, result: {effect_hoisted:?}", instr);

    match effect_hoisted {
        OpEffect::None => true,
        // ok to swap error and checkpoint, since error is very unlikely
        // OpEffect::MayFail => !prior_effect,
        // TODO: should be valid, but is it actually a good idea?
        OpEffect::MayFail => if g.conf.error_as_deopt { true } else { !prior_effect },
        _ => false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::{cfg::GraphBuilder, ops::{OptOp, ValueId}, osmibytecode::Condition};

    // Test helpers to reduce verbosity
    fn push_branch(g: &mut GraphBuilder, cond: Condition<ValueId>, t: BlockId, f: BlockId) {
        g.push_instr(OptOp::Jump(cond, t), &[], false, None, None);
        g.push_instr(OptOp::Jump(Condition::True, f), &[], false, None, None);
    }

    fn push_with_deopt(g: &mut GraphBuilder, block: BlockId, op: OptOp<ValueId>, args: &[ValueId]) {
        g.switch_to_block(block, 0, vec![]);
        if args.is_empty() {
            g.push_instr(op, &[], false, None, None);
        } else {
            g.push_instr(op, args, false, None, None);
        }
        g.push_instr(OptOp::deopt_always(), &[], false, None, None);
    }

    fn graph_with_param(range: std::ops::RangeInclusive<i64>) -> (GraphBuilder, ValueId) {
        let mut g = GraphBuilder::new(0);
        let val_info = g.new_value();
        val_info.range = range;
        let param = val_info.id;
        g.stack.push(param);
        (g, param)
    }

    #[test]
    fn test_hoist_pure_instruction() {
        let (mut g, param) = graph_with_param(0..=10);

        // Create branching structure:
        // bb0: if param == 0 goto bb1 else goto bb2
        // bb1: add param, 1; ...
        // bb2: add param, 1; ...

        let bb1 = g.new_block(1, true, vec![]);
        let bb1_id = bb1.id;
        let bb2 = g.new_block(2, true, vec![]);
        let bb2_id = bb2.id;

        let bb0_id = g.current_block;
        push_branch(&mut g, Condition::EqConst(param, 0), bb1_id, bb2_id);

        push_with_deopt(&mut g, bb1_id, OptOp::Add, &[param, ValueId::C_ONE]);
        push_with_deopt(&mut g, bb2_id, OptOp::Add, &[param, ValueId::C_ONE]);

        // Both blocks should have the add instruction
        assert_eq!(g.block_(bb1_id).instructions.len(), 2);
        assert_eq!(g.block_(bb2_id).instructions.len(), 2);

        // Try to hoist
        let hoisted = hoist_up(&mut g, bb0_id);

        assert!(hoisted, "Should have hoisted the common instructions");

        // Both Add and deopt should be hoisted, leaving bb1 and bb2 empty
        assert_eq!(g.block_(bb1_id).instructions.len(), 0, "bb1 should be empty after hoisting");
        assert_eq!(g.block_(bb2_id).instructions.len(), 0, "bb2 should be empty after hoisting");

        // bb0 should have Add + deopt, and the old conditional jump should be removed (unreachable after deopt)
        let bb0_instrs: Vec<_> = g.block_(bb0_id).instructions.values().collect();
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::Add)), "Should have Add");
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::DeoptAssert(_))), "Should have deopt");
    }

    #[test]
    fn test_hoist_pop_with_nested_branches() {
        // Test case similar to the user's example:
        // bb0 -> bb1, bb2
        // bb1 -> Pop, then branches
        // bb2 -> Pop, then branches
        // Only the Pop should be hoisted to bb0 (jumps stay in successors)

        let mut g = GraphBuilder::new(0);
        let v1 = g.new_value().id;

        let bb1 = g.new_block(1, false, vec![]);
        let bb1_id = bb1.id;
        let bb2 = g.new_block(2, false, vec![]);
        let bb2_id = bb2.id;

        // bb0: branches based on v1
        let bb0_id = g.current_block;
        push_branch(&mut g, Condition::GtConst(v1, 4), bb1_id, bb2_id);

        // Create bb3 and bb4 for the second level of branches
        let bb3 = g.new_block(3, false, vec![]);
        let bb3_id = bb3.id;
        let bb4 = g.new_block(4, false, vec![]);
        let bb4_id = bb4.id;

        // bb1: Pop, then branch
        g.switch_to_block(bb1_id, 0, vec![]);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        push_branch(&mut g, Condition::GtConst(v1, 3), bb3_id, bb4_id);

        // bb2: Pop (same as bb1), then branch
        g.switch_to_block(bb2_id, 0, vec![]);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        push_branch(&mut g, Condition::GtConst(v1, 3), bb3_id, bb4_id);

        // Seal the blocks in the order they would be sealed during compilation
        g.seal_block(bb1_id);
        g.seal_block(bb2_id);

        // Both bb1 and bb2 should have 3 instructions (Pop + 2 jumps)
        assert_eq!(g.block_(bb1_id).instructions.len(), 3);
        assert_eq!(g.block_(bb2_id).instructions.len(), 3);

        // Try to hoist from bb0 (should hoist the Pop)
        let hoisted = hoist_up(&mut g, bb0_id);

        assert!(hoisted, "Should have hoisted instructions");

        // Only Pop should be hoisted; jumps remain in successors
        assert_eq!(g.block_(bb1_id).instructions.len(), 2, "bb1 should have its two jumps left");
        assert_eq!(g.block_(bb2_id).instructions.len(), 2, "bb2 should have its two jumps left");
        assert!(g.block_(bb1_id).instructions.values().all(|instr| matches!(instr.op, OptOp::Jump(..))), "bb1 should only contain jumps");
        assert!(g.block_(bb2_id).instructions.values().all(|instr| matches!(instr.op, OptOp::Jump(..))), "bb2 should only contain jumps");

        // bb0 should now have the Pop inserted before its existing jumps
        let bb0_instrs: Vec<_> = g.block_(bb0_id).instructions.values().collect();
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::Pop)), "Should have Pop");
        assert!(bb0_instrs.iter().filter(|i| matches!(i.op, OptOp::Jump(..))).count() >= 2, "Original jumps should remain");
        let targets: Vec<_> = g.block_(bb0_id).outgoing_jumps.iter().map(|(_, target)| *target).collect();
        assert!(targets.contains(&bb1_id) && targets.contains(&bb2_id), "Original branch targets should remain");
    }

    #[test]
    fn test_hoist_non_first_instruction() {
        // Test that we can hoist instructions that are not at the first position
        // bb0 -> bb1, bb2
        // bb1 -> Pop, Add, deopt
        // bb2 -> Pop, Add, deopt
        // Both Pop and Add should be hoisted

        let (mut g, param) = graph_with_param(0..=10);

        let bb1 = g.new_block(1, true, vec![]);
        let bb1_id = bb1.id;
        let bb2 = g.new_block(2, true, vec![]);
        let bb2_id = bb2.id;

        let bb0_id = g.current_block;
        push_branch(&mut g, Condition::EqConst(param, 0), bb1_id, bb2_id);

        // bb1: Pop, Max, deopt
        g.switch_to_block(bb1_id, 0, vec![]);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        push_with_deopt(&mut g, bb1_id, OptOp::Max, &[param, ValueId::C_ONE]);

        // bb2: different order - Add, Max, deopt
        g.switch_to_block(bb2_id, 0, vec![]);
        g.push_instr(OptOp::Add, &[param, ValueId::C_ONE], false, None, Some(OpEffect::None));
        push_with_deopt(&mut g, bb2_id, OptOp::Max, &[param, ValueId::C_ONE]);

        assert_eq!(g.block_(bb1_id).instructions.len(), 3);
        assert_eq!(g.block_(bb2_id).instructions.len(), 3);

        let hoisted = hoist_up(&mut g, bb0_id);

        assert!(hoisted, "Should have hoisted Max");

        // Should have hoisted Max (common instruction), leaving Pop + deopt in bb1 and Add + deopt in bb2
        assert_eq!(g.block_(bb1_id).instructions.len(), 2, "bb1 should have Pop + deopt left");
        assert_eq!(g.block_(bb2_id).instructions.len(), 2, "bb2 should have Add + deopt left");

        // bb0 should have Max hoisted before jumps
        let bb0_instrs: Vec<_> = g.block_(bb0_id).instructions.values().collect();
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::Max)), "Should have Max");
    }

    #[test]
    fn test_hoist_jumps() {
        // Test that we can hoist jumps, including conditional and unconditional
        // bb0 -> bb1, bb2
        // bb1 -> Pop, Jump(cond, bb3), Jump(true, bb4)
        // bb2 -> Pop, Jump(cond, bb3), Jump(true, bb4)
        // Only Pop should be hoisted; jumps stay in successors

        let mut g = GraphBuilder::new(0);
        let v1 = g.new_value().id;

        let bb1 = g.new_block(1, false, vec![]);
        let bb1_id = bb1.id;
        let bb2 = g.new_block(2, false, vec![]);
        let bb2_id = bb2.id;
        let bb3 = g.new_block(3, false, vec![]);
        let bb3_id = bb3.id;
        let bb4 = g.new_block(4, false, vec![]);
        let bb4_id = bb4.id;

        let bb0_id = g.current_block;
        push_branch(&mut g, Condition::GtConst(v1, 5), bb1_id, bb2_id);

        // bb1: Pop, then jumps to bb3 or bb4
        g.switch_to_block(bb1_id, 0, vec![]);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        push_branch(&mut g, Condition::GtConst(v1, 3), bb3_id, bb4_id);

        // bb2: Pop, then same jumps
        g.switch_to_block(bb2_id, 0, vec![]);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        push_branch(&mut g, Condition::GtConst(v1, 3), bb3_id, bb4_id);

        g.seal_block(bb1_id);
        g.seal_block(bb2_id);

        assert_eq!(g.block_(bb1_id).instructions.len(), 3);
        assert_eq!(g.block_(bb2_id).instructions.len(), 3);

        let hoisted = hoist_up(&mut g, bb0_id);

        assert!(hoisted, "Should have hoisted instructions");

        // Pop should hoist, leaving two jumps in each successor
        assert_eq!(g.block_(bb1_id).instructions.len(), 2, "bb1 should have jumps left");
        assert_eq!(g.block_(bb2_id).instructions.len(), 2, "bb2 should have jumps left");
        assert!(g.block_(bb1_id).instructions.values().all(|instr| matches!(instr.op, OptOp::Jump(..))), "bb1 should only have jumps");
        assert!(g.block_(bb2_id).instructions.values().all(|instr| matches!(instr.op, OptOp::Jump(..))), "bb2 should only have jumps");

        let bb0_instrs: Vec<_> = g.block_(bb0_id).instructions.values().collect();
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::Pop)), "Should have Pop");
        let jump_count = bb0_instrs.iter().filter(|i| matches!(i.op, OptOp::Jump(..))).count();
        assert_eq!(jump_count, 2, "Original two jumps should remain in predecessor");

        let targets: Vec<_> = g.block_(bb0_id).outgoing_jumps.iter().map(|(_, target)| *target).collect();
        assert!(targets.contains(&bb1_id) && targets.contains(&bb2_id), "Predecessor should still branch to bb1 and bb2");
    }

    #[test]
    fn test_hoist_pop_after_pure_instructions() {
        // Test that Pop can be hoisted even when preceded by effect-free instructions
        // bb0 -> bb1, bb2
        // bb1 -> Add, Pop, deopt
        // bb2 -> Add, Pop, deopt
        // Pop should be hoisted (Add is not common due to different input order or similar)
        
        let (mut g, param) = graph_with_param(0..=10);
        
        let bb1 = g.new_block(1, true, vec![]);
        let bb1_id = bb1.id;
        let bb2 = g.new_block(2, true, vec![]);
        let bb2_id = bb2.id;
        
        let bb0_id = g.current_block;
        push_branch(&mut g, Condition::EqConst(param, 0), bb1_id, bb2_id);
        
        // bb1: Max (effect-free), Pop (effectful), Add (may fail)
        g.switch_to_block(bb1_id, 0, vec![]);
        g.push_instr(OptOp::Max, &[param, ValueId::C_ONE], false, None, Some(OpEffect::None));
        let val1 = g.push_instr(OptOp::Pop, &[], false, None, None).0;
        g.push_instr(OptOp::Add, &[param, val1], false, None, None);
        
        // bb2: Min (effect-free), Pop (effectful), Mul (may fail)
        g.switch_to_block(bb2_id, 0, vec![]);
        g.push_instr(OptOp::Min, &[param, ValueId::C_ONE], false, None, Some(OpEffect::None));
        let val2 = g.push_instr(OptOp::Pop, &[], false, None, None).0;
        g.push_instr(OptOp::Mul, &[param, val2], false, None, None);
        
        assert_eq!(g.block_(bb1_id).instructions.len(), 3, "{g}");
        assert_eq!(g.block_(bb2_id).instructions.len(), 3, "{g}");
        println!("Before hoisting:\n{}", g);
        
        let hoisted = hoist_up(&mut g, bb0_id);
        println!("After hoisting:\n{}", g);
        
        assert!(hoisted, "Should have hoisted common instructions");
        
        // Pop should be hoisted even though preceded by effect-free instructions
        // After hoisting Pop, bb1 should have Max and Add left, bb2 should have Min and Mul left
        let bb1_len = g.block_(bb1_id).instructions.len();
        let bb2_len = g.block_(bb2_id).instructions.len();
        assert_eq!(bb1_len, 2, "bb1 should have Max and Add left, got {} instructions", bb1_len);
        assert_eq!(bb2_len, 2, "bb2 should have Min and Mul left, got {} instructions", bb2_len);
        
        // bb0 should have Pop hoisted
        let bb0_instrs: Vec<_> = g.block_(bb0_id).instructions.values().collect();
        assert!(bb0_instrs.iter().any(|i| matches!(i.op, OptOp::Pop)), "Should have Pop hoisted");
    }
}

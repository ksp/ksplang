use std::collections::{HashMap};

use smallvec::SmallVec;

use crate::compiler::{
    cfg::{GraphBuilder, StackHistory},
    ops::{BlockId, InstrId, OptInstr, OptOp, ValueId},
    vm_code::Condition,
};
use crate::vm::OperationError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CfgInterpretStats {
    pub executed_ksplang: u64,
    pub executed_cfg_ops: u64,
    pub next_ip: usize,
    pub deoptimized: bool,
}

pub fn interpret_cfg(
    g: &GraphBuilder,
    stack: &mut Vec<i64>,
    error_is_deopt: bool,
) -> Result<CfgInterpretStats, OperationError> {
    let mut values: HashMap<ValueId, i64> = HashMap::new();
    let mut executed_cfg_ops: u64 = 0;
    let mut executed_ksplang: u64 = 0;
    let mut next_ip: usize = usize::MAX;
    let mut deoptimized = None;
    let mut error = None;

    let mut current_block = g.blocks.first().map(|bb| bb.id).unwrap_or(BlockId(0));

    let mut block_iteration_guard = 0usize;

    'block: loop {
        let block = g.block(current_block).expect("Invalid current_block");

        for instr in block.instructions.values() {
            executed_cfg_ops += 1;

            if instr.program_position != usize::MAX {
                next_ip = instr.program_position;
            }

            let op = &instr.op;

            match op {
                OptOp::Nop => continue,
                OptOp::Jump(condition, target) => {
                    if eval_condition(g, &values, condition) {
                        let Some(target_block) = g.block(*target) else {
                            panic!("Target block {target} not found")
                        };

                        assert_eq!(instr.inputs.len(), target_block.parameters.len(), "{target}");

                        for (param, arg) in target_block.parameters.iter().zip(&instr.inputs) {
                            assert!(param.is_constant());
                            let value = resolve_value(g, &values, *arg);
                            values.insert(*param, value);
                        }

                        block_iteration_guard += 1;
                        if block_iteration_guard > 10_000 {
                            deoptimized = Some(instr.id);
                            break;
                        }

                        executed_ksplang += block.ksplang_instr_count as u64;
                        for x in &block.ksplang_instr_count_additional {
                            executed_ksplang += resolve_value(g, &values, *x) as u64;
                        }

                        current_block = *target;
                        continue 'block;
                    }
                    continue;
                }
                OptOp::DeoptAssert(cond) => {
                    if !eval_condition(g, &values, cond) {
                        deoptimized = Some(instr.id);
                        break 'block;
                    }
                    continue;
                }
                OptOp::Push => {
                    for arg in &instr.inputs {
                        let value= resolve_value(g, &values, *arg);
                        stack.push(value);
                    }
                    continue;
                }
                OptOp::Pop => {
                    match stack.pop() {
                        Some(value) => {
                            if instr.out.is_computed() {
                                values.insert(instr.out, value);
                            }
                        }
                        None => {
                            error = Some((OperationError::PopFailed, instr.id));
                            break 'block;
                        }
                    }
                    continue;
                }
                OptOp::StackSwap => {
                    assert_eq!(instr.inputs.len(), 2);

                    let idx = resolve_value(g, &values, instr.inputs[0]);
                    let replacement = resolve_value(g, &values, instr.inputs[1]);
                    if idx < 0 {
                        error = Some((OperationError::IndexOutOfRange {
                            stack_len: stack.len(),
                            index: idx,
                        }, instr.id));
                        break 'block;
                    }

                    if idx as usize >= stack.len() {
                        deoptimized = Some(instr.id); // we don't know what's on top of the stack, that's been elided by optimizations
                        break 'block;
                    }

                    let old_value = stack[idx as usize];
                    stack[idx as usize] = replacement;

                    if instr.out.is_computed() {
                        values.insert(instr.out, old_value);
                    }
                    continue;
                }
                _ => {}
            }

            let arg_values: SmallVec<[i64; 4]> =
                instr.iter_inputs().map(|input| resolve_value(g, &values, input)).collect();

            match op.evaluate(&arg_values) {
                Ok(value) => {
                    if instr.out.is_computed() {
                        values.insert(instr.out, value);
                    }
                }
                Err(Some(err)) => {
                    error = Some((err, instr.id));
                    break 'block;
                }
                Err(None) => continue,
            }
        }

        break;
    }

    if let Some((error, failed_at)) = error {
        if error_is_deopt {
            deoptimized = Some(failed_at);
        } else {
            return Err(error);
        }
    }

    if let Some(deopt_instr) = deoptimized {
        let i = g.get_instruction_(deopt_instr);
        executed_ksplang += i.ksp_instr_count as u64;
        next_ip = restore_deopt_state(g, &values, stack, deopt_instr);
    }

    Ok(CfgInterpretStats {
        executed_ksplang: executed_ksplang,
        executed_cfg_ops,
        next_ip,
        deoptimized: deoptimized.is_some(),
    })
}

fn restore_deopt_state(
    g: &GraphBuilder,
    values: &HashMap<ValueId, i64>,
    stack: &mut Vec<i64>,
    start: InstrId,
) -> usize {
    let block_id = start.block_id();

    let block = g.block(block_id).unwrap();

    if let Some(instr) = block.instructions.get(&start.1) {
        if instr.program_position != usize::MAX && instr.stack_state.is_some() {
            stack.extend(build_stack_from_history(g, values, instr.stack_state.unwrap()));
            return instr.program_position;
        }
    }

    for (_, instr) in block.instructions.range(..start.1).rev() {
        revert_stack_effect(g, values, instr, stack);

        if let Some(stack_state) = instr.stack_state {
            assert_ne!(instr.program_position, usize::MAX, "Invalid CFG: stack_state without program position at instruction {}", instr.id);

            stack.extend(build_stack_from_history(g, values, stack_state));

            return instr.program_position;
        }
    }

    if block_id.is_first_block() {
        return block.ksplang_start_ip;
    }

    assert_eq!(block.incoming_jumps.len(), 1, "Cannot recover deopt state: block {block_id} has multiple incoming edges");

    let prev_instr = block.incoming_jumps[0];
    return restore_deopt_state(g, values, stack, prev_instr);
}

fn revert_stack_effect(
    g: &GraphBuilder,
    values: &HashMap<ValueId, i64>,
    instr: &OptInstr,
    stack: &mut Vec<i64>,
) {
    match instr.op {
        OptOp::Push => {
            for arg in instr.inputs.iter().rev() {
                let expected = resolve_value(g, values, *arg);
                let Some(actual) = stack.pop() else {
                    panic!("Cannot recover deopt state: stack underflow while undoing Push {instr}")
                };
                assert_eq!(actual, expected, "Cannot recover deopt state: mismatched value while undoing Push {instr}");
            }
        }
        OptOp::Pop => {
            assert!(instr.out.is_computed(), "No output value: {instr}");
            let value = values[&instr.out];
            stack.push(value);
        }
        OptOp::StackSwap => {
            assert_eq!(instr.inputs.len(), 2);
            let idx = resolve_value(g, values, instr.inputs[0]);
            assert!(idx >= 0 && idx as usize >= stack.len(), "index {idx} out of range {} ({instr})", stack.len());

            let replacement = resolve_value(g, values, instr.inputs[1]);
            assert_eq!(stack[idx as usize], replacement);

            assert!(instr.out.is_computed());
            stack[idx as usize] = values[&instr.out];
        }
        _ => {}
    }
}

fn build_stack_from_history<'a>(
    g: &'a GraphBuilder,
    values: &'a HashMap<ValueId, i64>,
    stack_state: u32,
) -> impl Iterator<Item = i64> + 'a {
    let value_ids = unfold_stack_history(&g.stack.stack_history, stack_state);
    value_ids
        .into_iter()
        .map(|value_id| resolve_value(g, values, value_id))
}

fn unfold_stack_history(histories: &[StackHistory], state: u32) -> Vec<ValueId> {
    assert_ne!(state, 0);
    let entry = &histories[state as usize - 1];

    if entry.base == 0 {
        entry.push.to_vec()
    } else {
        let mut stack = unfold_stack_history(histories, entry.base);
        let pop = entry.pop as usize;
        assert!(pop <= stack.len(), "stack history pop {pop} larger than stack depth {} for state {state}", stack.len());
        stack.truncate(stack.len() - pop);
        stack.extend_from_slice(&entry.push);
        stack
    }
}

fn resolve_value(g: &GraphBuilder, values: &HashMap<ValueId, i64>, id: ValueId) -> i64 {
    assert!(!id.is_null(), "Invalid CFG: null ValueId encountered during interpretation");
    if let Some(value) = id.to_predefined_const() {
        return value;
    }
    if id.is_constant() {
        return g.get_constant_(id);
    }
    *values.get(&id).unwrap_or_else(|| panic!("Invalid CFG: unresolved ValueId {id:?}"))
}

fn eval_condition(
    g: &GraphBuilder,
    values: &HashMap<ValueId, i64>,
    condition: &Condition<ValueId>,
) -> bool {
    let inputs: SmallVec<[i64; 2]> =
        condition.regs().into_iter().map(|reg| resolve_value(g, values, reg)).collect();
    condition.eval(&inputs)
}

#[cfg(test)]
mod test {
    use crate::compiler::{cfg::GraphBuilder, cfg_interpreter::interpret_cfg, ops::{OptOp, ValueId}};

    #[test]
    fn interpret_cfg_push_pushes_values() {
        let mut g = GraphBuilder::new(0);
        let value = g.store_constant(42);
        g.push_instr(OptOp::Push, &[value], false, None, None);

        let mut stack = Vec::new();
        let stats = interpret_cfg(&g, &mut stack, false).unwrap();

        assert_eq!(stack, vec![42]);
        assert_eq!(stats.executed_cfg_ops, 1);
        assert!(!stats.deoptimized);
    }

    #[test]
    fn interpret_cfg_pop_then_push_roundtrip() {
        let mut g = GraphBuilder::new(0);
        let popped_val = g.push_instr(OptOp::Pop, &[], false, None, None).0;
        g.push_instr(OptOp::Push, &[popped_val], false, None, None);

        let mut stack = vec![10, 20, 30];
        let stats = interpret_cfg(&g, &mut stack, false).unwrap();

        assert_eq!(stack, vec![10, 20, 30]);
        assert_eq!(stats.executed_cfg_ops, 2);
        assert!(!stats.deoptimized);
    }

    #[test]
    fn interpret_cfg_stackswap_swaps_values() {
        let mut g = GraphBuilder::new(0);
        let index = g.store_constant(1);
        let replacement = g.store_constant(40);
        let (v, _) = g.push_instr(OptOp::StackSwap, &[index, replacement], false, None, None);
        g.push_instr(OptOp::Push, &[v], false, None, None);

        let mut stack = vec![10, 20, 30];
        let stats = interpret_cfg(&g, &mut stack, false).unwrap();

        assert_eq!(stats.executed_cfg_ops, 2);
        assert_eq!(stack, vec![10, 40, 30, 20]);
    }

    #[test]
    fn interpret_cfg_stackswap_deopt() {
        let mut g = GraphBuilder::new(0);
        let index = g.store_constant(10);
        let replacement = g.store_constant(3);
        g.push_instr(OptOp::Pop, &[], false, None, None);
        g.push_instr(OptOp::StackSwap, &[index, replacement], false, None, None);

        let mut stack = vec![1, 2, 3, 10, 13];
        let deopt = interpret_cfg(&g, &mut stack, false).unwrap();

        assert!(deopt.deoptimized, "{deopt:?}");
        assert_eq!(0, deopt.next_ip, "{deopt:?}");
        assert_eq!(vec![1, 2, 3, 10, 13], stack);
    }

    #[test]
    fn interpret_cfg_stackswap_deopt_checkpoint() {
        let mut g = GraphBuilder::new(0);
        let index = g.store_constant(10);
        let replacement = g.store_constant(3);
        g.push_instr(OptOp::Pop, &[], false, None, None).1.unwrap().program_position = 10;
        g.push_instr_may_deopt(OptOp::StackSwap, &[ValueId::C_ZERO, ValueId::C_ZERO]).program_position = 20;
        g.push_instr_may_deopt(OptOp::StackSwap, &[index, replacement]).program_position = 30;

        let mut stack = vec![1, 2, 3, 10, 13];
        let deopt = interpret_cfg(&g, &mut stack, false).unwrap();

        assert!(deopt.deoptimized, "{deopt:?}");
        assert_eq!(30, deopt.next_ip, "{deopt:?}");
        assert_eq!(vec![0, 2, 3, 10], stack);
    }
}

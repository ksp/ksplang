use std::{cmp, collections::{BTreeSet, VecDeque}, ops::RangeInclusive, vec};
use rustc_hash::{FxHashMap as HashMap};

use num_integer::Integer;
use smallvec::{SmallVec, smallvec};

use crate::{compiler::{cfg::{GraphBuilder, StackState}, config::{JitConfig, get_config}, ops::{BlockId, InstrId, OpEffect, OptOp, ValueId}, opt_hoisting::hoist_up, osmibytecode::Condition, range_ops::{eval_combi, range_div, range_num_digits}, simplifier::{self, simplify_cond}, utils::{FULL_RANGE, abs_range, add_range, eval_combi_u64, intersect_range, range_2_i64, sort_tuple, sub_range}}, digit_sum::digit_sum, funkcia::funkcia, ops::Op, vm::{self, OperationError, QuadraticEquationResult, solve_quadratic_equation}};

pub trait TraceProvider {
    // type TracePointer
    fn get_results<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = (u32, SmallVec<[i64; 2]>)> + 'a;
    fn get_observed_stack_values<'a>(&'a mut self, ip: usize, depths: &[usize]) -> Vec<Vec<i64>>;
    fn is_lazy(&self) -> bool;

    fn get_branch_targets<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = usize>;
    // fn get_push_pop_count(&mut self, ip: usize) -> impl Iterator<Item = (u32, u32)>;
}

pub struct NoTrace();
impl TraceProvider for NoTrace {
    fn get_results<'a>(&'a mut self, _ip: usize) -> impl Iterator<Item = (u32, SmallVec<[i64; 2]>)> + 'a {
        std::iter::empty()
    }
    fn get_observed_stack_values<'a>(&'a mut self, _ip: usize, _depths: &[usize]) -> Vec<Vec<i64>> {
        vec![]
    }
    fn is_lazy(&self) -> bool { false }

    fn get_branch_targets<'a>(&'a mut self, _ip: usize) -> impl Iterator<Item = usize> {
        std::iter::empty()
    }
}

#[derive(Debug, Clone)]
pub struct PendingBranchInfo {
    pub target: usize,
    pub reversed_direction: bool,
    pub b: Vec<PrecompileStepResultBranch>,
    pub assumes: Vec<Vec<Condition<ValueId>>>,
    pub from: Vec<InstrId>,
    pub to_bb: BlockId,
    pub stack_snapshot: Vec<StackState>,
}

#[derive(Debug, Clone, Default)]
pub struct VisitedIpStats {
    pub visits: usize,
    pub branches: HashMap<usize, usize>, // from IP -> count
}

#[derive(Debug)]
pub struct Precompiler<'a, TP: TraceProvider> {
    pub ops: &'a [crate::ops::Op],
    pub initial_stack_size: usize,
    pub reversed_direction: bool,
    pub initial_position: usize,
    pub g: GraphBuilder,
    // deopt_info: HashMap<u32, DeoptInfo<u32>>,
    pub position: usize,
    pub instr_interpreted_count: usize,
    pub interpretation_limit: usize,
    pub soften_limits: bool,
    pub bb_limit: usize,
    pub instr_limit: usize,
    pub termination_ip: Option<usize>,
    pub visited_ips: HashMap<usize, VisitedIpStats>,
    pub pending_branches: VecDeque<PendingBranchInfo>,
    pub conf: JitConfig,
    pub tracer: TP
}

#[derive(Debug, Clone)]
pub struct PrecompileStepResultBranch {
    pub target: usize,
    pub condition: Condition<ValueId>,
    pub stack: (usize, Vec<ValueId>),
    pub call_ret: Option<ValueId>,
    pub additional_instr: Vec<(OptOp<ValueId>, Vec<ValueId>, ValueId)>,
}

#[derive(Debug, Clone)]
pub enum PrecompileStepResult {
    Continue,
    NevimJak,
    NevimJakChteloByToKonstantu(Vec<ValueId>),
    Branching(Vec<PrecompileStepResultBranch>),
}

impl<'a, TP: TraceProvider> Precompiler<'a, TP> {
    pub fn new(
        ops: &'a [crate::ops::Op],
        initial_stack_size: usize,
        reversed_direction: bool,
        initial_position: usize,
        interpretation_limit: usize,
        soften_limits: bool,
        termination_ip: Option<usize>,
        initial_graph: GraphBuilder,
        tracer: TP
    ) -> Self {
        Self {
            ops,
            initial_stack_size,
            reversed_direction,
            initial_position,
            position: initial_position,
            interpretation_limit,
            soften_limits,
            instr_interpreted_count: 0,
            bb_limit: usize::MAX,
            instr_limit: usize::MAX,
            g: initial_graph,
            termination_ip,
            visited_ips: HashMap::default(),
            pending_branches: VecDeque::new(),
            conf: get_config().clone(),
            tracer
        }
    }

    fn next_position(&self) -> usize {
        if self.reversed_direction {
            self.position.wrapping_sub(1)
        } else {
            self.position + 1
        }
    }

    fn instr_add(&mut self, a: ValueId, b: ValueId) -> ValueId {
        let (a, b) = sort_tuple(a, b);
        self.g.value_numbering(OptOp::Add, &[a, b], None, None)
    }

    fn branching(&mut self, target: ValueId, is_relative: bool, is_call: bool, condition: Condition<ValueId>) -> PrecompileStepResult {
        let at = self.g.next_instr_id();
        let condition = simplifier::simplify_cond(&mut self.g, condition, at);
        if condition == Condition::False {
            return PrecompileStepResult::Continue;
        }
    
        if let Some(target_const) = self.g.get_constant(target) {
            let target_ip: Option<usize> = if is_relative {
                target_const.try_into().ok()
                    .and_then(|x: isize| x.checked_add(1))
                    .and_then(|x|
                        if self.reversed_direction {
                            self.position.checked_sub_signed(x)
                        } else {
                            self.position.checked_add_signed(x)
                        }
                    )
            } else {
                target_const.try_into().ok()
            };
            if self.conf.should_log(5) {
                println!("Branching to constant target {target_const} {}->{target_ip:?} (relative={is_relative}, call={is_call}, condition={condition:?})", self.position);
            }

            if target_ip.is_none_or(|target_ip | target_ip >= self.ops.len()) {
                // branching out of the program
                self.g.push_deopt_assert(condition.neg(), false);
                return PrecompileStepResult::Continue;
            }

            let call_ret = if is_call {
                Some(self.g.store_constant(self.next_position() as i64))
            } else {
                None
            };

            let branch = PrecompileStepResultBranch {
                target: target_ip.unwrap(),
                condition: condition.clone(),
                stack: (0, call_ret.into_iter().collect()),
                call_ret,
                additional_instr: vec![],
            };

            let no_branch = PrecompileStepResultBranch {
                target: self.next_position(),
                condition: Condition::True,
                stack: (0, vec![]),
                call_ret: None,
                additional_instr: vec![],
            };
            if condition == Condition::True {
                return PrecompileStepResult::Branching(vec![branch]);
            } else {
                return PrecompileStepResult::Branching(vec![branch, no_branch]);
            }
        }

        PrecompileStepResult::NevimJakChteloByToKonstantu(vec![target])
    }

    fn resolve_constants(&mut self, needed: &[ValueId]) -> Option<Vec<PrecompileStepResultBranch>> {
        if needed.is_empty() { return None; }

        let Some(depths): Option<Vec<usize>> = needed.iter()
            .map(|&val| self.g.stack.stack.iter().rev().position(|&v| v == val))
            .collect() else {
            if self.g.conf.should_log(2) {
                println!("Warning: resolve_constants called with a non-stack value")
            }
            return None;
        };
        let max_depth = *depths.iter().max()?;

        let observed_combinations: BTreeSet<_> = self.tracer.get_observed_stack_values(self.position, &depths).into_iter().collect();

        if self.conf.should_log(4) {
            println!("Trying to resolve constants from {needed:?} via deopts: {observed_combinations:?}");
        }

        if observed_combinations.is_empty() || observed_combinations.len() > 1 {
            return None;
        }

        let stack_len = self.g.stack.stack.len();
        let pop_count = max_depth + 1;
        let start_index = stack_len - pop_count;
        let original_values_vec = self.g.stack.stack[start_index..].to_vec();

        let mut branches = Vec::new();

        for combination in &observed_combinations {
            let condition_raw = if needed.len() == 1 {
                let c = self.g.store_constant(combination[0]);
                Condition::Eq(needed[0], c)
            } else {
                let mut match_val = ValueId::C_ONE;
                for (j, &val) in needed.iter().enumerate() {
                    let const_val = combination[j];
                    let const_id = self.g.store_constant(const_val);
                    let eq = self.g.value_numbering(OptOp::Select(Condition::Eq(val, const_id)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None);
                    match_val = self.g.value_numbering(OptOp::And, &[match_val, eq], None, None);
                }
                self.g.stack.poped_values.push(match_val);
                Condition::Eq(ValueId::C_ONE, match_val)
            };

            let next_iid = self.g.next_instr_id();
            let condition = simplify_cond(&mut self.g, condition_raw.clone(), next_iid);
            let mut new_values = original_values_vec.clone();
            for (j, _) in needed.iter().enumerate() {
                let index_in_slice = pop_count - 1 - depths[j];
                new_values[index_in_slice] = self.g.store_constant(combination[j]);
            }

            branches.push(PrecompileStepResultBranch {
                target: self.position,
                condition: condition.clone(),
                stack: (new_values.len(), new_values),
                call_ret: None,
                additional_instr: vec![],
            });
            if condition == Condition::True {
                // aha, perfect
                return Some(vec![ branches.pop().unwrap() ])
            }
            if condition == Condition::False {
                // well well
                // panic!("Warning: n-gate, we can't be both right: tracer says {needed:?}={combination:?}, but compiler says no to {}\n\n{}", condition_raw, self.g);//.current_block_ref());
                // actually, it's 100% fine, we might very well be in some branch which prohibits this
                return None
            }

        }
        // self.g.push_checkpoint(); // prob not worth it?
        if branches.len() == 1 {
            self.g.push_deopt_assert(branches[0].condition.clone(), false);
            branches[0].condition = Condition::True;
        } else {
            // TODO: make sure we auto-insert deopt
            branches.push(PrecompileStepResultBranch {
                target: self.position,
                condition: Condition::True,
                stack: (0, vec![]),
                call_ret: None,
                additional_instr: vec![
                    (OptOp::DeoptAssert(Condition::True), vec![], ValueId(0))
                ]
            })
        }

        Some(branches)
    }

    fn can_elide_stack_read(&mut self, instr: InstrId) -> bool {
        // we need to make sure the read does not have the function of deopt
        // i.e., there is already another read of the same variable in the same block
        let i = self.g.get_instruction_(instr);
        assert!(matches!(i.op, OptOp::StackRead | OptOp::StackSwap));
        let addr = i.inputs[0];

        for (_, prev) in self.g.block_(instr.0).instructions.range(0..instr.1).rev() {
            if matches!(prev.op, OptOp::StackRead | OptOp::StackSwap) &&
                prev.inputs[0] == addr
            {
                return true;
            }

            if matches!(prev.op, OptOp::Pop) {
                return false;
            }
        }

        false
    }

    pub fn push_swap(&mut self, ix: ValueId, val: ValueId) -> ValueId {
        assert!(!self.g.current_block_ref().is_terminated);
        let (val, _) = self.g.analyze_val_at(val, self.g.next_instr_id());
        let (ix, _) = self.g.analyze_val_at(ix, self.g.next_instr_id());
        let next_iid = self.g.next_instr_id();
        // try find previous anti-swap
        let mut interfering_swaps = vec![];
        let mut interfering_reads = vec![];
        let mut has_effect = false;
        let mut has_pops = false;
        let mut has_branching = false;
        let mut found_anti_swap = None;
        let mut found_anti_read = None;

        let mut bid = self.g.current_block;

        'main: loop {
            let iids: Vec<u32> = self.g.block_(bid).instructions.keys().rev().copied().collect();
            for &iid in &iids {
                let iid = InstrId(bid, iid);
                let instr = &self.g.get_instruction_(iid);
                let effect = !matches!(instr.effect, OpEffect::None | OpEffect::ControlFlow);
                match instr.op {
                    OptOp::Push | OptOp::Pop => { has_pops = true; },
                    OptOp::StackSwap => {
                        let &[instr_ix, instr_val] = instr.inputs.as_slice() else { panic!() };
                        let is_same_address = simplify_cond(&mut self.g, Condition::Eq(instr_ix, ix), next_iid);
                        if is_same_address == Condition::True {
                            found_anti_swap = Some(iid);
                            break 'main;
                        }
                        if is_same_address != Condition::False {
                            if interfering_swaps.len() > 4 { break; }
                            interfering_swaps.push((iid, instr_ix, instr_val, is_same_address));
                        }
                    }
                    OptOp::StackRead => {
                        let &[instr_ix] = instr.inputs.as_slice() else { panic!() };
                        let out_val = instr.out;
                        let is_same_address = simplify_cond(&mut self.g, Condition::Eq(instr_ix, ix), next_iid);
                        if is_same_address == Condition::True {
                            // don't break, try to find the oldest stack read
                            found_anti_read = Some(iid);
                            // break 'main; // we won't find anything better probably
                        }
                        if is_same_address != Condition::False {
                            interfering_reads.push((iid, instr_ix, out_val, is_same_address));
                        }
                    }
                    _ => {
                    }
                }
                has_effect |= effect;
            }
            let block = self.g.block_(bid);
            if block.is_sealed && block.incoming_jumps.len() == 1 {
                bid = block.incoming_jumps[0].0;
                has_branching = true;
            } else {
                break;
            }
        }

        if let Some(anti_swap) = found_anti_swap {
            if self.conf.should_log(15) {
                println!("We have found anti-swap: {}", self.g.get_instruction_(anti_swap));
            }
            // try to optimize away the StackSwap completely if it just undoes previous one
            {
                if !has_effect && !has_pops && !has_branching && interfering_swaps.is_empty() && interfering_reads.is_empty() {
                    let prev_swap = self.g.instr_mut(anti_swap).unwrap();
                    let &[prev_ix, prev_val] = prev_swap.inputs.as_slice() else { panic!() };
                    // rewrite previous swap to StackRead
                    assert!(matches!(prev_swap.op, OptOp::StackSwap));
                    prev_swap.op = OptOp::StackRead;
                    prev_swap.inputs = smallvec![prev_ix];
                    prev_swap.effect = OpEffect::StackRead;
                    let prev_out_raw = prev_swap.out;
                    let (prev_out, _) = self.g.analyze_val_at(prev_out_raw, self.g.next_instr_id());
                    if prev_val.is_computed() && prev_val != prev_ix {
                        if let Some(info) = self.g.values.get_mut(&prev_val) {
                            info.used_at.remove(&anti_swap);
                            if info.used_at.is_empty() {
                                self.g.stack.poped_values.push(prev_val);
                            }
                        }
                    }
                    if prev_out != prev_out_raw &&
                        self.can_elide_stack_read(anti_swap)
                    {
                        // we don't even need the read, it's just shadowing a previous one
                        if self.conf.should_log(15) {
                            println!("Removing {anti_swap} (replace {prev_out_raw} with {prev_out})");
                        }
                        self.g.replace_values([(prev_out_raw, prev_out)].into_iter().collect());
                        self.g.remove_instruction(anti_swap, false);
                        // remove any checkpoints in between to avoid deopting into the unsafe space
                        let checkpoints: Vec<InstrId> =
                            self.g.block_(anti_swap.0).instructions.range(anti_swap.1..)
                                .filter(|(_, instr)| instr.op == OptOp::Checkpoint)
                                .map(|(_, instr)| instr.id)
                                .collect();
                        for iid in checkpoints {
                            self.g.remove_instruction(iid, false);
                        }
                    }
                    // remove preceeding Checkpoint, it's not needed for anything (does not work)
                    // if let Some(prev_prev) = self.g.block_(anti_swap.0).instructions.range(0..anti_swap.1).last() &&
                    //     prev_prev.1.op == OptOp::Checkpoint &&
                    //     (self.g.block_(anti_swap.0).instructions.range(0..anti_swap.1).filter(|i| i.1.op == OptOp::Checkpoint).count() >= 2)
                    // {
                    //     let iid = prev_prev.1.id;
                    //     self.g.remove_instruction(iid, true);
                    // }
                    if val == prev_out {
                        // we are writing back the original value = no change needed
                        return prev_val;
                    }


                    let (new_val, _) = self.g.push_instr(OptOp::StackSwap, &[ix, val], false, None, None);
                    // this operation return prev_val - what was assigned in the removed StackSwap
                    // however, the actually emitted StackSwap will return the original read value:
                    self.g.add_assumption(new_val, InstrId::BEGIN, Condition::Eq(prev_out, new_val), FULL_RANGE);
                    return prev_val;
                }
            }

            // can't remove writes, but we can at least return original value
            {
                let next_op = self.ops.get(self.next_position());
                if interfering_swaps.len() <= 2 && next_op != Some(&Op::Pop) {
                    self.g.push_checkpoint();
                    for (_instr_id, _instr_ix, _, condition) in &interfering_swaps {
                        // let Some(deopt_id) = self.g.make_instr_id_at(
                        //     BeforeOrAfter::Before(*instr_id),
                        //     |iid| anti_swap == iid || interfering_swaps.iter().any(|(x, _, _, _)| *x == iid)
                        // ) else { break 'attempt_remove };
                        // let mut deopt = OptInstr::deopt(condition.clone());
                        // deopt.id = deopt_id;
                        // self.g.current_block_mut().instructions.insert(deopt_id.1, deopt);

                        self.g.push_deopt_assert(condition.clone().neg(), false);
                        assert!(!self.g.current_block_ref().is_terminated, "What is going on: {condition} (all swaps: {interfering_swaps:?})\n{}", self.g);
                    }
                    let orig_val = self.g.get_instruction_(anti_swap).inputs[1];
                    let (orig_val, _) = self.g.analyze_val_at(orig_val, self.g.next_instr_id());
                    let (new_val, _) = self.g.push_instr(OptOp::StackSwap, &[ix, val], false, None, None);
                    self.g.add_assumption(new_val, InstrId::BEGIN, Condition::Eq(orig_val, new_val), FULL_RANGE);
                    return orig_val;
                }
            }
        }

        if let Some(anti_read) = found_anti_read {
            // we found read of the same location -> return same value as before
            let next_op = self.ops.get(self.next_position());
            if interfering_swaps.len() <= 2 && next_op != Some(&Op::Pop) {
                self.g.push_checkpoint();
                for (_instr_id, _instr_ix, _, condition) in &interfering_swaps {
                    self.g.push_deopt_assert(condition.clone().neg(), false);
                    assert!(!self.g.current_block_ref().is_terminated, "What is going on: {condition} (all swaps: {interfering_swaps:?})\n{}", self.g);
                }
                if self.conf.should_log(15) {
                    println!("Found previous read: {}", self.g.get_instruction_(anti_read));
                }
                let orig_val = self.g.get_instruction_(anti_read).out;
                let (orig_val, _) = self.g.analyze_val_at(orig_val, self.g.next_instr_id());
                let (new_val, _) = self.g.push_instr(OptOp::StackSwap, &[ix, val], false, None, None);
                self.g.add_assumption(new_val, InstrId::BEGIN, Condition::Eq(orig_val, new_val), FULL_RANGE);
                return orig_val;
            }
        }

        // else
        {
            let instr = self.g.push_instr_may_deopt(OptOp::StackSwap, &[ix, val]);
            instr.map(|i| i.out).unwrap_or(ValueId(0))
        }
    }

    pub fn step(&mut self) -> PrecompileStepResult {
        use PrecompileStepResult::*;
        let op = self.ops[self.position as usize];

        match op {
            crate::ops::Op::Nop => Continue,
            crate::ops::Op::Praise => {
                let n = self.g.peek_stack();
                if let Some(constant) = self.g.get_constant(n) {
                    if constant > 100 || constant < 0 {
                        return NevimJak;
                    }

                    self.g.pop_stack();

                    if constant > 0 {
                        let str = "Mám rád KSP";
                        let mut vals = Vec::new();
                        for chr in str.chars() {
                            vals.push(ValueId::from_predefined_const(chr as i64).unwrap());
                        }

                        for _ in 0..constant {
                            for &v in &vals { self.g.stack.push(v); }
                        }
                    }
                    Continue
                } else {
                    NevimJakChteloByToKonstantu(vec![n])
                }
            }
            crate::ops::Op::Pop => {
                self.g.pop_stack();
                Continue
            }
            crate::ops::Op::Pop2 => {
                let orig = self.g.pop_stack();
                self.g.pop_stack();
                self.g.stack.push(orig);
                Continue
            }
            crate::ops::Op::Max => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();

                let out = self.g.value_numbering(OptOp::Max, &[a, b], None, None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::LSwap => {
                let x = self.g.peek_stack();
                let out = self.push_swap(ValueId::C_ZERO, x);
                if self.g.current_block_ref().is_terminated { return Continue }
                self.g.pop_stack();
                self.g.stack.push(out);

                let next_pos = self.next_position();
                if let Some(d) = self.g.push_checkpoint() {
                    d.program_position = next_pos;
                    d.ksp_instr_count += 1;
                }
                Continue
            }
            crate::ops::Op::Swap => {
                let (i, x) = self.g.peek_stack_2();
                let out = self.push_swap(i, x);
                if self.g.current_block_ref().is_terminated { return Continue }
                self.g.pop_stack();
                self.g.pop_stack();
                self.g.stack.push(out);

                let next_pos = self.next_position();
                if let Some(d) = self.g.push_checkpoint() {
                    d.program_position = next_pos;
                    d.ksp_instr_count += 1;
                }
                Continue
            }
            crate::ops::Op::Roll => {
                let (n, x) = self.g.peek_stack_2();

                let Some(n) = self.g.get_constant(n) else {
                    return NevimJakChteloByToKonstantu(vec![n]);
                };

                if n > 128 { return NevimJak; }

                if n == 0 {
                    self.g.pop_stack_n(2);
                    return Continue
                }

                if n < 0 {
                    self.g.push_assert(Condition::False, OperationError::NegativeLength { value: n }, None);
                    return Continue
                }

                if let Some(x) = self.g.get_constant(x) {
                    self.g.pop_stack_n(2);
                    let rotate_by = x.rem_euclid(n);
                    let mut vals = self.g.pop_stack_n(n as usize);
                    if self.conf.should_log(20) {
                        println!("Roll({n}, {rotate_by}) {vals:?}");
                    }
                    vals[..].rotate_left(rotate_by as usize);
                    if self.conf.should_log(20) {
                        println!("        -> {vals:?}");
                    }
                    for v in vals.iter().rev() {
                        self.g.stack.push(*v)
                    }
                    return Continue
                }

                return NevimJak // TODO:
            }
            crate::ops::Op::FF => NevimJak,
            crate::ops::Op::KPi => NevimJak,
            crate::ops::Op::Increment => {
                let a = self.g.pop_stack();
                let out = if let Some(c) = self.g.get_constant(a) {
                    if c == i64::MAX {
                        self.g.push_assert(Condition::False, OperationError::IntegerOverflow, None);
                        return Continue;
                    }
                    self.g.store_constant(c + 1)
                } else {
                    self.instr_add(a, ValueId::C_ONE)
                };
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Universal => {
                let control = self.g.peek_stack();
                let mut control_range = self.g.val_range_at(control, self.g.next_instr_id());
                if *control_range.end() != *control_range.start() {
                    // TODO: fucking hack
                    let info = self.g.val_info(control);
                    if let Some(instr) = info.and_then(|i| i.assigned_at).and_then(|i| self.g.get_instruction(i)) {
                        if instr.op == OptOp::Funkcia {
                            // this will be 0 for sure, nobody uses funkcia for anything else
                            self.g.push_deopt_assert(Condition::EqConst(control, 0), false);
                            control_range = 0..=0;
                        }
                    }
                }
                let out = match control_range.into_inner() {
                    (0, 0) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        self.instr_add(a, b)
                    }
                    (1, 1) => {
                        // abs(a - b)
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();

                        if a == b {
                            ValueId::C_ZERO
                        } else {
                            let (a, b) = sort_tuple(a, b);
                            self.g.value_numbering(OptOp::AbsSub, &[a, b], None, None)
                        }
                    }
                    (2, 2) => {
                        // a * b
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        let (a, b) = sort_tuple(a, b);
                        self.g.value_numbering(OptOp::Mul, &[a, b], None, None)
                    }
                    (3, 3) => {
                        self.g.pop_stack();
                        //  a % b if non-zero, otherwise a / b
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        self.g.value_numbering(OptOp::CursedDiv, &[a, b], None, None)
                    }
                    (4, 4) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        self.g.value_numbering(OptOp::AbsFactorial, &[a], None, None)
                    }
                    (5, 5) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        self.g.value_numbering(OptOp::Sgn, &[a], None, None)
                    },
                    (a, a2) if a == a2 => {
                        self.g.push_assert(Condition::False, OperationError::InvalidArgumentForUniversal { argument: a }, None);
                        return Continue
                    }

                    _ => return NevimJakChteloByToKonstantu(vec![control]),
                };
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Remainder | crate::ops::Op::Modulo => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let euclidean = matches!(op, crate::ops::Op::Modulo);

                let op = if euclidean { OptOp::ModEuclid } else { OptOp::Mod };
                let out = self.g.value_numbering(op, &[a, b], None, None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::TetrationNumIters | crate::ops::Op::TetrationItersNum => {
                let val1 = self.g.pop_stack();
                let val2 = self.g.pop_stack();
                let (num, iters) = if matches!(op, crate::ops::Op::TetrationNumIters) {
                    (val1, val2)
                } else {
                    (val2, val1)
                };

                let num_range = self.g.val_range(num);
                let iters_range = self.g.val_range(iters);

                let range = eval_combi(num_range, iters_range, 16, |num, iters| {
                        vm::tetration(num, iters).ok()
                    });

                let out = self.g.value_numbering(OptOp::Tetration, &[num, iters], range, None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Median => {
                let n = self.g.peek_stack();
                let n_range = self.g.val_range_at(n, self.g.next_instr_id());

                if *n_range.end() <= 0 {
                    self.g.push_assert(Condition::False, OperationError::NonpositiveLength { value: 0 }, Some(n));
                    return Continue
                }

                if *n_range.end() > 25 {
                    return if *n_range.start() <= 3 {
                        NevimJakChteloByToKonstantu(vec![n])
                    } else {
                        NevimJak
                    }
                }

                let vals = self.g.peek_stack_n(0..*n_range.end() as usize);
                assert_eq!(n, vals[0]);

                if n_range.start() == n_range.end() {
                    let out = self.g.value_numbering(OptOp::Median, &vals, None, None);
                    self.g.stack.push(out);
                } else {
                    let out = self.g.value_numbering(OptOp::MedianCursed, &vals, None, None);
                    self.g.stack.push(out);
                }
                Continue
            }
            crate::ops::Op::DigitSum => {
                let x = self.g.peek_stack();
                let range = self.g.val_range(x);

                if *range.start() >= 0 && *range.end() < 10 {
                    self.g.stack.push(x);
                    return Continue;
                }

                if *range.start() == *range.end() {
                    let c = self.g.store_constant(digit_sum(*range.start()));
                    self.g.stack.push(c);
                    return Continue;
                }

                let out = self.g.value_numbering(OptOp::DigitSum, &[x], None, None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::LenSum => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);

                let range_a = range_num_digits(&a_range);
                let range_b = range_num_digits(&b_range);

                // TODO: fucking hack which will add unnecessary deopts
                let out =
                    if *a_range.start() >= 1 && *a_range.start() < 10 && *a_range.end() <= 11 && *b_range.start() >= 1 && *b_range.start() < 10 && *b_range.end() <= 11 {
                        // this is likely creating a constnant which we could not infer, so let's add a deopt and call it a day
                        if *a_range.end() >= 10 {
                            if self.g.conf.should_log(2) {
                                println!("DEBUG LenSumDeoptHack {a_range:?} {b_range:?} {a}* {b}");
                            }
                            self.g.push_deopt_assert(Condition::LtConst(a, 10), false);
                        }
                        if *b_range.end() >= 10 {
                            if self.g.conf.should_log(2){
                                println!("DEBUG LenSumDeoptHack {a_range:?} {b_range:?} {a} {b}*");
                            }
                            self.g.push_deopt_assert(Condition::LtConst(b, 10), false);
                        }
                        ValueId::C_TWO
                    } else {
                        self.g.value_numbering(OptOp::LenSum, &[a, b], Some(add_range(&range_a, &range_b)), None)
                    };

                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Bitshift => {
                let bits = self.g.peek_stack();
                let bits_range = self.g.val_range(bits);
                // let num_range = self.g.val_range(num);

                if *bits_range.end() < 0 {
                    self.g.push_instr_may_deopt(OptOp::deopt_always(), &[]);
                    return Continue;
                }

                let bits = self.g.pop_stack();
                let num = self.g.pop_stack();

                // let range = eval_combi(num_range, bits_range, 1024, |num, bits| Some(num.checked_shl(rhs) << bits));

                let out = self.g.value_numbering(OptOp::ShiftL, &[num, bits], None, None);
                    // let (num_start, num_end) = num_range.into_inner(); // TODO: migrate to simplifier
                    // let (bits_start, bits_end) = bits_range.into_inner();

                    // let max_shift = 1u64 << bits_end.clamp(0, 63);
                    // let min_shift = 1u64 << bits_start.clamp(0, 63);

                    // let candidates = [
                    //     (num_start as u64).saturating_mul(min_shift) as i64,
                    //     (num_start as u64).saturating_mul(max_shift) as i64,
                    //     (num_end as u64).saturating_mul(min_shift) as i64,
                    //     (num_end as u64).saturating_mul(max_shift) as i64,
                    // ];

                    // let min_result = *candidates.iter().min().unwrap();
                    // let max_result = *candidates.iter().max().unwrap();
                    // info.range = min_result..=max_result;
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::And => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);
                let range = eval_combi(a_range, b_range, 1024, |a, b| Some(a & b));

                let out = self.g.value_numbering(OptOp::And, &[a, b], range, None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Funkcia => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                if a == b {
                    self.g.stack.push(ValueId::C_ZERO);
                    return Continue;
                }

                if a.is_constant() && b.is_constant() {
                    let result = funkcia(self.g.get_constant_(a), self.g.get_constant_(b)) as i64;
                    let c = self.g.store_constant(result);
                    self.g.stack.push(c);
                    return Continue;
                }

                let (a_start, a_end) = self.g.val_range(a).into_inner();
                let (b_start, b_end) = self.g.val_range(b).into_inner();

                if a_end <= 1 && b_end <= 1 {
                    self.g.stack.push(ValueId::C_ZERO);
                    return Continue;
                }

                if a == ValueId::C_ONE || a == ValueId::C_ZERO {
                    let mod_out = if b_end < 1_000_000_007 {
                        b
                    } else {
                        let mod_c = self.g.store_constant(1_000_000_007);
                        self.g.value_numbering(OptOp::Mod, &[b, mod_c], None, None)
                    };
                    let out = self.g.push_instr(OptOp::Select(Condition::LeqConst(b, 1)), &[ValueId::C_ZERO, mod_out], true, None, None).0;
                    self.g.stack.push(out);
                    return Continue;
                }

                let range = eval_combi(
                    cmp::min(cmp::max(1, a_start), a_end)..=a_end,
                    cmp::min(cmp::max(1, b_start), b_end)..=b_end,
                    256,
                    |a, b: i64| Some(funkcia(a, b) as i64),
                );

                let out = self.g.value_numbering(OptOp::Funkcia, &[a, b], range, None);

                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::Gcd2 => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = abs_range(self.g.val_range(a));
                let b_range = abs_range(self.g.val_range(b));
                let range = eval_combi_u64(a_range.clone(), b_range.clone(), 256, |a, b| {
                        Some(a.gcd(&b))
                    });

                let out = self.g.value_numbering(OptOp::Gcd, &[a, b], range.map(range_2_i64), None);
                self.g.stack.push(out);
                Continue
            }
            crate::ops::Op::GcdN => {
                let n = self.g.peek_stack();
                let Some(n_const) = self.g.get_constant(n) else {
                    return NevimJakChteloByToKonstantu(vec![n])
                };

                if n_const > 128 || n_const <= 0 {
                    return NevimJakChteloByToKonstantu(vec![n])
                }

                self.g.pop_stack();
                let vals = self.g.pop_stack_n(n_const as usize);
                // TODO: migrate to simplifier
                // let (constants, vals): (BTreeSet<ValueId>, BTreeSet<ValueId>) = vals.iter().partition(|x| x.is_constant());
                // let constants: Vec<i64> = constants.into_iter().map(|c| self.g.get_constant_(c)).collect();
                // let const_gcd = constants.into_iter().map(|v| v.abs_diff(0)).reduce(|a, b| a.gcd(&b));

                // if const_gcd == Some(1) || vals.len() == 0 {
                //     if const_gcd.unwrap() > i64::MAX as u64 {
                //         self.g.push_instr_internal(OptOp::Assert(Condition::False, OperationError::IntegerOverflow), &[], ValueId(0));
                //         return Continue;
                //     }
                //     let result = self.g.store_constant(const_gcd.unwrap() as i64);
                //     self.g.stack.push(result);
                //     return Continue;
                // }

                // let ranges: Vec<RangeInclusive<u64>> = vals.iter().map(|v| abs_range(self.g.val_range(*v))).collect();

                // if const_gcd == None && vals.len() == 1 {
                //     let val = *vals.first().unwrap();
                //     if *ranges[0].end() > i64::MAX as u64 {
                //         self.g.push_assert(Condition::Neq(val, ValueId::C_IMIN), OperationError::IntegerOverflow, None);
                //     }
                //     self.g.stack.push(val);
                //     return Continue;
                // }

                // let min_end = ranges.iter().map(|r| *r.end())
                //     .chain(const_gcd).max().unwrap();

                // let all_zero: bool = matches!(const_gcd, Some(0) | None) && ranges.iter().all(|r| *r.start() == 0);
                // let out_range = if all_zero { 0 } else { 1 }..=min_end;

                // // `as i64` will correctly convert to i64::MIN
                // let args: Vec<ValueId> = vals.iter().copied()
                //                                     .chain(const_gcd.map(|c| self.g.store_constant(c as i64)))
                //                                     .collect();

                let result = self.g.value_numbering(OptOp::Gcd, &vals, None, None);

                self.g.stack.push(result);

                Continue
            },
            crate::ops::Op::Qeq => {
                let (a, b, c) = self.g.peek_stack_3();
                let (a_start, a_end) = self.g.val_range(a).into_inner();
                let (b_start, b_end) = self.g.val_range(b).into_inner();
                let (c_start, c_end) = self.g.val_range(c).into_inner();

                if self.g.get_constant(a) == Some(0) {

                    if self.g.get_constant(b) == Some(0) {
                        self.g.pop_stack_n(3);
                        // equation is `c == 0`
                        if c_start <= 0 && c_end >= 0 {
                            let cond = if (c_start, c_end) == (0, 0) {
                                Condition::False
                            } else {
                                Condition::Neq(ValueId::C_ZERO, c)
                            };
                            self.g.push_assert(cond, OperationError::QeqZeroEqualsZero, None);
                        }

                        // zero solutions:
                        return Continue
                    }

                    if b_start == 1 && b_end == 1 {
                        self.g.pop_stack_n(3);
                        // -c
                        let r = self.g.value_numbering(OptOp::Sub, &[ValueId::C_ZERO, c], None, None);
                        self.g.stack.push(r);
                        return Continue
                    }

                    if b_start <= 0 && b_end >= 0 {
                        self.g.push_deopt_assert(Condition::Neq(ValueId::C_ZERO, b), false);
                    }

                    if b_start <= -1 && b_end >= -1 && c_start == i64::MIN {
                        // it's not clear what happens when we do -(i64::MIN / -1), the result is in range but intermediate isn't
                        self.g.push_deopt_assert(Condition::Neq(ValueId::C_IMIN, c), false);
                    }

                    // result = -(c / b) assuming b divides c
                    let can_overflow = c_start == i64::MIN && b_start <= 1 && b_end >= 1;
                    let mut must_assert_divisibility = false;
                    let bruteforced_div_range = eval_combi(c_start..=c_end, b_start..=b_end, 256, |c, b| {
                            if c.checked_rem(b) == Some(0) { Some(c / b) }
                            else { must_assert_divisibility = true; None }
                    });

                    if bruteforced_div_range.as_ref().is_some_and(|r| r.is_empty()) {
                        self.g.pop_stack_n(3);
                        // just a pop-3, the division will never yield a resul
                        return Continue
                    }
                    let div_range = bruteforced_div_range.clone().unwrap_or_else(|| {
                        range_div(&(c_start..=c_end), &(b_start..=b_end))
                    });
                    let negated_range = sub_range(&(0..=0), &div_range);
                    let mut alt_branch = vec![];
                    if (must_assert_divisibility || bruteforced_div_range.is_none()) &&
                        !matches!((b_start, b_end), (1, 1) | (-1, -1) | (-1, 1)) {

                        // if B does not divide C, there is no solution
                        // usually, we can assume this won't happen because the KSPlang programmer did not want to handle Qeq
                        // retuning variable number of results
                        // However, if we can prove that the states are distinguishable (result range and stack.peek() range do not overlap),
                        // let's make a branch for this, since it can be legitimately useful in some cases (for duplication 😭)

                        let are_states_distinguishable =
                            self.g.stack.peek().is_some_and(|v| intersect_range(&self.g.val_range(v), &negated_range).is_empty());

                        let at = self.g.next_instr_id();
                        let divisibility = simplifier::simplify_cond(&mut self.g, Condition::Divides(c, b), at);

                        if divisibility == Condition::False {
                            // no solutions
                            self.g.pop_stack_n(3);
                            return Continue
                        }

                        if !are_states_distinguishable || divisibility == Condition::True {
                            self.g.push_deopt_assert(divisibility, true);
                        } else {
                            // ok branching...
                            // we put the branch after all instruction, as that's easier to implement
                            alt_branch.push(PrecompileStepResultBranch {
                                target: self.next_position(),
                                condition: divisibility.neg(),
                                stack: (3, vec![]),
                                call_ret: None,
                                additional_instr: vec![],
                            });
                        }
                    }

                    let (elide_neg, dividend, divisor) = if b_start == b_end && b_start != i64::MIN {
                        (true, c, self.g.store_constant(-b_start))
                    } else if c_start == c_end && c_start != i64::MIN {
                        (true, self.g.store_constant(-c_end), b)
                    } else {
                        (false, c, b)
                    };

                    // overflow will happen even when it shouldn't for
                    // c == i64::MIN, b==-1 (but neither is recognized as constant)
                    if !elide_neg && c_start == i64::MIN && b_start <= -1 && b_end >= -1 {
                        // TODO: test this shit
                        self.g.push_deopt_assert(Condition::Neq(c, ValueId::C_IMIN), false);
                    }

                    // TODO: move these instructions to additional_instr and remove the alt_branch.is_empty() hack
                    let div = self.g.value_numbering(OptOp::Div, &[dividend, divisor], if !alt_branch.is_empty() { None } else if elide_neg { Some(negated_range.clone()) } else { Some(div_range.clone()) }, Some(OpEffect::None)); // all failures must be handled specially here

                    let result = if !elide_neg {
                        let neg = self.g.value_numbering(OptOp::Sub, &[ValueId::C_ZERO, div],
                            alt_branch.is_empty().then_some(negated_range),
                            Some(if can_overflow { OpEffect::MayFail } else { OpEffect::None })
                        );
                        neg
                    } else {
                        div
                    };

                    if alt_branch.len() == 0 {
                        self.g.pop_stack_n(3);
                        self.g.stack.push(result);
                        return Continue
                    } else {
                        alt_branch.push(PrecompileStepResultBranch {
                            target: self.next_position(),
                            condition: Condition::True,
                            stack: (3, vec![result]),
                            call_ret: None,
                            additional_instr: vec![],
                        });
                        return Branching(alt_branch)
                    }
                }

                if a_start == a_end && b_start == b_end && c_start == c_end {
                    // all constants
                    self.g.pop_stack_n(3);
                    match solve_quadratic_equation(a_start, b_start, c_start) {
                        Ok(QuadraticEquationResult::None) => {},
                        Ok(QuadraticEquationResult::One(sol1)) => {
                            let sol1 = self.g.store_constant(sol1);
                            self.g.stack.push(sol1);
                        },
                        Ok(QuadraticEquationResult::Two(sol1, sol2)) => {
                            let sol1 = self.g.store_constant(sol1);
                            let sol2 = self.g.store_constant(sol2);
                            self.g.stack.push(sol1);
                            self.g.stack.push(sol2);
                        },
                        Err(error) => {
                            self.g.push_assert(Condition::False, error, None);
                        }
                    }
                    return Continue
                }

                NevimJak
            },
            crate::ops::Op::BulkXor => {
                let n = self.g.peek_stack();
                let Some(n) = self.g.get_constant(n) else {
                    return NevimJakChteloByToKonstantu(vec![n])
                };
                if n < 0 || n > 2 * self.g.stack.stack.len() as i64 + 64 {
                    return NevimJak
                }

                let vals = self.g.peek_stack_n(1..n as usize * 2 + 1);
                let mut xors = vec![];
                for i in 0..(n as usize) {
                    let (a, b) = (vals[i * 2], vals[i * 2 + 1]);
                    let ar = self.g.val_range(a);
                    let br = self.g.val_range(b);
                    if *ar.start() > 0 && *br.start() > 0 {
                        xors.push(Ok(ValueId::C_ZERO))
                    } else if *ar.start() > 0 && *br.end() <= 0 {
                        xors.push(Ok(ValueId::C_ONE))
                    } else if *ar.end() <= 0 && *br.start() > 0 {
                        xors.push(Ok(ValueId::C_ONE))
                    } else if *ar.end() <= 0 && *br.end() <= 0 {
                        xors.push(Ok(ValueId::C_ZERO))
                    } else {
                        xors.push(Err((a, ar, b, br)))
                    }
                }

                if xors.iter().filter(|x| x.is_err()).count() > 8 {
                    return NevimJak
                }

                self.g.pop_stack_n(n as usize * 2 + 1);

                for x in xors.into_iter().rev() {
                    match x {
                        Ok(c) => self.g.stack.push(c),
                        Err((a, ar, b, br)) => {
                            let mut try_opt = |ar: RangeInclusive<i64>, b: ValueId, br: RangeInclusive<i64>| {
                                if *ar.end() <= 0 { // 0 ^ b
                                    if br == (0..=1) {
                                        Some(b)
                                    } else {
                                        Some(self.g.value_numbering(OptOp::Select(Condition::GtConst(b, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None))
                                    }
                                } else if *ar.start() > 0 { // 1 ^ b
                                    Some(self.g.value_numbering(OptOp::Select(Condition::LeqConst(b, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None))
                                } else {
                                    None
                                }
                            };

                            let r = try_opt(ar.clone(), b, br.clone())
                                .or_else(|| try_opt(br, a, ar))
                                .unwrap_or_else(|| {
                                    let a_cond = self.g.value_numbering(OptOp::Select(Condition::GtConst(a, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None);
                                    let b_cond = self.g.value_numbering(OptOp::Select(Condition::GtConst(b, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None);
                                    self.g.value_numbering(OptOp::Select(Condition::Neq(a_cond, b_cond)), &[ValueId::C_ONE, ValueId::C_ZERO], None, None)
                                });
                            self.g.stack.push(r);
                        }
                    }
                }

                Continue
            },
            crate::ops::Op::BranchIfZero => {
                let (val, target) = self.g.peek_stack_2();
                return self.branching(target, false, false, Condition::Eq(ValueId::C_ZERO, val));
            }
            crate::ops::Op::Call => {
                let t = self.g.peek_stack();
                return self.branching(t, false, true, Condition::True);
            }
            crate::ops::Op::Goto => {
                let t = self.g.peek_stack();
                return self.branching(t, false, false, Condition::True);
            }
            crate::ops::Op::Jump => {
                let t = self.g.peek_stack();

                let t_range = self.g.val_range_at(t, self.g.next_instr_id());
                if t_range.start() != t_range.end() && *t_range.start() >= 0 {
                    let n_increments = if self.reversed_direction {
                        self.ops[..self.position].iter().rev().take_while(|&&x| x == Op::Increment).count()
                    } else {
                        self.ops[self.position+1..].iter().take_while(|&&x| x == Op::Increment).count()
                    };

                    if n_increments > 0 && *t_range.end() <= n_increments as i64 {
                        // TODO: more lenient heuristic + deopts?
                        // self.g.push_deopt_assert(Condition::GeqConst(t, 0), false);
                        // self.g.push_deopt_assert(Condition::LeqConst(t, n_increments as i16), false);

                        let n_id = self.g.store_constant(n_increments as i64);
                        let diff = self.g.value_numbering(OptOp::Sub, &[n_id, t], None, None);

                        self.g.push_instr(OptOp::KsplangOpsIncrement(Condition::True), &[diff], false, None, None);

                        return PrecompileStepResult::Branching(vec![PrecompileStepResultBranch {
                            target: self.position + 1 + n_increments,
                            condition: Condition::True,
                            // result of this is the number of increments
                            stack: (1, vec![n_id]),
                            call_ret: None,
                            additional_instr: vec![],
                        }]);
                    }
                }

                return self.branching(t, true, false, Condition::True);
            }
            // BS instrukce
            crate::ops::Op::Rev | crate::ops::Op::Sleep | crate::ops::Op::Deez | crate::ops::Op::Sum => NevimJak,
        }
    }

    fn interpretation_soft_limit(&self) -> usize { self.interpretation_limit }
    fn interpretation_hard_limit(&self) -> usize {
        if self.soften_limits { 2 * self.interpretation_limit } else { self.interpretation_limit } }

    fn branching_limit_exhausted(&self) -> bool {
        let instr_count = self.g.reachable_blocks().map(|b| b.instructions.len()).sum::<usize>();
        self.g.reachable_blocks().count() >= self.bb_limit ||
        instr_count >= self.instr_limit ||
        // self.instr_interpreted_count * 2 > self.interpretation_soft_limit && !self.pending_branches.is_empty() ||
        self.instr_interpreted_count > self.interpretation_soft_limit()
    }

    // fn condition_cnf(&mut self, cnf: &[Vec<Condition<ValueId>>]) -> Condition<ValueId> { if cnf.len() == 0 { return Condition::True; }
    //     if cnf.len() == 1 && cnf[0].len() == 0 { return Condition::False; }
    //     if cnf.len() == 1 && cnf[0].len() == 1 { return cnf[0][0].clone(); }

    //     let mut acc = vec![];
    //     for and in cnf {
    //         let mut acc_and = None;
    //         for cond in and {
    //             let val = self.g.
    //         }
    // }

    fn interpret_block(&mut self) -> () {
        let baseline_instr_count: usize = self.g.reachable_blocks().filter(|b| b.id != self.g.current_block).map(|b| b.instructions.len()).sum();

        loop {
            self.g.stack.check_invariants();
            self.g.set_program_position(Some(self.position));
            if self.g.current_block_ref().is_terminated {
                if self.conf.should_log(2) {
                    println!("end interpret_block: BB is terminated");
                }
                break;
            }
            if self.termination_ip == Some(self.position) || self.position >= self.ops.len() {
                if self.conf.should_log(2) {
                    println!("end interpret_block: termination_ip={} reached", self.position);
                }
                break;
            }
            if self.g.stack.stack_depth as usize + 1 >= self.initial_stack_size {
                if self.conf.should_log(2) {
                    println!("end interpret_block: Stack depth dangerously close");
                }
                break;
            }
            if self.instr_interpreted_count >= self.interpretation_hard_limit() || self.g.stack.stack.len() > 250 {
                if self.conf.should_log(2) {
                    println!("end interpret_block: Interpretation hard limit reached");
                }
                break;
            }
            if self.instr_interpreted_count >= self.interpretation_soft_limit() || self.g.stack.stack.len() > 200 {
                let top = self.g.val_range_at(self.g.stack.peek().unwrap_or(ValueId(0)), self.g.next_instr_id());
                let op = &self.ops[self.position];
                // terminate if we don't seem to be building a constants
                // ...and the instruction doesn't seem to be free stack size reduction
                if top.start().abs_diff(*top.end()) > 1_000 &&
                    !matches!(op, Op::And | Op::Funkcia | Op::LSwap | Op::Swap | Op::TetrationItersNum | Op::TetrationNumIters | Op::Remainder | Op::Modulo | Op::Max | Op::Pop | Op::Pop2 | Op::Increment | Op::Bitshift) {
                    if self.conf.should_log(2) {
                        println!("end interpret_block: Interpretation soft limit reached, terminating due to top stack value range {top:?} at {} {op:?}", self.position);
                    }
                    break;
                }
            }
            self.instr_interpreted_count += 1;

            if self.conf.should_log(20) {
                let trace_results_fmt: String =
                    self.tracer.get_results(self.position)
                        .map(|r| format!("{}:{:?}; ", r.0, r.1))
                        .collect();
                print!("  Current Block: ");
                // TODO: wtf
                struct DisplayBlockWithRanges<'a>(&'a crate::compiler::cfg::BasicBlock, &'a GraphBuilder);
                impl<'a> std::fmt::Display for DisplayBlockWithRanges<'a> {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        self.0.richer_fmt(f, |v| self.1.val_range(v))
                    }
                }
                println!("{}", DisplayBlockWithRanges(self.g.current_block_ref(), &self.g));
                println!("  Stack: {}", self.g.fmt_stack());
                println!("Interpreting op {}: {:?}", self.position, self.ops[self.position]);
                if trace_results_fmt.len() > 0 {
                    println!("Trace results: {}", trace_results_fmt);
                }

            }

            let stack_counts = (self.g.stack.push_count, self.g.stack.pop_count);
            self.visited_ips.entry(self.position).or_default().visits += 1;
            let mut result = self.step();


            if let PrecompileStepResult::NevimJakChteloByToKonstantu(ref needed) = result {
                if let Some(branches) = self.resolve_constants(needed) {
                    self.instr_interpreted_count -= 1;
                    self.g.current_block_mut().ksplang_instr_count -= 1;
                    result = PrecompileStepResult::Branching(branches);
                }
            }

            self.g.current_block_mut().ksplang_instr_count += 1;

            match result {
                PrecompileStepResult::Continue => {}
                PrecompileStepResult::NevimJak | PrecompileStepResult::NevimJakChteloByToKonstantu(_) => {
                    self.g.current_block_mut().ksplang_instr_count -= 1;
                    if self.conf.should_log(2) {
                        println!("  Deoptimizing at IP {} {:?}: {:?}", self.position, self.ops[self.position], result);
                    }
                    if stack_counts != (self.g.stack.push_count, self.g.stack.pop_count) {
                        panic!("Error when interpreting OP {} {:?}: modifed stack, but then returned {result:?}. Stack: {}", self.position, self.ops[self.position], self.g.fmt_stack())
                    }
                    break;
                },
                PrecompileStepResult::Branching(branches) if branches.len() == 1 => {
                    let b = &branches[0];
                    assert_eq!(b.condition, Condition::True);
                    if b.additional_instr.len() > 0 { todo!("{:?}", b) }
                    self.g.pop_stack_n(b.stack.0 as usize);
                    for v in &b.stack.1 { self.g.stack.push(*v); }
                    self.position = b.target;
                    continue;
                },
                PrecompileStepResult::Branching(branches) => {
                    let should_deopt = self.branching_limit_exhausted();
                    if self.g.conf.should_log(3) {
                        println!("  Branching: {:?}", branches);
                        println!("  Finalizing block at {} {}", self.g.fmt_stack(), self.g.current_block_ref());
                        if should_deopt {
                            println!("    (but will deopt due to limits [bbs {} <= {}, instr {} <= {}, interpreted {} <= {}])",
                                self.g.reachable_blocks().count(), self.bb_limit,
                                baseline_instr_count + self.g.current_block_ref().incoming_jumps.len(), self.instr_limit,
                                self.instr_interpreted_count, self.interpretation_soft_limit(),
                            );
                        }
                    }
                    if should_deopt {
                        self.g.current_block_mut().ksplang_instr_count -= 1;
                        break;
                    }
                    let mut prev_assumptions = vec![];
                    for branch in branches {
                        *self.visited_ips.entry(branch.target).or_default().branches.entry(self.position).or_default() += 1;

                        let mut stack_snapshot = self.g.stack.save();
                        stack_snapshot.stack.truncate(stack_snapshot.stack.len() - branch.stack.0 as usize);
                        stack_snapshot.stack.extend(&branch.stack.1);

                        let existing_idx = self.pending_branches.iter().position(|pb|
                            pb.target == branch.target &&
                            pb.reversed_direction == self.reversed_direction &&
                            pb.stack_snapshot[0].depth == stack_snapshot.depth &&
                            pb.stack_snapshot[0].stack.len() == stack_snapshot.stack.len()
                        );

                        let target_block_id = if let Some(idx) = existing_idx {
                            BlockId(self.pending_branches[idx].to_bb.0)
                        } else {
                            let new_block = self.g.new_block(branch.target, false, vec![]);
                            new_block.id
                        };

                        // TODO: merging, ordering heuristics

                        let Some(branch_id) = self.g.push_instr(OptOp::Jump(branch.condition.clone(), target_block_id), &stack_snapshot.stack, false, None, None).1.map(|i| i.id) else {
                            // branch was optimized out right away
                            continue
                        };

                        if self.conf.should_log(2) {
                            if existing_idx.is_some() {
                                println!(
                                    "    Merged branch to IP={} {} with condition {:?}, stack: {} {:?}",
                                    branch.target, target_block_id, branch.condition, stack_snapshot.depth, stack_snapshot.stack
                                );
                            } else {
                                println!(
                                    "    Created branch to IP={} {} with condition {:?}, stack: {} {:?}",
                                    branch.target, target_block_id, branch.condition, stack_snapshot.depth, stack_snapshot.stack
                                );
                            }
                        }

                        let mut assumes = prev_assumptions.clone();
                        assumes.push(branch.condition.clone());
                        prev_assumptions.push(branch.condition.clone().neg());

                        if let Some(idx) = existing_idx {
                            if let Some(pb) = self.pending_branches.get_mut(idx) {
                                pb.from.push(branch_id);
                                pb.b.push(branch.clone());
                                pb.stack_snapshot.push(stack_snapshot);
                                // TODO: proper intersection of assumptions (i.e. a > 2 | a > 5  => a > 2)
                                pb.assumes.push(assumes);
                            }
                        } else {
                            self.pending_branches.push_back(PendingBranchInfo {
                                target: branch.target,
                                reversed_direction: self.reversed_direction,
                                assumes: vec![assumes],
                                b: vec![branch],
                                from: vec![branch_id],
                                to_bb: target_block_id,
                                stack_snapshot: vec![stack_snapshot],
                            });
                        }
                    }
                    for _ in 0..self.g.stack.stack.len() {
                        self.g.stack.pop().unwrap();
                    }
                    if self.conf.allow_pruning {
                        self.g.clean_poped_values();
                    }
                    self.g.current_block_mut().is_finalized = true;
                    return;
                },
                // x => todo!("Unhandled branching result: {:?}", x),
            }

            if self.conf.allow_pruning {
                self.g.clean_poped_values();
            }

            self.position = self.next_position();
        }
        if self.conf.allow_pruning {
            self.g.clean_poped_values();
        }
        if self.conf.should_log(3) {
            println!("Finalizing block. Stack: {}", self.g.fmt_stack());
        }
        self.g.stack.check_invariants();
        if self.g.current_block_mut().is_terminated {
            self.g.stack.clear();
        } else {
            self.g.push_instr_may_deopt(OptOp::deopt_always(), &[]);
            self.g.current_block_mut().is_finalized = true;
        }
    }


    pub fn interpret(&mut self) -> () {
        self.g.set_program_position(Some(self.position));

        'main: loop {
            self.interpret_block();

            // try to hoist common code from successor blocks into the just-finished current block
            if self.conf.allow_uphoisting &&
                let &[incoming_jump] = &self.g.current_block_ref().incoming_jumps[..]
            {
                let did_hoist = hoist_up(&mut self.g, incoming_jump.0);
                if did_hoist && self.conf.should_log(2) {
                    println!("  Hoisted code up from successors of block {}", self.g.block_(incoming_jump.0));
                    for s in self.g.block_(incoming_jump.0).following_blocks() {
                        println!("  {}", self.g.block_(s))
                    }
                }
            }

            let pb = loop {
                let Some(pb) = self.pending_branches.pop_front() else {
                    break 'main;
                };
                if !self.g.block_(pb.to_bb).is_reachable {
                    if self.conf.should_log(2) {
                        println!("Skipping pending branch {pb:?}, the target block is unreachable")
                    }
                    continue;
                }
                if self.conf.should_log(2) {
                    println!("Continuing on pending branch {pb:?}");
                }
                break pb;
            };
            let bid = pb.to_bb;
            assert_eq!(self.g.block_(bid).parameters, []);
            assert!(!pb.stack_snapshot.is_empty());
            let stack_depth = pb.stack_snapshot[0].depth;
            for s in &pb.stack_snapshot {
                assert_eq!(s.depth, stack_depth);
            }
            assert!(pb.stack_snapshot.iter().all(|snap| snap.stack.len() == pb.stack_snapshot[0].stack.len()));
            let mut preds = pb.from.iter()
                .map(|inc| self.g.block_(inc.0))
                .min_by_key(|p| p.predecessors.len())
                .map(|b| {
                    let mut p = b.predecessors.clone();
                    p.insert(b.id);
                    p
                }).unwrap();
            for &inc in &pb.from {
                let block_preds = &self.g.block_(inc.0).predecessors;
                preds.retain(|p| *p == inc.0 || block_preds.contains(p));
            }
            {
                let block_mut = self.g.block_mut(bid).unwrap();
                block_mut.incoming_jumps.extend_from_slice(&pb.from);
                block_mut.predecessors = preds;
            }
            self.position = pb.target;
            self.g.assumed_program_position = Some(pb.target);
            // stack will be created by seal_block from auto-created parameters
            self.g.switch_to_block(bid, pb.stack_snapshot[0].depth, vec![]);
            assert_eq!(self.g.stack.stack, []);
            assert_eq!(pb.assumes.len(), pb.stack_snapshot.len());
            self.g.seal_block(bid);

            let common_assumes: BTreeSet<_> =
                 pb.assumes.iter().enumerate()
                    .map(|(edge_ix, a)| a.iter().map(|x| {
                        let assume = self.g.fix_replaced_values_cond(x);
                        // replace arguments with PHI values
                        let assume = assume.replace_regs(|r|
                            if let Some(param_ix) = self.g.get_instruction_(pb.from[edge_ix]).inputs.iter().position(|i| i == r){
                                self.g.block_(bid).parameters[param_ix]
                            } else {
                                 *r
                            }
                        );
                        simplify_cond(&mut self.g, assume, InstrId(bid, 1))
                    }).collect())
                    .reduce(|mut a: BTreeSet<_>, b: BTreeSet<_>| { a.retain(|x| b.contains(x)); a }).unwrap();

            for assume in common_assumes {
                self.g.add_assumption_simple(InstrId(bid, 0), assume);
            }

            if self.g.block_(bid).incoming_jumps.len() > 1 {
                self.g.push_checkpoint();
            }
            assert_eq!(self.g.stack.stack.len(), pb.stack_snapshot[0].stack.len());
        }

        // kill remaining pending branches
        while let Some(pb) = self.pending_branches.pop_front() {
            println!("Killing pending branch to {} with {} branches", pb.target, pb.b.len());
            todo!()
        }

        self.g.set_program_position(None);
        if self.conf.should_log(2) {
            println!("F Stack: {}", self.g.fmt_stack());
            println!("FINAL Program:");
            println!("{}", self.g);
        }
    }
}

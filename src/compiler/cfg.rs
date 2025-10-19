use core::{fmt};
use std::{
    borrow::Cow, collections::{BTreeMap, BTreeSet, HashMap, HashSet}, i32, mem, ops::{Range, RangeInclusive}
};

use arrayvec::ArrayVec;
use smallvec::{SmallVec, ToSmallVec, smallvec};

use crate::{compiler::{ops::{BlockId, InstrId, OpEffect, OptInstr, OptOp, ValueId, ValueInfo}, simplifier, utils::intersect_range, vm_code::Condition}, vm::OperationError};

// #[derive(Debug, Clone, PartialEq)]
// struct DeoptInfo<TReg> {
//     pub error: Option<OperationError>, // whether to raise an error
//     pub error_value: Option<TReg>, // which register contains an error argument
//     pub stack_unroll: u32, // how many stack positions to pop
//     pub stack_push: Vec<TReg>, // which registers to push onto stack
//     pub instruction_pointer: usize, // where to continue execution
//     pub reverse_direction: bool // whether to continue in reverse direction
// }

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BlockId,
    pub parameters: Vec<ValueId>,
    pub instructions: BTreeMap<u32, OptInstr>,
    pub incoming_jumps: Vec<InstrId>,
    pub outgoing_jumps: Vec<(InstrId, BlockId)>,
    pub next_instr_id: u32,
    pub is_sealed: bool,    // no more incoming_jumps will be added
    pub is_finalized: bool, // no more instructions will be added
    pub is_terminated: bool, // has terminal instruction (deopt false, jump true, etc)
    pub predecessors: HashSet<BlockId>, // all dominators
                                        // pub successors: Vec<BlockId>,
}

impl BasicBlock {
    pub fn new(id: BlockId, is_sealed: bool, parameters: Vec<ValueId>) -> Self {
        Self {
            id,
            parameters,
            instructions: BTreeMap::new(),
            incoming_jumps: Vec::new(),
            outgoing_jumps: Vec::new(),
            next_instr_id: 1,
            predecessors: HashSet::new(),
            is_finalized: false,
            is_terminated: false,
            is_sealed,
        }
    }

    pub fn is_entry(&self) -> bool {
        self.id.0 == 0
    }

    pub fn add_instruction(&mut self, mut instr: OptInstr) -> &mut OptInstr {
        let id = InstrId(self.id, self.next_instr_id);
        assert!(instr.id == InstrId(BlockId(0), 0) || instr.id == id, "Instruction already has an id: {:?}, expected {:?}", instr.id, id);
        instr.id = id;
        self.next_instr_id += 1;
        if let OptOp::Jump(_, target) = &instr.op {
            self.outgoing_jumps.push((id, *target));
        }
        let entry = self.instructions.entry(id.1);
        assert!(matches!(entry, std::collections::btree_map::Entry::Vacant(_)), "Instruction ID already exists in block: {:?}", id);
        entry.or_insert(instr)
    }
}

impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "BB {}({}) {{",
            self.id,
            self.parameters.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", ")
        )?;
        if !self.predecessors.is_empty() {
            writeln!(f, "    // preds: {}", self.predecessors.iter().map(|b| format!("{}", b)).collect::<Vec<_>>().join(", "))?;
        }
        if !self.incoming_jumps.is_empty() || !self.is_sealed {
            writeln!(f, "    // incoming: {}{}",
                self.incoming_jumps.iter().map(|j| format!("{}", j)).collect::<Vec<_>>().join(", "),
                if self.is_sealed { "" } else { " (not sealed)" }
            )?;
        }
        if !self.outgoing_jumps.is_empty() {
            writeln!(f, "    // outgoing: {}", self.outgoing_jumps.iter().map(|(j, b)| format!("i{} -> bb{}", j.1, b)).collect::<Vec<_>>().join(", "))?;
        }
        for instr in self.instructions.values() {
            writeln!(f, "    {}", instr)?;
        }
        if !self.is_finalized {
            writeln!(f, "    ...")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct StackHistory {
    pub base: u32,
    pub pop: u32,
    pub push: Box<[ValueId]>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StackState {
    pub depth: u32,
    pub stack: Vec<ValueId>,
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum ConstOrVal { Const(i64), Val(ValueId) }

#[derive(Debug, Clone, PartialEq)]
pub struct StackStateTracker {
    pub stack: Vec<ValueId>,
    pub lookup: HashMap<ValueId, Vec<u32>>,
    pub poped_values: Vec<ValueId>, // values that were popped from the stack (will be checked if used somewhere, and maybe removed)
    pub stack_depth: u32,
    pub push_count: u32,
    pub pop_count: u32,
    pub stack_history: Vec<StackHistory>,
    pub pop_from_last_history: u32,
    pub push_from_last_history: u32,
}

impl StackStateTracker {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            lookup: HashMap::new(),
            poped_values: Vec::new(),
            stack_depth: 0,
            stack_history: vec![],
            pop_from_last_history: 0,
            push_from_last_history: 0,
            push_count: 0,
            pop_count: 0,
        }
    }

    pub fn stack_position(&self) -> i32 {
        self.stack.len() as i32 - self.stack_depth as i32
    }

    pub fn record_real_pop(&mut self) {
        self.stack_depth += 1;
    }

    pub fn peek(&self) -> Option<ValueId> {
        self.stack.last().copied()
    }

    pub fn get(&self, ix: usize) -> Option<&ValueId> {
        self.stack.get(self.stack.len() - 1 - ix)
    }

    pub fn pop(&mut self) -> Option<ValueId> {
        if let Some(val) = self.stack.pop() {
            self.pop_count += 1;
            if self.push_from_last_history > 0 {
                self.push_from_last_history -= 1;
            } else {
                self.pop_from_last_history += 1;
            }

            let x = self.lookup.get_mut(&val).unwrap();
            assert_eq!(x.pop(), Some(self.stack.len() as u32));
            if x.is_empty() {
                self.lookup.remove(&val);
                self.poped_values.push(val);
            }
            Some(val)
        } else {
            None
        }
    }

    pub fn push(&mut self, val: ValueId) {
        self.push_count += 1;
        self.push_from_last_history += 1;
        self.lookup.entry(val).or_insert_with(Vec::new).push(self.stack.len() as u32);
        self.stack.push(val);
    }

    pub fn save_history(&mut self) -> u32 {
        let pop = self.pop_from_last_history;
        let pushes = self.push_from_last_history;
        let entry = if (pushes as usize) < self.stack.len() && self.stack_history.len() > 0 {
            StackHistory {
                base: self.stack_history.len() as u32,
                pop,
                push: self.stack[self.stack.len() - pushes as usize..].into(),
            }
        } else {
            StackHistory { base: 0, pop: self.stack_depth, push: self.stack[..].into() }
        };
        self.stack_history.push(entry);
        self.pop_from_last_history = 0;
        self.push_from_last_history = 0;
        self.stack_history.len() as u32
    }

    pub fn save(&mut self) -> StackState {
        StackState {
            depth: self.stack_depth,
            stack: self.stack.clone(),
        }
    }
    pub fn restore(&mut self, state: StackState) {
        self.pop_from_last_history = self.stack.len() as u32;
        self.push_from_last_history = state.stack.len() as u32;
        self.stack = state.stack;
        self.stack_depth = state.depth;
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GraphBuilder {
    pub values: HashMap<ValueId, ValueInfo>,
    pub blocks: Vec<BasicBlock>,
    pub current_block: BlockId,
    pub stack: StackStateTracker,
    pub next_val_id: i32,
    pub constants: Vec<i64>,
    pub constant_lookup: HashMap<i64, ValueId>,
    pub value_index: HashMap<(OptOp<ValueId>, SmallVec<[ValueId; 4]>), Vec<(ValueId, InstrId)>>, // value numbering - common subexpression elimination
    pub assumed_program_position: Option<usize>
}

impl GraphBuilder {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
            blocks: vec![BasicBlock::new(BlockId(0), true, vec![])],
            current_block: BlockId(0),
            stack: StackStateTracker::new(),
            next_val_id: 1,
            constants: vec![],
            constant_lookup: HashMap::new(),
            value_index: HashMap::new(),
            assumed_program_position: None,
        }
    }

    pub fn set_program_position(&mut self, pos: Option<usize>) {
        self.assumed_program_position = pos;
    }

    pub fn current_block_mut(&mut self) -> &mut BasicBlock {
        self.block_mut(self.current_block).unwrap()
    }

    pub fn current_block_ref(&self) -> &BasicBlock {
        self.block_(self.current_block)
    }

    pub fn next_instr_id(&self) -> InstrId {
        InstrId(self.current_block, self.current_block_ref().next_instr_id)
    }

    pub fn new_block(&mut self, is_sealed: bool, parameters: Vec<ValueId>) -> &mut BasicBlock {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(BasicBlock::new(id, is_sealed, parameters));
        self.block_mut(id).unwrap()
    }

    pub fn get_phi_sources(&self, val: ValueId) -> SmallVec<[ValueId; 4]> {
        let mut result: SmallVec<[ValueId; 4]> = smallvec![];
        let mut visited: SmallVec<[ValueId; 4]> = smallvec![val];
        let mut stack: SmallVec<[ValueId; 4]> = smallvec![val];

        while let Some(val) = stack.pop() {
            let x = self.val_info(val).and_then(|info| info.assigned_at);
            match x {
                Some(instr_id) if instr_id.is_block_head() => {
                    let block = self.block_(instr_id.block_id());
                    if !block.is_sealed {
                        // treat this as normal value, we don't know where it will come from
                        if !result.contains(&val) {
                            result.push(val);
                        }
                        continue;
                    }

                    let param_index = block.parameters.iter().position(|&v| v == val).unwrap();
                    for incoming in &block.incoming_jumps {
                        let jump = self.get_instruction(*incoming).unwrap();
                        let source_val = jump.inputs[param_index];
                        if !visited.contains(&source_val) {
                            stack.push(source_val);
                            visited.push(val);
                        }
                    }
                }
                _ => {
                    if !result.contains(&val) {
                        result.push(val);
                    }
                }
            }
        }
        result
    }

    pub fn seal_block(&mut self, id: BlockId) {
        let (block_id, params, incoming) = {
            let block = self.block_mut(id).unwrap();
            if block.is_sealed { return; }
            block.is_sealed = true;
            (block.id, block.parameters.clone(), block.incoming_jumps.clone())
        };

        // remove trivial phis (params) and tighten ranges for real phis; lazily create params if needed
        let mut replacements: BTreeMap<ValueId, ValueId> = BTreeMap::new();
        let mut tighten_ranges: BTreeMap<usize, RangeInclusive<i64>> = BTreeMap::new();

        if incoming.is_empty() {
            assert_eq!(0, params.len());
        } else if incoming.len() == 1 {
            // all parameters are trivial
            let jump_id = incoming[0];
            if params.is_empty() {
                // init the stack with jump inputs
                let jump = self.get_instruction_(jump_id);
                for src in jump.inputs.clone() {
                    self.stack.push(src);
                }
            } else {
                let jump = self.get_instruction_(jump_id);
                for (&src, &p) in params.iter().zip(&jump.inputs) {
                    if p != src { replacements.insert(p, src); }
                }
                self.block_mut(block_id).unwrap().parameters.clear();
            }

            self.instr_mut(jump_id).unwrap().inputs.clear();
        } else {
            let jumps: Vec<&OptInstr> = incoming.iter().map(|j| self.get_instruction(*j).unwrap()).collect();
            let arg_count = jumps[0].inputs.len();
            for j in &jumps {
                assert_eq!(j.inputs.len(), arg_count, "Inconsistent number of arguments to block {}: expected {}, got {} from jump {}", block_id, arg_count, j.inputs.len(), j.id);
            }

            let mut resolved: Vec<Option<ValueId>> = vec![None; arg_count];
            for i in 0..arg_count {
                let vals: BTreeSet<ValueId> = jumps.iter().flat_map(|j| self.get_phi_sources(j.inputs[i])).collect();
                assert!(!vals.is_empty());
                if vals.len() == 1 {
                    resolved[i] = Some(*vals.iter().next().unwrap());
                } else {
                    let range = vals.iter().map(|v| self.val_range(*v))
                        .reduce(|a, b| intersect_range(&a, &b))
                        .unwrap();
                    tighten_ranges.insert(i, range);
                }
            }

            let keep_ix: Vec<usize> = (0..arg_count).filter(|i| resolved[*i].is_none()).collect();

            if params.is_empty() {
                // lazy-init: create parameters for non-trivial phis; drop trivial ones entirely
                //  + also append all jump values to the stack
                let mut new_params: Vec<ValueId> = Vec::with_capacity(keep_ix.len());
                let mut new_stack: Vec<ValueId> = resolved.iter().map(|x| x.unwrap_or(ValueId(0))).collect();
                for &i in &keep_ix {
                    // create a new parameter value anchored at block head and with tightened range
                    let vi = self.new_value();
                    vi.assigned_at = Some(InstrId(block_id, 0));
                    vi.range = tighten_ranges.get(&i).cloned().unwrap_or(i64::MIN..=i64::MAX);
                    new_params.push(vi.id);
                    new_stack[i] = vi.id;
                }
                assert!(!new_stack.contains(&ValueId(0)));
                self.block_mut(block_id).unwrap().parameters = new_params;
                for val in new_stack {
                    self.stack.push(val);
                }
            } else {
                for i in 0..arg_count {
                    if let Some(val) = resolved[i] {
                        if let Some(&param) = params.get(i) {
                            if param != val { replacements.insert(param, val); }
                        }
                    }
                }
                
                // filter block params
                let new_params = keep_ix.iter().map(|&i| params[i]).collect();
                self.block_mut(block_id).unwrap().parameters = new_params;
            }
            // filter jumps
            for &jid in &incoming {
                if let Some(instr) = self.instr_mut(jid) {
                    let filtered = keep_ix.iter().map(|&i| instr.inputs[i]).collect();
                    instr.inputs = filtered;
                }
            }
        }

        self.replace_values(replacements);

        // tighten ranges of remaining params
        for (ix, p) in params.iter().enumerate() {
            if let Some(new_range) = tighten_ranges.get(&ix) {
                if let Some(info) = self.values.get_mut(&p) {
                    let new_range = intersect_range(&info.range.clone(), new_range);
                    assert!(!new_range.is_empty(), "Empty range for parameter {} of block {} after tightening ({:?}, {:?})", p, block_id, info.range, new_range);
                    info.range = new_range;
                }
            }
        }
    }

    pub fn switch_to_block(&mut self, id: BlockId, stack_depth: u32, stack_state: Vec<ValueId>) {
        self.current_block = id;
        self.stack.restore(StackState {
            depth: stack_depth,
            stack: stack_state,
        });
    }

    pub fn new_value(&mut self) -> &mut ValueInfo {
        let id = ValueId(self.next_val_id);
        self.next_val_id += 1;
        let info = ValueInfo {
            id,
            assigned_at: None,
            range: i64::MIN..=i64::MAX,
            used_at: HashSet::new(),
        };
        let entry = self.values.entry(id);
        assert!(matches!(entry, std::collections::hash_map::Entry::Vacant(_)), "Value ID already exists: {:?}", entry);
        entry.or_insert(info)
    }

    pub fn value_numbering_try_lookup(&self, op: OptOp<ValueId>, args: &[ValueId], at: InstrId) -> Option<ValueId> {
        let instr = (op, args.to_smallvec());
        if let Some(vals) = self.value_index.get(&instr) {
            for (val, instr) in vals {
                if instr.block_id() == at.block_id() {
                    if instr.instr_ix() < at.instr_ix() {
                        return Some(*val);
                    }
                } else if instr.block_id().is_first_block()
                    || self.current_block_ref().predecessors.contains(&instr.block_id())
                {
                    return Some(*val);
                }
            }
        }
        None
    }

    fn replace_values(&mut self, mut replace: BTreeMap<ValueId, ValueId>) {
        while !replace.is_empty() {
            let (old, new) = replace.pop_first().unwrap();
            if old == new {
                continue;
            }
            assert!(old.is_computed(), "non-computed value {:?} {}", old, old);
            if let Some(is) = self.stack.lookup.remove(&old) {
                for &i in &is {
                    self.stack.stack[i as usize] = new;
                }
                let xs = self.stack.lookup.entry(new).or_default();
                xs.extend(&is);
                xs.sort();
            }

            let info = self.values.remove(&old).unwrap();
            for &instr_id in &info.used_at {
                let instr = self.instr_mut(instr_id).unwrap();
                for inp in &mut instr.inputs {
                    if *inp == old {
                        *inp = new;
                    }
                }

                let instr = self.get_instruction(instr_id).unwrap();

                // simplifier::simplify_instr(cfg, i) TODO

                if instr.effect.allows_value_numbering() {
                    if let Some(v) = self.value_numbering_try_lookup(instr.op.clone(), &instr.inputs, instr_id) {
                        replace.insert(instr.out, v);
                        // self.instr_mut(instr_id).unwrap().effect = OpEffect::None;
                    }
                }
            }
        }
    }

    fn value_numbering_store(&mut self, op: OptOp<ValueId>, args: &[ValueId], val: ValueId, defined_at: InstrId) {
        let instr = (op, args.to_smallvec());
        let v = self.value_index.entry(instr).or_insert_with(Vec::new);
        if v.last() != Some(&(val, defined_at)) {
            v.push((val, defined_at));
        }
    }

    pub fn value_numbering(
        &mut self,
        op: OptOp<ValueId>,
        args: &[ValueId],
        range: Option<RangeInclusive<i64>>,
        effect: Option<OpEffect>,
    ) -> ValueId {
        // TODO: also store unsimplified expr?
        // if let Some(existing_val) = self.value_numbering_try_lookup(op.clone(), args) {
        //     return existing_val;
        // }

        self.push_instr(op, args, true, range, effect).0
    }

    pub fn store_constant(&mut self, value: i64) -> ValueId {
        if let Some(predefined) = ValueId::from_predefined_const(value) {
            return predefined
        }
        if let Some(&id) = self.constant_lookup.get(&value) {
            return id;
        }
        let id = ValueId::new_const(ValueId::PREDEF_RANGE + self.constants.len() as i32 + 1);
        self.constants.push(value);
        self.constant_lookup.insert(value, id);
        id
    }

    fn mark_used_at(&mut self, val: ValueId, instr: InstrId) {
        if val.is_constant() || val.is_null() {
            return;
        }

        if let Some(info) = self.values.get_mut(&val) {
            info.used_at.insert(instr);
        }
    }

    fn infer_op_range_effect(&self, op: &OptOp<ValueId>, args: &[ValueId]) -> (Option<RangeInclusive<i64>>, OpEffect) {
        let ranges = args.iter().map(|v| self.val_range(*v)).collect::<Vec<_>>();
        (op.evaluate_range_quick(&ranges), op.effect_based_on_ranges(&ranges))
    }

    pub fn push_instr(&mut self, op: OptOp<ValueId>, args: &[ValueId], value_numbering: bool, out_range: Option<RangeInclusive<i64>>, effect: Option<OpEffect>) -> (ValueId, Option<&mut OptInstr>) {
        // assert!(!out.is_constant(), "Cannot assign to constant: {:?} <- {:?}{:?}", out, op, args);
        assert!(!args.contains(&ValueId(0)), "Cannot use null ValueId: {:?}{:?}", op, args);
        assert!(!self.current_block_ref().is_finalized, "Cannot add instruction to finalized block: {:?}", self.current_block_ref());

        let effect2 = match effect {
            Some(e) => OpEffect::better_of(e, op.worst_case_effect()),
            None => op.worst_case_effect()
        };
        let value_numbering = value_numbering && effect2.allows_value_numbering();

        let has_output = op.has_output();

        let instr = OptInstr {
            id: InstrId(self.current_block, u32::MAX),
            op: op.clone(),
            inputs: args.into(),
            out: if has_output { ValueId(i32::MAX) } else { ValueId(0) },
            stack_state: None,
            program_position: self.assumed_program_position.unwrap_or(usize::MAX),
            effect: effect2
        };

        let (mut instr, simplifier_range) = simplifier::simplify_instr(self, instr);
        instr.id = InstrId(self.current_block, self.current_block_ref().next_instr_id);
        assert_eq!(has_output, instr.op.has_output());

        if instr.op == OptOp::Nop {
            return (ValueId(0), None);
        }

        if instr.op == OptOp::Add && instr.inputs.len() == 1 {
            // used to signal value already exists
            return (instr.inputs[0], None);
        }

        if let OptOp::Const(c) = instr.op {
            return (self.store_constant(c), None);
        }

        if value_numbering {
            if let Some(existing_val) = self.value_numbering_try_lookup(instr.op.clone(), &instr.inputs, instr.id) {
                return (existing_val, None);
            }
        }

        let mut out_val = ValueId(0);
        if has_output {
            let (inferred_range, inferred_effect) = self.infer_op_range_effect(&instr.op, &instr.inputs);
            instr.effect = OpEffect::better_of(instr.effect, inferred_effect);
            let val_range =
                simplifier_range.iter().chain(&out_range).chain(&inferred_range)
                    .cloned()
                    .reduce(|a, b| intersect_range(&a, &b))
                    .unwrap_or(i64::MIN..=i64::MAX);
            assert!(!val_range.is_empty() || instr.op.is_terminal(), "Empty output range for instr {}: {:?} <- {:?}{:?} (specified range={out_range:?}, simplifier range={out_range:?}, inferred range={inferred_range:?})", instr.id, instr.out, instr.op, instr.inputs);

            if *val_range.start() == *val_range.end() {
                out_val = self.store_constant(*val_range.start());
                instr.out = ValueId(0);
            } else {
                let val = self.new_value();
                val.range = val_range;
                val.assigned_at = Some(instr.id);
                out_val = val.id;
                instr.out = val.id;
            }
        }

        if instr.out == ValueId(0) && instr.effect == OpEffect::None {
            return (out_val, None)
        }

        assert!(self.current_block_ref().is_finalized == false, "Cannot add instruction to finalized block: {:?}", self.current_block_ref());
        if instr.op.is_terminal() {
            self.current_block_mut().is_terminated = true;
        }

        if value_numbering {
            self.value_numbering_store(instr.op.clone(), &instr.inputs, out_val, instr.id);
        }

        for arg in instr.iter_inputs() {
            self.mark_used_at(arg, instr.id);
        }

        let instr = self.current_block_mut().add_instruction(instr);
        (out_val, Some(instr))
    }

    pub fn push_instr_may_deopt(&mut self, op: OptOp<ValueId>, args: &[ValueId]) -> &mut OptInstr {
        // TODO: refactor as checkpoint instruction
        let stack_state = self.stack.save_history();
        let instr = self.push_instr(op, args, false, None, None).1.unwrap();
        instr.stack_state = Some(stack_state);
        instr
    }

    pub fn push_assert(&mut self, c: Condition<ValueId>, error: OperationError, val: Option<ValueId>) {
        let mut args: ArrayVec<ValueId, 1> = ArrayVec::new();
        if let Some(val) = val {
            args.push(val);
        }
        self.push_instr(OptOp::Assert(c, error), &args, false, None, None);
    }

    pub fn push_deopt_assert(&mut self, c: Condition<ValueId>, precise_deoptinfo: bool) {
        let c = simplifier::canonicalize_condition(self, c);
        if c == Condition::True { return; }

        if precise_deoptinfo {
            self.push_instr_may_deopt(OptOp::DeoptAssert(c), &[]);
        } else {
            self.push_instr(OptOp::DeoptAssert(c), &[], false, None, None);
        }
    }

    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(id.0 as usize)
    }

    pub fn block_(&self, id: BlockId) -> &BasicBlock {
        let Some(x) = self.blocks.get(id.0 as usize) else {
            panic!("Block {id} does not exist (there is {} BBs)", self.blocks.len());
        };
        x
    }

    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut BasicBlock> {
        self.blocks.get_mut(id.0 as usize)
    }

    pub fn instr_mut(&mut self, id: InstrId) -> Option<&mut OptInstr> {
        self.block_mut(id.block_id())?.instructions.get_mut(&id.instr_ix())
    }

    pub fn set_effect(&mut self, id: InstrId, effect: OpEffect) {
        let instr = self.instr_mut(id).unwrap();
        instr.effect = effect;
    }

    pub fn pop_stack(&mut self) -> ValueId {
        match self.stack.pop() {
            Some(reg) => reg,
            None => {
                self.stack.record_real_pop();
                self.push_instr(OptOp::Pop, &[], false, None, None).0
            }
        }
    }

    pub fn pop_stack_n(&mut self, n: usize) -> Vec<ValueId> {
        let mut r = vec![];
        for _ in 0..n {
            r.push(self.pop_stack());
        }
        r
    }

    pub fn peek_stack(&mut self) -> ValueId {
        match self.stack.peek() {
            Some(reg) => reg,
            None => {
                let reg = self.pop_stack();
                self.stack.push(reg);
                reg
            }
        }
    }
    pub fn peek_stack_n(&mut self, n: Range<usize>) -> Vec<ValueId> {
        if n.end <= self.stack.stack.len() {
            n.into_iter().map(|i| self.stack.get(i).copied().unwrap()).collect()
        } else {
            let mut vals = vec![];
            let mut result = vec![];
            for i in 0..n.end {
                let reg = self.pop_stack();
                vals.push(reg);
                if i >= n.start {
                    result.push(reg);
                }
            }
            for &reg in vals.iter().rev() {
                self.stack.push(reg);
            }
            result
        }
    }

    pub fn peek_stack_2(&mut self) -> (ValueId, ValueId) {
        let regs = self.peek_stack_n(0..2);
        (regs[0], regs[1])
    }

    pub fn peek_stack_3(&mut self) -> (ValueId, ValueId, ValueId) {
        let regs = self.peek_stack_n(0..3);
        (regs[0], regs[1], regs[2])
    }

    pub fn get_instruction(&self, id: InstrId) -> Option<&OptInstr> {
        let b = self.blocks.get(id.block_id().0 as usize)?;
        b.instructions.get(&id.instr_ix())
    }

    pub fn get_instruction_(&self, id: InstrId) -> &OptInstr {
        let Some(b) = self.blocks.get(id.0.0 as usize) else {
            panic!("Block of instr {id} does not exist (there is {} BBs)", self.blocks.len());
        };
        let Some(instr) = b.instructions.get(&id.instr_ix()) else {
            panic!("Instruction {id} does not exist. Block: {}",  b);
        };
        instr
    }

    pub fn get_constant(&self, id: ValueId) -> Option<i64> {
        if id.is_constant() {
            id.to_predefined_const().or_else(|| Some(self.constants[(-id.0 - 1 - ValueId::PREDEF_RANGE) as usize]))
        } else {
            None
        }
    }

    pub fn get_constant_(&self, id: ValueId) -> i64 {
        if !id.is_constant() {
            panic!("Not a constant: {:?}", id);
        }
        if let Some(x) = id.to_predefined_const() {
            x
        } else {
            self.constants[(-id.0 - 1 - ValueId::PREDEF_RANGE) as usize]
        }
    }

    pub fn list_used_constants(&self) -> Vec<(ValueId, i64)> {
        let mut used = HashMap::new();
        for b in &self.blocks {
            for i in b.instructions.values() {
                for v in i.iter_inputs() {
                    if v.is_constant() && v.to_predefined_const().is_none() {
                        used.entry(v).or_insert_with(|| {
                            let Some(c) = self.get_constant(v) else {
                                panic!("Cannot find constant {} used by {}", v, i)
                            };
                            c
                        });
                    }
                }
            }
        }

        used.into_iter().collect()
    }

    pub fn get_defined_at<'a>(&'a self, v: ValueId) -> Option<&'a OptInstr> {
        if v.is_constant() { return None }
        self.val_info(v).and_then(|info| info.assigned_at)
                        .and_then(|at| self.get_instruction(at))
    }

    pub fn val_info<'a>(&'a self, v: ValueId) -> Option<Cow<'a, ValueInfo>> {
        if v.is_constant() {
            let c = self.get_constant_(v);
            let mut x = ValueInfo::new(v);
            x.range = c..=c;
            Some(Cow::Owned(x))
        } else {
            self.values.get(&v).map(|v| Cow::Borrowed(v))
        }
    }

    pub fn val_range(&self, v: ValueId) -> RangeInclusive<i64> {
        if v.is_constant() {
            let c = self.get_constant_(v);
            return c..=c;
        }
        match self.values.get(&v) {
            Some(reg) => reg.range.clone(),
            None => i64::MIN..=i64::MAX,
        }
    }

    pub fn stack_top_info<'a>(&'a self, offset: usize) -> Option<Cow<'a, ValueInfo>> {
        self.stack.get(offset).and_then(|a| self.val_info(*a))
    }

    pub fn fmt_stack(&self) -> String {
        let mut parts = vec![];
        for val in self.stack.stack.iter().rev() {
            if val.is_constant() {
                parts.push(self.get_constant_(*val).to_string());
            } else {
                let (start, end) = self.val_range(*val).into_inner();
                if start != i64::MIN && end != i64::MAX {
                    parts.push(format!("{}[{}..={}]", val, start, end));
                } else if start != i64::MIN {
                    parts.push(format!("{}[{}..]", val, start));
                } else if end != i64::MAX {
                    parts.push(format!("{}[..={}]", val, end));
                } else {
                    parts.push(format!("{}", val));
                }
            }
        }
        parts.reverse();
        format!("{} [{}]", self.stack.stack.len(), parts.join(", "))
    }

    pub fn remove_instruction(&mut self, id: InstrId, force_value_removal: bool) {
        let InstrId(block_id, instr_ix) = id.clone();
        let Some(instr) = self.get_instruction(id) else {
            return;
        };
        let args: Vec<ValueId> = instr.iter_inputs().filter(|r| r.is_computed()).collect();
        let stack_state = instr.stack_state;
        let program_position = instr.program_position;
        let val_id = instr.out;
        if let Some(out_val) = self.values.get(&val_id) {
            assert!(val_id.is_computed());

            if !force_value_removal {
                assert!(out_val.used_at.is_empty(), "Cannot remove instruction {:?} because its output value {:?} is still used at {:?}", id, val_id, out_val.used_at);
            }

            //remove from value_index (value numbering)
            let vi_key = (instr.op.clone(), instr.inputs.clone());
            if let Some(vals) = self.value_index.get_mut(&vi_key) {
                vals.retain(|(v, _i)| *v != val_id);
                if vals.is_empty() {
                    self.value_index.remove(&vi_key);
                }
            }
            self.values.remove(&val_id);
        }
        self.blocks[block_id.0 as usize].instructions.remove(&instr_ix);

        if let Some(stack_state) = stack_state {
            // move the stack state onto the next instruction if it has none to still allow deopting "here"
            if let Some((_, next_instr)) = self.blocks[block_id.0 as usize].instructions.range_mut(instr_ix+1..).next() {
                if next_instr.stack_state.is_none() {
                    next_instr.stack_state = Some(stack_state);
                    next_instr.program_position = program_position; // we must also revert to the previous program position to keep stack and IP in sync
                }
            } else {
                // append annotated Nop to allow deopting
                self.blocks[block_id.0 as usize].add_instruction(OptInstr {
                    id: InstrId(0.into(), 0),
                    op: OptOp::Nop,
                    inputs: SmallVec::new(),
                    out: ValueId(0),
                    stack_state: Some(stack_state),
                    program_position,
                    effect: OpEffect::None,
                });
            }
        }

        // remove inputs if this was their last use


        let mut clean_values = vec![];
        for arg in args {
            if let Some(info) = self.values.get_mut(&arg) {
                info.used_at.remove(&id);
                if info.used_at.is_empty() {
                    clean_values.push(arg);
                }
            }
        }
        for val in clean_values {
            self.clean_value(val);
        }
    }

    pub fn clean_value(&mut self, val: ValueId) {
        let fuck_errors = false;
        if let Some(val) = self.values.get(&val) {
            let val_id  = val.id;
            if val.used_at.is_empty() && !self.stack.lookup.contains_key(&val_id) {
                let Some(instruction_id) = val.assigned_at else {
                    return // it's a parameter or something like that
                };
                if instruction_id.is_block_head() {
                    todo!("phis (BB parameters)")

                } else if let Some(defined_at) = self.get_instruction(instruction_id) {
                    let effect = defined_at.effect;
                    if !(effect == OpEffect::None || (fuck_errors && effect == OpEffect::MayFail)) {
                        // can't remove instruction, no reason to remove the value
                        // maybe codegen can then optimize it to assert-only
                        return;
                    }
                    let instruction_id = defined_at.id;
                    self.remove_instruction(instruction_id, false);

                    assert!(!self.values.contains_key(&val_id), "Value {:?} should have been removed with instruction {:?}", val_id, instruction_id);
                } else {
                    todo!("probably should not happen?");
                }
            }
        }
    }

    pub fn clean_poped_values(&mut self) {
        for val in mem::take(&mut self.stack.poped_values) {
            self.clean_value(val);
        }
    }
}

use core::fmt;
use std::{
    borrow::Cow, cmp, collections::{BTreeMap, HashMap, HashSet}, fmt::Display, mem, num::NonZeroI32, ops::{Range, RangeInclusive}
};

use smallvec::SmallVec;

use crate::{compiler::vm_code::Condition, vm::OperationError};

// const PREDEFINED_VALUES: [i64; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 24, 32, 64, 128, 256, 512, 1024, i64::MAX, -1, -2, -3];

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(pub i32);
impl ValueId {
    pub const PREDEF_RANGE: i32 = 4096;
    pub const C_ZERO: ValueId = Self::from_predefined_const(0).unwrap();
    pub const C_ONE: ValueId = Self::from_predefined_const(1).unwrap();
    pub const C_TWO: ValueId = Self::from_predefined_const(2).unwrap();
    pub const C_IMIN: ValueId = Self::from_predefined_const(i64::MIN).unwrap();
    pub const C_IMAX: ValueId = Self::from_predefined_const(i64::MAX).unwrap();
    pub const fn is_null(&self) -> bool {
        self.0 == 0
    }
    pub const fn is_constant(&self) -> bool {
        self.0 < 0
    }
    pub const fn is_computed(&self) -> bool {
        self.0 > 0
    }
    pub const fn to_option(self) -> Option<NonZeroI32> {
        NonZeroI32::new(self.0)
    }

    pub const fn to_predefined_const(self) -> Option<i64> {
        let id = self.0;
        if id >= 0 || id < -ValueId::PREDEF_RANGE {
            return None
        }
        let id = -id;
        if id <= 2049 {
            return Some(id as i64 - 1025);
        }
        if id <= 2049 + 54 {
            return Some((1 as i64) << (id - 2049 + 10));
        }
        if id <= 2049 + 54 + 54 {
            return Some(((1 as i64) << (id - 2049 - 54 + 10)).wrapping_sub(1));
        }
        None
    }

    pub const fn new_val(id: i32) -> ValueId {
        assert!(id > 0);
        ValueId(id)
    }

    pub const fn new_const(id: i32) -> ValueId {
        assert!(id > 0);
        ValueId(-id)
    }

    pub const fn from_predefined_const(x: i64) -> Option<ValueId> {
        if x >= -1024 && x <= 1024 {
            Some(Self::new_const(x as i32 + 1025))
        } else if x & (x.wrapping_sub(1)) == 0 {
            // power of 2 (0010000000 in binary)
            Some(Self::new_const(2049 - 10 + x.trailing_zeros() as i32))
        } else if x & (x.wrapping_add(1)) == 0 {
            // power of 2 - 1 (011111111 in binary)
            Some(Self::new_const(2049 - 10 + 64 - 10 + x.trailing_ones() as i32))
        } else {
            None
        }
    }
}
impl From<i32> for ValueId {
    fn from(value: i32) -> Self {
        ValueId(value)
    }
}
impl fmt::Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_null() {
            write!(f, "∅")
        } else if let Some(c) = self.to_predefined_const() {
            write!(f, "{}", c)
        } else if self.is_constant() {
            write!(f, "c{}", -self.0 - Self::PREDEF_RANGE)
        } else {
            write!(f, "v{}", self.0)
        }
    }
}
impl fmt::Debug for ValueId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

#[test]
fn test_predefined_valueid() {
    let vals = (-1024..=1024).into_iter()
        .chain((0..63).map(|x| 1i64 << x))
        .chain((0..63).map(|x| (1i64 << x).wrapping_sub(1)));
    for v in vals {
        let vid = ValueId::from_predefined_const(v);
        assert!(vid.is_some_and(|x| x.is_constant()), "v={v} vid={:?}", vid.map(|x| x.0));
        assert_eq!(Some(v), ValueId::to_predefined_const(vid.unwrap()), "vid={}", vid.unwrap().0);
    }
    for v in 2049..4095 {
        assert_eq!(None, ValueId::from_predefined_const(v), "{v}");
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);
impl From<u32> for BlockId {
    fn from(value: u32) -> Self { BlockId(value) }
}
impl Into<usize> for BlockId {
    fn into(self) -> usize { self.0 as usize }
}
impl Into<u32> for BlockId {
    fn into(self) -> u32 { self.0 }
}
impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}
impl fmt::Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Unique identifier for instructions
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstrId(pub BlockId, pub u32);
impl InstrId {
    pub fn block_id(self) -> BlockId {
        self.0
    }
    pub fn instr_ix(self) -> u32 {
        self.1
    }
    pub fn is_block_head(self) -> bool {
        self.1 == 0
    }
}
impl fmt::Display for InstrId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "i{}_{}", self.0 .0, self.1)
    }
}
impl fmt::Debug for InstrId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OptOp<TVal: Clone + PartialEq + Eq + Display> {
    Push,
    Pop,
    Nop, // used for stack state accounting

    Add,          // a + b
    Sub,          // a - b
    AbsSub,       // |a - b|
    Mul,          // a * b
    Div,          // a / b
    CursedDiv,    // a % b if non-zero, otherwise a / b
    Mod,          // a % b
    ModEuler,     // a % b (always non-negative)
    Tetration,    // a tetrated b times
    Funkcia,      // funkcia(a, b)
    LenSum,       // len(a) + len(b)
    Max,          // max(a, b)
    Min,          // min(a, b)
    Sgn,          // sgn(a)
    AbsFactorial, // |a|!
    Universal, // universal[a](b, c) (or deopt if different number of params should be used instead)
    And,       // a <- b & c
    Or,        // a <- b | c
    Xor,       // a <- b ^ c
    ShiftL,    // a <- b << c
    ShiftR,    // a <- b >> c

    BinNot,                        // a <- ~b
    BoolNot,                       // a <- !b
    Condition(Condition<TVal>), // a <- condition ? 1 : 0

    Select(Condition<TVal>), // a <- b ? c : d

    DigitSum, // a <- digit_sum(b)
    Gcd,      // a <- gcd(b, c)

    StackSwap, // a <- stack[b]; stack[b] <- c; if b + d < stack_size, otherwise deopt

    Const(i64),

    Jump(Condition<TVal>, BlockId), // if true: jump to BB. `inputs` are parameters for the target BB

    Assert(Condition<TVal>, OperationError, Option<TVal>), // error, optional argument
    DeoptAssert(Condition<TVal>), // if false: abort block execution, IP where we continue
    // Done(u32), // instruction pointer where to continue execution
    Median,
    MedianCursed, // _ <- median(N, a, b, c, ...)
                  // KsplangOp(crate::ops::Op),
                  // KsplangOpWithArg(crate::ops::Op, TReg)
}

impl<TVal: Clone + PartialEq + Eq + Display> OptOp<TVal> {
    pub fn is_terminal(&self) -> bool {
        matches!(self, OptOp::Jump(Condition::True, _) | OptOp::DeoptAssert(Condition::False) | OptOp::Assert(Condition::False, _, _))
    }

    pub fn condition(&self) -> Option<Condition<TVal>> {
        match self {
            OptOp::Condition(cond) => Some(cond.clone()),
            OptOp::Select(cond) => Some(cond.clone()),
            OptOp::Jump(cond, _) => Some(cond.clone()),
            OptOp::Assert(cond, _, _) => Some(cond.clone()),
            OptOp::DeoptAssert(cond) => Some(cond.clone()),
            _ => None,
        }
    }

    pub fn is_commutative(&self, arg_count: usize) -> Range<usize> {
        match self {
            OptOp::Add | OptOp::Mul | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Gcd | OptOp::Max | OptOp::Min | OptOp::AbsSub | OptOp::Median | OptOp::Funkcia | OptOp::LenSum => 0..arg_count,
            OptOp::MedianCursed => 1..arg_count, // first argument is N
            _ => 0..0,
        }
    }

    pub fn worst_case_effect(&self) -> OpEffect {
        match self {
            OptOp::Push | OptOp::Pop => OpEffect::None, // stack push/pop bound checks are tracked separately
            OptOp::Nop | OptOp::Const(_) | OptOp::Condition(_) | OptOp::Select(_) | OptOp::DigitSum | OptOp::Gcd | OptOp::Median | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::ShiftR | OptOp::BinNot | OptOp::BoolNot | OptOp::Funkcia | OptOp::LenSum | OptOp::Min | OptOp::Max | OptOp::Sgn => OpEffect::None,

            // overflow checks, div by zero
            OptOp::Add | OptOp::Sub | OptOp::AbsSub | OptOp::Mul | OptOp::Div | OptOp::CursedDiv | OptOp::Mod | OptOp::ModEuler | OptOp::Tetration | OptOp::ShiftL | OptOp::AbsFactorial =>
                OpEffect::MayFail,

            OptOp::Assert(_, _, _) => OpEffect::MayFail,

            OptOp::Jump(_, _) => OpEffect::ControlFlow,
            OptOp::DeoptAssert(_) | OptOp::Universal | OptOp::MedianCursed => OpEffect::MayDeopt,
            OptOp::StackSwap => OpEffect::StackWrite,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct OptOptPattern {
    pub options_values: Vec<ValueId>,
    pub options_opts: Vec<(OptOp<Box<OptOptPattern>>, Vec<OptOptPattern>)>,
    pub anything_in_range: Vec<RangeInclusive<i64>>,
    pub constant_in_range: Vec<RangeInclusive<i64>>,
    pub disable_commutativity: bool,
}

impl OptOptPattern {
    pub fn new(op: OptOp<Box<OptOptPattern>>, args: Vec<OptOptPattern>) -> Self {
        Self::default().or_op(op, args)
    }

    pub fn new_val(val: ValueId) -> Self {
        Self::default().or_value(val)
    }

    pub fn new_range(range: RangeInclusive<i64>) -> Self {
        Self::default().or_in_range(range)
    }

    pub fn new_constant(range: RangeInclusive<i64>) -> Self {
        Self::default().or_constant(range)
    }

    pub fn or_value(mut self, val: ValueId) -> Self {
        self.options_values.push(val);
        self
    }

    pub fn or_op(mut self, op: OptOp<Box<OptOptPattern>>, args: Vec<OptOptPattern>) -> Self {
        self.options_opts.push((op, args));
        self
    }

    pub fn or_in_range(mut self, range: RangeInclusive<i64>) -> Self {
        self.anything_in_range.push(range);
        self
    }

    pub fn or_constant(mut self, range: RangeInclusive<i64>) -> Self {
        self.constant_in_range.push(range);
        self
    }
}

impl fmt::Display for OptOptPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = vec![];
        if !self.options_values.is_empty() {
            parts.push(format!("Values({})", self.options_values.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", ")));
        }
        if !self.options_opts.is_empty() {
            parts.push(format!("Ops({})", self.options_opts.iter().map(|(op, args)| format!("{:?}({})", op, args.iter().map(|a| format!("{}", a)).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(", ")));
        }
        if !self.anything_in_range.is_empty() {
            parts.push(format!("Range({})", self.anything_in_range.iter().map(|r| format!("{:?}", r)).collect::<Vec<_>>().join(", ")));
        }
        if !self.constant_in_range.is_empty() {
            parts.push(format!("Const({})", self.constant_in_range.iter().map(|r| format!("{:?}", r)).collect::<Vec<_>>().join(", ")));
        }

        let nocomm = if self.disable_commutativity { "no-comm: " } else { "" };

        write!(f, "P({}{})", nocomm, parts.join(" | "))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpEffect {
    None,
    MayFail,
    MayDeopt,
    ControlFlow,
    StackWrite,
}

impl OpEffect {
    pub fn only_if(&mut self, condition: bool) {
        if condition { *self = OpEffect::None }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptInstr {
    pub id: InstrId,
    pub op: OptOp<ValueId>,
    pub inputs: SmallVec<[ValueId; 4]>,
    pub out: ValueId,
    pub stack_state: Option<u32>, // stack state before this instruction (for deoptimization)
    pub program_position: usize, // u64::MAX if unknown
    pub effect: OpEffect,
}

impl OptInstr {
    pub fn iter_inputs(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.inputs.iter().copied().chain(self.op.condition().into_iter().flat_map(|cond| cond.regs()))
    }
}

impl fmt::Display for OptInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{: >3} {: >4} | ", self.id.0.0, self.id.1)?;
        if !self.out.is_null() {
            write!(f, "{} <- ", self.out)?;
        }
        write!(f, "{:?}", self.op)?;
        for arg in &self.inputs {
            write!(f, " {}", arg)?;
        }
        write!(f, "   [ ")?;
        if self.effect != self.op.worst_case_effect() {
            write!(f, "{:?} ", self.effect)?;
        }
        if let Some(stack_state) = self.stack_state {
            write!(f, "stack={} ", stack_state)?;
        }
        write!(f, "IP={} ]", self.program_position)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValueInfo {
    pub id: ValueId,
    pub assigned_at: Option<InstrId>,
    pub range: RangeInclusive<i64>,
    pub used_at: HashSet<InstrId>,
}

impl ValueInfo {
    pub fn new(id: ValueId) -> Self {
        Self { id, assigned_at: None, range: i64::MIN..=i64::MAX, used_at: HashSet::new() }
    }
    pub fn is_constant(&self) -> bool {
        self.range.start() == self.range.end()
    }
    pub fn as_constant(&self) -> Option<i64> {
        if self.is_constant() {
            Some(*self.range.start())
        } else {
            None
        }
    }
}

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
    pub predecessors: HashSet<BlockId>, // all dominators
                                        // pub successors: Vec<BlockId>,
}

impl BasicBlock {
    pub fn new(id: BlockId, parameters: Vec<ValueId>) -> Self {
        Self {
            id,
            parameters,
            instructions: BTreeMap::new(),
            incoming_jumps: Vec::new(),
            outgoing_jumps: Vec::new(),
            next_instr_id: 1,
            predecessors: HashSet::new(),
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
        writeln!(f, "BB {}({}) {{", self.id, self.parameters.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "))?;
        if !self.predecessors.is_empty() {
            writeln!(f, "    // preds: {}", self.predecessors.iter().map(|b| format!("{}", b)).collect::<Vec<_>>().join(", "))?;
        }
        if !self.incoming_jumps.is_empty() {
            writeln!(f, "    // incoming: {}", self.incoming_jumps.iter().map(|j| format!("{}", j)).collect::<Vec<_>>().join(", "))?;
        }
        if !self.outgoing_jumps.is_empty() {
            writeln!(f, "    // outgoing: {}", self.outgoing_jumps.iter().map(|(j, b)| format!("i{} -> bb{}", j.1, b)).collect::<Vec<_>>().join(", "))?;
        }
        for instr in self.instructions.values() {
            writeln!(f, "    {}", instr)?;
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

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum ConstOrVal { Const(i64), Val(ValueId) }

#[derive(Debug, Clone, PartialEq)]
pub struct StackStateTracker {
    pub stack: Vec<ValueId>,
    pub lookup: HashMap<ValueId, Vec<u32>>,
    pub poped_values: Vec<ValueId>, // values that were popped from the stack (will be checked if used somewhere, and maybe removed)
    pub stack_depth: u32,
    pub stack_position: i32,
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
            stack_position: 0,
            stack_history: vec![],
            pop_from_last_history: 0,
            push_from_last_history: 0,
            push_count: 0,
            pop_count: 0,
        }
    }

    pub fn record_real_pop(&mut self) {
        self.stack_position -= 1;
        if self.stack_position < 0 {
            self.stack_depth = cmp::max(self.stack_depth, -self.stack_position as u32);
        }
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
            blocks: vec![BasicBlock::new(BlockId(0), vec![])],
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

    pub fn value_numbering_core<Fallback>(
        &mut self,
        instr: (OptOp<ValueId>, SmallVec<[ValueId; 4]>),
        fallback: Fallback,
    ) -> ValueId
    where
        Fallback: FnOnce(&mut Self, OptOp<ValueId>, &[ValueId]) -> ValueId,
    {
        if let Some(vals) = self.value_index.get(&instr) {
            for (val, instr) in vals {
                if instr.block_id() == self.current_block
                    || instr.block_id().0 == 0
                    || self.current_block_ref().predecessors.contains(&instr.block_id())
                {
                    return *val;
                }
            }
        }

        let val = fallback(self, instr.0.clone(), &instr.1);
        if let Some(constant) = self.values.get(&val).and_then(|info: &ValueInfo| info.as_constant()) {
            // maybe remove the value
            if !self.stack.lookup.contains_key(&val) {
                self.stack.poped_values.push(val);
            }

            return self.store_constant(constant);
        }

        let defined_at = self.values[&val].assigned_at.expect("value_numbering failed: assignment instruction not recorded");
        self.value_index.entry(instr).or_insert_with(Vec::new).push((val, defined_at));
        val
    }

    pub fn value_numbering<FVal: FnOnce(&mut ValueInfo) -> (), FInstr: FnOnce(&mut OptInstr) -> ()>(
        &mut self,
        op: OptOp<ValueId>,
        args: Vec<ValueId>,
        val_settings: FVal,
        instr_settings: FInstr,
    ) -> ValueId {
        self.value_numbering_core((op, args.into()), |this, op, args| {
            let val = this.new_value();
            val_settings(val);
            let val_id = val.id;
            let i = this.push_instr(op, args, val_id);
            instr_settings(i);
            val_id
        })
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
        // self.value_numbering_core((OptOp::Const(value), vec![]), |this, op, _| {
        //     // add to block 0, so it can be reused anywhere
        //     let assigned_at = InstrId(BlockId(0), this.blocks[0].next_instr_id);
        //     let reg = this.new_value(|r| {
        //         r.range = value..=value;
        //         r.assigned_at = assigned_at;
        //     });
        //     let instr = OptInstr { op, inputs: vec![], out: reg, stack_state: None, program_position: usize::MAX };
        //     this.blocks[0].add_instruction(instr);
        //     reg
        // })
    }

    fn mark_used_at(&mut self, val: ValueId, instr: InstrId) {
        if val.is_constant() || val.is_null() {
            return;
        }

        if let Some(info) = self.values.get_mut(&val) {
            info.used_at.insert(instr);
        }
    }

    pub fn push_instr(&mut self, op: OptOp<ValueId>, args: &[ValueId], out: ValueId) -> &mut OptInstr {
        assert!(!out.is_constant(), "Cannot assign to constant: {:?} <- {:?}{:?}", out, op, args);
        assert!(!args.contains(&ValueId(0)), "Cannot use null ValueId: {:?} <- {:?}{:?}", out, op, args);
        let effect = op.worst_case_effect();
        let instr = OptInstr {
            id: InstrId(self.current_block, self.current_block_ref().next_instr_id),
            op, inputs: args.into(), out,
            stack_state: None,
            program_position: self.assumed_program_position.unwrap_or(usize::MAX),
            effect
        };

        if !out.is_null() {
            let Some(val_info) = self.values.get_mut(&out) else {
                panic!("Out Value not registered: {:?} <- {:?}{:?}", out, instr.op, instr.inputs);
            };
            assert!(val_info.assigned_at.is_none() || val_info.assigned_at == Some(instr.id));
            val_info.assigned_at = Some(instr.id);
        }

        for arg in instr.iter_inputs() {
            self.mark_used_at(arg, instr.id);
        }

        self.current_block_mut().add_instruction(instr)
    }

    pub fn push_instr_may_deopt(&mut self, op: OptOp<ValueId>, args: &[ValueId], out: ValueId) -> &mut OptInstr {
        let stack_state = self.stack.save_history();
        let instr = self.push_instr(op, args, out);
        instr.stack_state = Some(stack_state);
        instr
    }

    pub fn push_assert(&mut self, c: Condition<ValueId>, error: OperationError, val: Option<ValueId>) {
        self.push_instr(OptOp::Assert(c, error, val), &[], ValueId(0));
    }

    pub fn push_deopt_assert(&mut self, c: Condition<ValueId>, precise_deoptinfo: bool) {
        if precise_deoptinfo {
            self.push_instr_may_deopt(OptOp::DeoptAssert(c), &[], ValueId(0));
        } else {
            self.push_instr(OptOp::DeoptAssert(c), &[], ValueId(0));
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
                let reg = self.new_value().id;
                self.push_instr(OptOp::Pop, &[], reg);
                reg
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
        for (i, val) in self.stack.stack.iter().rev().enumerate() {
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
                    todo!("should not happen?")
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

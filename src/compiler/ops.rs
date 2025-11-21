use std::{cmp, collections::BTreeSet, fmt::{self, Debug, Display}, num::NonZeroI32, ops::{Range, RangeInclusive}};

use num_integer::Integer;
use smallvec::{SmallVec, ToSmallVec};

use crate::{compiler::{osmibytecode::Condition, range_ops::{eval_combi, range_and, range_div, range_mod, range_mod_euclid, range_num_digits, range_or, range_xor}, utils::{FULL_RANGE, abs_range, add_range, intersect_range, mul_range, range_2_i64, sub_range, union_range}}, digit_sum, funkcia, vm::{self, OperationError, median}};


#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(pub i32);
impl ValueId {
    pub const PREDEF_RANGE: i32 = 4096;
    pub const C_NEG_ONE: ValueId = Self::from_predefined_const(-1).unwrap();
    pub const C_NEG_TWO: ValueId = Self::from_predefined_const(-2).unwrap();
    pub const C_ZERO: ValueId = Self::from_predefined_const(0).unwrap();
    pub const C_ONE: ValueId = Self::from_predefined_const(1).unwrap();
    pub const C_TWO: ValueId = Self::from_predefined_const(2).unwrap();
    pub const C_THREE: ValueId = Self::from_predefined_const(3).unwrap();
    pub const C_FOUR: ValueId = Self::from_predefined_const(4).unwrap();
    pub const C_FIVE: ValueId = Self::from_predefined_const(5).unwrap();
    pub const C_SIX: ValueId = Self::from_predefined_const(6).unwrap();
    pub const C_SEVEN: ValueId = Self::from_predefined_const(7).unwrap();
    pub const C_IMIN: ValueId = Self::from_predefined_const(i64::MIN).unwrap();
    pub const C_IMAX: ValueId = Self::from_predefined_const(i64::MAX).unwrap();
    pub const fn is_null(&self) -> bool {
        self.0 == 0
    }
    pub const fn is_new_value_placeholder(&self) -> bool {
        self.0 == i32::MAX
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
        } else if self.is_new_value_placeholder() {
            write!(f, "vNEW")
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct BlockId(pub u32);
impl BlockId {
    pub const UNDEFINED: BlockId = BlockId(u32::MAX);
    pub fn is_undefined(&self) -> bool { self.0 == u32::MAX }
    pub fn is_first_block(&self) -> bool { self.0 == 0 }
}
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
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct InstrId(pub BlockId, pub u32);
impl InstrId {
    pub const UNDEFINED: InstrId = InstrId(BlockId::UNDEFINED, u32::MAX);
    pub fn block_id(self) -> BlockId { self.0 }
    pub fn instr_ix(self) -> u32 {
        self.1
    }
    pub fn is_block_head(self) -> bool {
        self.1 == 0
    }
}
impl fmt::Display for InstrId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 == u32::MAX {
            write!(f, "i{}_END", self.0.0)
        } else {
            write!(f, "i{}_{}", self.0.0, self.1)
        }
    }
}
impl fmt::Debug for InstrId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
impl Into<(u32, u32)> for InstrId {
    fn into(self) -> (u32, u32) { (self.0 .0, self.1) }
}
impl Into<u64> for InstrId {
    fn into(self) -> u64 { ((self.0 .0 as u64) << 32) | (self.1 as u64) }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeforeOrAfter<T> {
    Before(T),
    After(T),
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
    ModEuclid,     // a % b (always non-negative)
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

    Select(Condition<TVal>), // a <- b ? c : d

    DigitSum, // a <- digit_sum(b)
    Gcd,      // a <- gcd(b, c)

    StackSwap, // a <- stack[b]; stack[b] <- c; if index out of range, deopt
    StackRead, // a <- stack[b];                if index out of range, deopt

    Const(i64),

    Checkpoint, // checkpoint for deoptimization - stores stack state in inputs (stack_depth, ... stack values)

    Jump(Condition<TVal>, BlockId), // if true: jump to BB. `inputs` are parameters for the target BB

    Assert(Condition<TVal>, OperationError), // error, optional argument
    DeoptAssert(Condition<TVal>), // if false: abort block execution, IP where we continue
    // Done(u32), // instruction pointer where to continue execution
    Median,
    MedianCursed, // _ <- median(N, a, b, c, ...)

    KsplangOpsIncrement(Condition<TVal>) // if true: CTR += a + b + c + ...
}

impl<TVal: Clone + PartialEq + Eq + Display + Debug> OptOp<TVal> {
    pub fn is_terminal(&self) -> bool {
        matches!(self, OptOp::Jump(Condition::True, _) | OptOp::DeoptAssert(Condition::False) | OptOp::Assert(Condition::False, _))
    }

    pub fn condition(&self) -> Option<Condition<TVal>> {
        match self {
            OptOp::Select(cond) => Some(cond.clone()),
            OptOp::Jump(cond, _) => Some(cond.clone()),
            OptOp::Assert(cond, _) => Some(cond.clone()),
            OptOp::DeoptAssert(cond) => Some(cond.clone()),
            OptOp::KsplangOpsIncrement(cond) => Some(cond.clone()),
            _ => None,
        }
    }

    pub fn condition_mut(&mut self) -> Option<&mut Condition<TVal>> {
        match self {
            OptOp::Select(cond) => Some(cond),
            OptOp::Jump(cond, _) => Some(cond),
            OptOp::Assert(cond, _) => Some(cond),
            OptOp::DeoptAssert(cond) => Some(cond),
            OptOp::KsplangOpsIncrement(cond) => Some(cond),
            _ => None,
        }
    }

    pub fn deopt_always() -> Self {
        OptOp::DeoptAssert(Condition::False)
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
            OptOp::Push | OptOp::Pop => OpEffect::StackWrite,
            OptOp::Nop | OptOp::Const(_) | OptOp::Select(_) | OptOp::DigitSum | OptOp::Gcd | OptOp::Median | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::ShiftR | OptOp::BinNot | OptOp::BoolNot | OptOp::Funkcia | OptOp::LenSum | OptOp::Min | OptOp::Max | OptOp::Sgn | OptOp::Checkpoint => OpEffect::None,
            OptOp::KsplangOpsIncrement(_) => OpEffect::CtrIncrement,

            // overflow checks, div by zero
            OptOp::Add | OptOp::Sub | OptOp::AbsSub | OptOp::Mul | OptOp::Div | OptOp::CursedDiv | OptOp::Mod | OptOp::ModEuclid | OptOp::Tetration | OptOp::ShiftL | OptOp::AbsFactorial =>
                OpEffect::MayFail,

            OptOp::Assert(_, _) => OpEffect::MayFail,

            OptOp::Jump(_, _) => OpEffect::ControlFlow,
            OptOp::DeoptAssert(_) | OptOp::Universal | OptOp::MedianCursed => OpEffect::MayDeopt,
            OptOp::StackSwap => OpEffect::StackWrite,
            OptOp::StackRead => OpEffect::StackRead,
        }
    }

    pub fn arity(&self) -> RangeInclusive<usize> {
        match self {
            OptOp::Pop | OptOp::Nop => 0..=0,
            OptOp::Push => 1..=usize::MAX,
            OptOp::Add | OptOp::Mul | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Gcd | OptOp::Max | OptOp::Min => 1..=usize::MAX,
            OptOp::LenSum => 1..=2,
            OptOp::AbsSub | OptOp::Sub | OptOp::Div | OptOp::CursedDiv | OptOp::Mod | OptOp::ModEuclid => 2..=2,
            OptOp::Tetration => 2..=2,
            OptOp::Funkcia => 2..=2,
            OptOp::Sgn | OptOp::AbsFactorial | OptOp::BinNot | OptOp::BoolNot | OptOp::DigitSum => 1..=1,
            OptOp::Select(_) => 2..=2,
            OptOp::Const(_) => 0..=0,
            OptOp::Checkpoint => 1..=usize::MAX, // first arg is stack depth, rest are stack values
            OptOp::Jump(_, _) => 0..=usize::MAX,
            OptOp::Assert(_, _) => 0..=1,
            OptOp::DeoptAssert(_) => 0..=0,
            OptOp::MedianCursed | OptOp::Median => 1..=usize::MAX,
            OptOp::ShiftL | OptOp::ShiftR => 2..=2,
            OptOp::StackSwap => 2..=2,
            OptOp::StackRead => 1..=1,
            OptOp::Universal => 2..=3,
            OptOp::KsplangOpsIncrement(_) => 1..=usize::MAX,
        }
    }

    pub fn has_output(&self) -> bool {
        !matches!(self, OptOp::Push | OptOp::Nop | OptOp::Checkpoint | OptOp::Jump(_, _) | OptOp::Assert(_, _) | OptOp::DeoptAssert(_) | OptOp::KsplangOpsIncrement(_))
    }

    pub fn discriminant(&self) -> usize {
        match self {
            OptOp::Push => 1,
            OptOp::Pop => 2,
            OptOp::Nop => 3,
            OptOp::Add => 4,
            OptOp::Sub => 5,
            OptOp::AbsSub => 6,
            OptOp::Mul => 7,
            OptOp::Div => 8,
            OptOp::CursedDiv => 9,
            OptOp::Mod => 10,
            OptOp::ModEuclid => 11,
            OptOp::Tetration => 12,
            OptOp::Funkcia => 13,
            OptOp::LenSum => 14,
            OptOp::Max => 15,
            OptOp::Min => 16,
            OptOp::Sgn => 17,
            OptOp::AbsFactorial => 18,
            OptOp::Universal => 19,
            OptOp::And => 20,
            OptOp::Or => 21,
            OptOp::Xor => 22,
            OptOp::ShiftL => 23,
            OptOp::ShiftR => 24,
            OptOp::BinNot => 25,
            OptOp::BoolNot => 26,
            OptOp::Select(condition) => 28 << 16 | condition.discriminant(),
            OptOp::DigitSum => 29,
            OptOp::Gcd => 30,
            OptOp::StackSwap => 31,
            OptOp::StackRead => 39,
            OptOp::Const(_) => 32,
            OptOp::Checkpoint => 38,
            OptOp::Jump(condition, block_id) => 33 << 48 | (condition.discriminant() as usize) << 32 | (block_id.0 as usize),
            OptOp::Assert(condition, _) => 34 << 32 | (condition.discriminant() as usize) << 16,
            OptOp::DeoptAssert(condition) => 35 << 16 | condition.discriminant(),
            OptOp::Median => 36,
            OptOp::MedianCursed => 37,
            OptOp::KsplangOpsIncrement(condition) => 40 << 16 | condition.discriminant(),
        }
    }

    pub fn evaluate(&self, inputs: &[i64]) -> Result<i64, Option<OperationError>> {
        let cond_count = self.condition().map(|c| c.regs().len()).unwrap_or(0);
        debug_assert!(self.arity().contains(&(inputs.len() - cond_count)), "Invalid number of inputs for {:?}: {}", self, inputs.len());
        match self {
            OptOp::Push | OptOp::Pop | OptOp::Nop | OptOp::Checkpoint | OptOp::KsplangOpsIncrement(_) => Err(None),
            OptOp::Add => inputs.iter().try_fold(0i64, |a, b| a.checked_add(*b)).ok_or(Some(OperationError::IntegerOverflow)),
            OptOp::Sub => {
                        assert_eq!(inputs.len(), 2);
                        inputs[0].checked_sub(inputs[1]).ok_or(Some(OperationError::IntegerOverflow))
                    }
            OptOp::AbsSub => {
                        assert_eq!(inputs.len(), 2);
                        let a = inputs[0];
                        let b = inputs[1];
                        if a >= b {
                            a.checked_sub(b).ok_or(Some(OperationError::IntegerOverflow))
                        } else {
                            b.checked_sub(a).ok_or(Some(OperationError::IntegerOverflow))
                        }
                    }
            OptOp::Mul => inputs.iter().try_fold(1i64, |a, b| a.checked_mul(*b)).ok_or(Some(OperationError::IntegerOverflow)),
            OptOp::Div => {
                        let a = inputs[0];
                        let b = inputs[1];
                        a.checked_div(b).ok_or(Some(if b == 0 { OperationError::DivisionByZero } else { OperationError::IntegerOverflow }))
                    }
            OptOp::CursedDiv => {
                        let a = inputs[0];
                        let b = inputs[1];
                        if b == 0 {
                            Err(Some(OperationError::DivisionByZero))
                        } else if a % b == 0 {
                            a.checked_div(b).ok_or(Some(OperationError::IntegerOverflow))
                        } else {
                            a.checked_rem(b).ok_or(Some(OperationError::IntegerOverflow))
                        }
                    }
            OptOp::Mod => inputs[0].checked_rem(inputs[1]).ok_or(Some(OperationError::DivisionByZero)),
            OptOp::ModEuclid => inputs[0].checked_rem_euclid(inputs[1]).ok_or(Some(OperationError::DivisionByZero)),
            OptOp::Tetration => Ok(vm::tetration(inputs[0], inputs[1])?),
            OptOp::Funkcia => Ok(funkcia::funkcia(inputs[0], inputs[1]) as i64),
            OptOp::LenSum => Ok(inputs.iter().map(|x| vm::decimal_len(*x)).sum()),
            OptOp::Max => inputs.iter().copied().max().ok_or(None),
            OptOp::Min => inputs.iter().copied().min().ok_or(None),
            OptOp::Sgn => Ok(inputs[0].signum()),
            OptOp::AbsFactorial => Ok(vm::abs_factorial(inputs[0])?),
            OptOp::Universal => todo!(),
            OptOp::And => Ok(inputs.iter().fold(!0i64, |a, b| a & *b)),
            OptOp::Or => Ok(inputs.iter().fold(0i64, |a, b| a | *b)),
            OptOp::Xor => Ok(inputs.iter().fold(0i64, |a, b| a ^ *b)),
            OptOp::ShiftL | OptOp::ShiftR => if inputs[1] < 0 {
                Err(Some(OperationError::NegativeBitCount { bits: inputs[1] }))
            } else if inputs[1] >= 64 {
                Ok(0)
            } else {
                Ok(if matches!(self, OptOp::ShiftL) { inputs[0] << inputs[1] } else { inputs[0] >> inputs[1] })
            },
            OptOp::BinNot => Ok(!inputs[0]),
            OptOp::BoolNot => Ok(if inputs[0] == 0 { 1 } else { 0 }),
            OptOp::Select(condition) => Ok(if condition.eval(&inputs[0..inputs.len()-2]) { inputs[inputs.len()-2] } else { inputs[inputs.len()-1] }),
            OptOp::DigitSum => Ok(digit_sum::digit_sum(inputs[0])),
            OptOp::Gcd => inputs.iter().map(|x| x.abs_diff(0)).reduce(|a, b| a.gcd(&b)).unwrap().try_into().map_err(|_| Some(OperationError::IntegerOverflow)),
            OptOp::StackSwap => Err(None),
            OptOp::StackRead => Err(None),
            OptOp::Const(x) => Ok(*x),
            OptOp::Median => {
                let mut vals: SmallVec<[i64; 5]> = inputs.to_smallvec();
                Ok(vm::median(&mut vals))
            },
            OptOp::MedianCursed => {
                let n = inputs[0];
                if n <= 0 { return Err(Some(OperationError::NonpositiveLength { value: n })) }
                if n > inputs.len() as i64 { return Err(None) }
                let mut vals: SmallVec<[i64; 5]> = inputs[..(n as usize)].to_smallvec();
                Ok(vm::median(&mut vals))
            },
            OptOp::Jump(condition, _) => if condition.eval(inputs) { Err(None) } else { Ok(0) },
            OptOp::Assert(condition, operation_error) => if condition.eval(inputs) {
                Ok(0)
            } else {
                Err(Some(if inputs.len() > cond_count {
                    operation_error.with_value(inputs[condition.regs().len()])
                } else {
                    operation_error.clone()
                }))
            },
            OptOp::DeoptAssert(condition) => if condition.eval(inputs) {
                Ok(0)
            } else {
                Err(None)
            },
        }
    }

    pub fn evaluate_range_quick(&self, inputs: &[RangeInclusive<i64>]) -> Option<RangeInclusive<i64>> {
        debug_assert!(self.arity().contains(&inputs.len()), "Invalid number of inputs for {:?}: {}", self, inputs.len());

        match self {
            OptOp::Push | OptOp::Pop | OptOp::Nop | OptOp::Checkpoint | OptOp::Jump(_, _) | OptOp::Assert(_, _) | OptOp::DeoptAssert(_) | OptOp::StackSwap | OptOp::StackRead | OptOp::Universal | OptOp::KsplangOpsIncrement(_) => None,
            OptOp::Const(c) => Some(*c..=*c),
            OptOp::Add => inputs.iter().cloned().reduce(|a, b| add_range(&a, &b)),
            OptOp::Mul => inputs.iter().cloned().reduce(|a, b| mul_range(&a, &b).0),
            OptOp::Sub => Some(sub_range(&inputs[0], &inputs[1])),
            OptOp::AbsSub => {
                let (a, b) = (&inputs[0], &inputs[1]);
                Some(range_2_i64(intersect_range(&abs_range(sub_range(a, b)), &abs_range(sub_range(b, a)))))
            },
            OptOp::Div => Some(range_div(&inputs[0], &inputs[1])),
            OptOp::CursedDiv => Some(union_range(range_div(&inputs[0], &inputs[1]), range_mod(inputs[0].clone(), inputs[1].clone()))),
            OptOp::Mod => Some(range_mod(inputs[0].clone(), inputs[1].clone())),
            OptOp::ModEuclid => Some(range_mod_euclid(inputs[0].clone(), inputs[1].clone())),
            OptOp::Tetration => eval_combi(inputs[0].clone(), inputs[1].clone(), 16, |a, b| vm::tetration(a, b).ok()), // TODO: smarter heuristic?
            OptOp::Funkcia => Some(0..=cmp::min(1_000_000_007 - 1, inputs[0].end().saturating_mul(*inputs[1].end()))),
            OptOp::LenSum => Some(add_range(&range_num_digits(&inputs[0]), &range_num_digits(&inputs[1]))),
            OptOp::Max => Some(inputs.iter().map(|r| *r.start()).max().unwrap()..=inputs.iter().map(|r| *r.end()).max().unwrap()),
            OptOp::Min => Some(inputs.iter().map(|r| *r.start()).min().unwrap()..=inputs.iter().map(|r| *r.end()).min().unwrap()),
            OptOp::Sgn => Some(inputs[0].start().signum()..=inputs[0].end().signum()),
            OptOp::AbsFactorial => {
                let (start, end) = abs_range(inputs[0].clone()).into_inner();
                if start > 20 {
                    Some(1..=0)
                } else {
                    Some(vm::abs_factorial(cmp::min(start , 20) as i64).unwrap()..=vm::abs_factorial(cmp::min(end, 20) as i64).unwrap())
                }
            },
            OptOp::And => inputs.iter().cloned().reduce(range_and),
            OptOp::Or => inputs.iter().cloned().reduce(range_or),
            OptOp::Xor => inputs.iter().cloned().reduce(range_xor),
            OptOp::ShiftL => {
                let can_overflow = inputs[0].end().leading_zeros() as i64 <= *inputs[1].end();
                if *inputs[1].end() < 0 {
                    None // always error
                } else if can_overflow {
                    None
                } else {
                    assert!(*inputs[1].end() < 64);
                    assert!(*inputs[1].start() < 64);
                    Some((inputs[0].start() << inputs[1].start().max(&0))..=(inputs[0].end() << inputs[1].end()))
                }
            }
            OptOp::ShiftR => None, // TODO
            OptOp::BinNot => Some(0..=1), // TODO
            OptOp::BoolNot => if *inputs[0].start() > 0 || *inputs[0].end() < 0 {
                Some(0..=0)
            } else if *inputs[0].start() == 0 && *inputs[0].end() == 0 {
                Some(1..=1)
            } else {
                Some(0..=1)
            },
            OptOp::DigitSum => Some(digit_sum::digit_sum_range(inputs[0].clone())),
            OptOp::Gcd => {
                let ranges = inputs.iter().map(|v| abs_range(v.clone()));
                let min_end = ranges.clone().map(|r| *r.end()).min().unwrap();
                let all_zeros = ranges.clone().all(|r| *r.start() == 0);

                Some(range_2_i64(if all_zeros { 0 } else { 1 }..=min_end))
            },
            OptOp::Median => {
                let mut starts: Vec<i64> = inputs.iter().map(|r| *r.start()).collect();
                let mut ends: Vec<i64> = inputs.iter().map(|r| *r.end()).collect();
                let med_start = median(&mut starts[..]);
                let med_end = median(&mut ends[..]);
                Some(med_start..=med_end)
            },
            OptOp::MedianCursed => {
                let mut starts: Vec<i64> = inputs.iter().map(|r| *r.start()).collect();
                let mut ends: Vec<i64> = inputs.iter().map(|r| *r.end()).collect();

                let mut min_start = i64::MAX;
                let mut max_start = i64::MIN;
                for i in intersect_range(&inputs[0], &(1..=inputs.len() as i64)) {
                    let med_start = median(&mut starts[..i as usize]);
                    let med_end = median(&mut ends[..i as usize]);
                    min_start = cmp::min(min_start, med_start);
                    max_start = cmp::max(max_start, med_end);
                }
                Some(min_start..=max_start)
            },
            OptOp::Select(_) => inputs.iter().cloned().reduce(union_range),
        }
    }

    pub fn effect_based_on_ranges(&self, inputs: &[RangeInclusive<i64>]) -> OpEffect {
        debug_assert!(self.arity().contains(&inputs.len()), "Invalid number of inputs for {:?}: {}", self, inputs.len());

        match self {
            OptOp::Add =>
                if inputs.iter().map(|r| *r.end()).try_fold(0i64, |a, b| a.checked_add(b)).is_some() &&
                    inputs.iter().map(|r| *r.start()).try_fold(0i64, |a, b| a.checked_add(b)).is_some() {
                    OpEffect::None
                } else {
                    OpEffect::MayFail
                },
            OptOp::Mul => {
                let mut acc = inputs[0].clone();
                for r in &inputs[1..] {
                    let (new_acc, overflowed) = mul_range(&acc, r);
                    if overflowed {
                        return OpEffect::MayFail
                    }
                    acc = new_acc;
                }
                OpEffect::None
            },
            OptOp::Sub => {
                let (start_a, end_a) = inputs[0].clone().into_inner();
                let (start_b, end_b) = inputs[1].clone().into_inner();
                if end_a.checked_sub(start_b).is_some() && start_a.checked_sub(end_b).is_some() {
                    OpEffect::None
                } else {
                    OpEffect::MayFail
                }
            },
            OptOp::AbsSub => {
                let (start_a, end_a) = inputs[0].clone().into_inner();
                let (start_b, end_b) = inputs[1].clone().into_inner();
                if cmp::max(end_a, end_b).abs_diff(cmp::min(start_a, start_b)) <= i64::MAX as u64 {
                    OpEffect::None
                } else {
                    OpEffect::MayFail
                }
            },
            OptOp::Div | &OptOp::CursedDiv =>
                if inputs[1].contains(&0) {
                    OpEffect::MayFail
                } else if inputs[0].contains(&i64::MIN) && inputs[1].contains(&-1) {
                    OpEffect::MayFail
                } else {
                    OpEffect::None
                },
            OptOp::ModEuclid | OptOp::Mod =>
                if inputs[1].contains(&0) {
                    OpEffect::MayFail
                } else {
                    OpEffect::None
                },
            OptOp::Tetration => OpEffect::MayFail, // TODO
            OptOp::AbsFactorial =>
                if *abs_range(inputs[0].clone()).end() <= 20 {
                    OpEffect::None
                } else {
                    OpEffect::MayFail
                },
            OptOp::Gcd =>
                if inputs.iter().all(|r| *r.start() == i64::MIN) {
                    OpEffect::MayFail
                } else {
                    OpEffect::None
                },
            _ => self.worst_case_effect() // do not depend on ranges
        }
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpEffect {
    None,
    MayFail,
    MayDeopt,
    ControlFlow,
    /// Reads the stack without any modification (pop and push both use StackWrite)
    StackRead,
    StackWrite,
    CtrIncrement,
}

impl OpEffect {
    pub fn only_if(&mut self, condition: bool) {
        if condition { *self = OpEffect::None }
    }

    pub fn allows_value_numbering(&self) -> bool {
        !matches!(self, OpEffect::StackRead | OpEffect::StackWrite | OpEffect::ControlFlow | OpEffect::CtrIncrement)
    }

    pub fn better_of(a: OpEffect, b: OpEffect) -> OpEffect {
        use OpEffect::*;
        match (a, b) {
            (None, _) | (_, None) => None,
            (MayFail, _) | (_, MayFail) => MayFail,
            (MayDeopt, _) | (_, MayDeopt) => MayDeopt,
            (ControlFlow, _) | (_, ControlFlow) => ControlFlow,
            (CtrIncrement, _) | (_, CtrIncrement) => CtrIncrement,
            (StackRead, _) | (_, StackRead) => StackRead,
            (StackWrite, StackWrite) => StackWrite,
        }
    }
    pub fn worse_of(a: OpEffect, b: OpEffect) -> OpEffect {
        use OpEffect::*;
        match (a, b) {
            (StackWrite, _) | (_, StackWrite) => StackWrite,
            (StackRead, _) | (_, StackRead) => StackRead,
            (CtrIncrement, _) | (_, CtrIncrement) => CtrIncrement,
            (ControlFlow, _) | (_, ControlFlow) => ControlFlow,
            (MayDeopt, _) | (_, MayDeopt) => MayDeopt,
            (MayFail, _) | (_, MayFail) => MayFail,
            (None, None) => None
        }
    }

    pub fn char(&self) -> char {
        match self {
            OpEffect::None => ' ',
            OpEffect::MayFail => '.',
            OpEffect::MayDeopt => 'd',
            OpEffect::ControlFlow => 'C',
            OpEffect::StackRead => 'r',
            OpEffect::StackWrite => 'W',
            OpEffect::CtrIncrement => 'i',
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptInstr {
    pub id: InstrId,
    pub op: OptOp<ValueId>,
    pub inputs: SmallVec<[ValueId; 4]>,
    pub out: ValueId,
    pub program_position: usize, // u64::MAX if unknown
    pub ksp_instr_count: u32,
    pub effect: OpEffect,
}

impl OptInstr {
    pub fn new(id: InstrId, op: OptOp<ValueId>, inputs: &[ValueId], out: ValueId) -> Self {
        let effect = op.worst_case_effect();
        Self {
            id,
            op,
            inputs: inputs.to_smallvec(),
            out,
            program_position: usize::MAX,
            ksp_instr_count: 0,
            effect,
        }
    }
    pub fn validate(&self) {
        assert!(!self.out.is_constant(), "Cannot assign to constant: {}", self);
        assert!(!self.inputs.contains(&ValueId(0)), "Cannot use null ValueId: {}", self);
        assert!(self.op.arity().contains(&self.inputs.len()), "Invalid op artity: {} {:?} {}", self, self.op.arity(), self.inputs.len());
        assert_ne!(0, self.id.1, "0 is reserved for block head");
    }
    pub fn assert(condition: Condition<ValueId>, error: OperationError, value: Option<ValueId>) -> Self {
        Self::new(InstrId::UNDEFINED, OptOp::Assert(condition, error), value.as_slice(), ValueId::from(0))
    }
    pub fn deopt(condition: Condition<ValueId>) -> Self {
        Self::new(InstrId::UNDEFINED, OptOp::DeoptAssert(condition), &[], ValueId::from(0))
    }
    pub fn with_effect(mut self, effect: OpEffect) -> Self {
        self.effect = effect;
        self
    }
    pub fn with_id(mut self, id: InstrId) -> Self {
        self.id = id;
        self
    }
    pub fn with_position(mut self, pos: usize) -> Self {
        self.program_position = pos;
        self
    }
    pub fn with_op(mut self, op: OptOp<ValueId>, args: &[ValueId], effect: OpEffect) -> Self {
        self.op = op;
        self.inputs = args.to_smallvec();
        self.effect = effect;
        self
    }
    pub fn iter_inputs(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.op.condition().into_iter().flat_map(|cond| cond.regs()).chain(self.inputs.iter().copied())
    }

    pub fn richer_fmt(&self, f: &mut fmt::Formatter<'_>,
                             mut val_range: impl FnMut(ValueId) -> RangeInclusive<i64>)
        -> fmt::Result {

        write!(f, "{: >3} {: >4} | ", self.id.0.0, self.id.1)?;
        if !self.out.is_null() {
            let out = format!("{}", self.out);
            write!(f, "{out:>5} <- ")?;
        } else {
            write!(f, "{:<9}", "")?;
        }
        let mut op_str = format!("{:?}", self.op);
        for arg in &self.inputs {
            if arg.is_constant() && arg.to_predefined_const().is_none() {
                let r = val_range(*arg);
                if r.start() == r.end() {
                    op_str += &format!(" {}", r.start());
                    continue;
                }
            }
            op_str += &format!(" {}", arg);
        }
        write!(f, "{op_str:<40}")?;
        write!(f, ": {}{} ",
            if self.effect != self.op.worst_case_effect() { "*" } else { " " },
            self.effect.char()
        )?;
        if self.program_position != usize::MAX {
            write!(f, "IP={:<10} ", self.program_position)?;
        } else {
            write!(f, "{:<14}", "")?;
        }
        if self.out.is_computed() {
            let out_range = val_range(self.out);
            if out_range != FULL_RANGE {
                if *out_range.start() == i64::MIN {
                    write!(f, " ..={:x}", out_range.end())?;
                } else if *out_range.end() == i64::MAX {
                    write!(f, " {:x}..=", out_range.start())?;
                } else {
                    write!(f, " {:x}..={:x}", out_range.start(), out_range.end())?;
                }
            }
        }
        write!(f, "")
    }
}

impl fmt::Display for OptInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.richer_fmt(f, |_| FULL_RANGE)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValueInfo {
    pub id: ValueId,
    pub directly_derived_from: Option<ValueId>,
    pub assigned_at: Option<InstrId>,
    pub range: RangeInclusive<i64>,
    pub used_at: BTreeSet<InstrId>,
    pub assumptions: Vec<(Condition<ValueId>, i64, i64, InstrId)>,
}

impl ValueInfo {
    pub fn new(id: ValueId) -> Self {
        Self { id, directly_derived_from: None, assigned_at: None, range: i64::MIN..=i64::MAX, used_at: BTreeSet::new(), assumptions: vec![] }
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

    pub fn set_assigned_at(&mut self, id: InstrId, op: &OptOp<ValueId>, inputs: &[ValueId]) {
        self.assigned_at = Some(id);

        if matches!(op, OptOp::Add | OptOp::Sub | OptOp::Mul | OptOp::Div | OptOp::Mod | OptOp::ModEuclid | OptOp::Min | OptOp::Max | OptOp::Select(_) | OptOp::Median | OptOp::ShiftR) &&
            inputs.iter().filter(|v| v.is_computed()).count() == 1
        {   // trackable in derived ranges without exploding recursion
            self.directly_derived_from = inputs.iter().find(|v| v.is_computed()).copied();
        }
    }

    pub fn iter_assumptions<'a>(&'a self, at: InstrId, preds: &'a BTreeSet<BlockId>) -> impl Iterator<Item = &'a (Condition<ValueId>, i64, i64, InstrId)> + 'a {
        self.assumptions.iter().rev()
            .filter(move |(_, _, _, instr)|
                if instr.0 == at.0 { instr.1 < at.1 }
                else {
                    instr.block_id() == BlockId(0) ||
                    preds.contains(&instr.block_id())
                }
            )
    }
}

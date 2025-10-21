use core::fmt;
use std::{collections::{BTreeMap, BTreeSet, HashMap, HashSet}, fmt::Display, mem, u32};
use arrayvec::ArrayVec;
use smallvec::SmallVec;

use crate::compiler::{cfg::{BasicBlock, GraphBuilder}, ops::{BlockId, InstrId, OpEffect, OptOp, ValueId}};


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrecompiledOp<TReg: Display> {
    Push(TReg),
    Push2(TReg, TReg),
    Push3(TReg, TReg, TReg),
    Push4(TReg, TReg, TReg, TReg),
    Pop(TReg),
    Pop2(TReg, TReg),
    Pop3(TReg, TReg, TReg),
    Pop4(TReg, TReg, TReg, TReg),
    PopSecond(TReg), // like pop2 instruction

    Add(TReg, TReg, TReg), // a <- b + c
    AddConst(TReg, TReg, i32), // a <- b + const
    Sub(TReg, TReg, TReg), // a <- b - c
    SubConst(TReg, i32, TReg), // a <- const - c
    AbsSub(TReg, TReg, TReg), // a <- |b - c|
    Mul(TReg, TReg, TReg), // a <- b * c
    MulConst(TReg, TReg, i32), // a <- b * const
    Div(TReg, TReg, TReg), // a <- b / c
    CursedDiv(TReg, TReg, TReg), // a <- b % c if non-zero, otherwise b / c
    Mod(TReg, TReg, TReg), // a <- b % c
    ModEuler(TReg, TReg, TReg), // a <- b mod c (always non-negative)
    Tetration(TReg, TReg, TReg), // a <- b tetrated c times
    Funkcia(TReg, TReg, TReg), // a <- funkcia(b, c)
    Max(TReg, TReg, TReg), // a <- max(b, c)
    Min(TReg, TReg, TReg), // a <- min(b, c)
    Clamp(TReg, TReg, TReg, TReg), // a <- min(max(a, b), c)
    Sgn(TReg, TReg), // a <- sgn(b)
    AbsFactorial(TReg, TReg), // a <- |b|!
    Universal2(TReg, TReg, TReg, TReg), // a <- universal[b](c, d) (or deopt if universal1 should be used instead)
    Universal1(TReg, TReg, TReg), // a <- universal[b](c) (or deopt if universal2 should be used instead)
    And(TReg, TReg, TReg), // a <- b & c
    Or(TReg, TReg, TReg), // a <- b | c
    Xor(TReg, TReg, TReg), // a <- b ^ c
    ShiftL(TReg, TReg, TReg), // a <- b << c
    ShiftR(TReg, TReg, TReg), // a <- b >> c
    ShiftConst(TReg, TReg, i8), // a <- b << const OR b >> const (based on sign)

    BinNot(TReg, TReg), // a <- ~b
    BoolNot(TReg, TReg), // a <- !b
    Condition(TReg, Condition<TReg>), // a <- condition ? 1 : 0

    Select(TReg, Condition<TReg>, TReg, TReg), // a <- b ? c : d

    DigitSum(TReg, TReg), // a <- digit_sum(b)
    DigitSumSmall(TReg, TReg), // a <- digit_sum(b); if b > 10_000, deopt
    DigitSumTwice(TReg, TReg), // a <- digit_sum(digit_sum(b))
    DigitSumDigitSumLensum(TReg, TReg), // a <- lensum(digit_sum(digit_sum(b)), digit_sum(b))
    Gcd(TReg, TReg, TReg), // a <- gcd(b, c)

    StackSwap(TReg, TReg, TReg, u8), // a <- stack[b]; stack[b] <- c; if b + d >= stack_size, deopt
    StackRead(TReg, TReg, u8),       // a <- stack[b];                if b + c >= stack_size, deopt

    LoadConst(TReg, i32),
    LoadConst64(TReg, u16),

    Jump(Condition<TReg>, u16), // if true: jump to instruction (in this precompiled block)

    Assert(Condition<TReg>, u16), // error code
    DeoptAssert(Condition<TReg>, u16), // if false: abort block execution, deopt info number
    Done(u32), // instruction pointer where to continue execution
    Median2(TReg, TReg, TReg), // a <- median(b, c)
    MedianCursed2(TReg, TReg), // a <- median(b, 2)
    Median3(TReg, TReg, TReg, TReg), // a <- median(b, c, d)
    MedianCursed3(TReg, TReg, TReg), // a <- median(b, c, 3)
    MedianCursed5(TReg, TReg, TReg, TReg, TReg), // a <- median(b, c, d, e, 5)
    KsplangOp(crate::ops::Op),
    KsplangOpWithArg(crate::ops::Op, TReg),

    Spill(u32, TReg), // somewhere[ix] <- a move to a larger register file, should not really happen but easier to implement this than a proper register allocator...
    Unspill(u32, TReg), // a <- somewhere[ix]
}

impl<TReg: Display> PrecompiledOp<TReg> {
    pub fn replace_regs<TReg2: Display, F>(&self, f: F) -> PrecompiledOp<TReg2>
        where F: Fn(&TReg, bool) -> TReg2
    {
        match self {
            PrecompiledOp::Push(a) => PrecompiledOp::Push(f(a, false)),
            PrecompiledOp::Push2(a, b) => PrecompiledOp::Push2(f(a, false), f(b, false)),
            PrecompiledOp::Push3(a, b, c) => PrecompiledOp::Push3(f(a, false), f(b, false), f(c, false)),
            PrecompiledOp::Push4(a, b, c, d) => PrecompiledOp::Push4(f(a, false), f(b, false), f(c, false), f(d, false)),

            PrecompiledOp::Pop(a) => PrecompiledOp::Pop(f(a, true)),
            PrecompiledOp::Pop2(a, b) => PrecompiledOp::Pop2(f(a, true), f(b, true)),
            PrecompiledOp::Pop3(a, b, c) => PrecompiledOp::Pop3(f(a, true), f(b, true), f(c, true)),
            PrecompiledOp::Pop4(a, b, c, d) => PrecompiledOp::Pop4(f(a, true), f(b, true), f(c, true), f(d, true)),
            PrecompiledOp::PopSecond(a) => PrecompiledOp::PopSecond(f(a, true)),

            PrecompiledOp::Add(a, b, c) => PrecompiledOp::Add(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::AddConst(a, b, c) => PrecompiledOp::AddConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Sub(a, b, c) => PrecompiledOp::Sub(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::SubConst(a, b, c) => PrecompiledOp::SubConst(f(a, true), *b, f(c, false)),
            PrecompiledOp::AbsSub(a, b, c) => PrecompiledOp::AbsSub(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Mul(a, b, c) => PrecompiledOp::Mul(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MulConst(a, b, c) => PrecompiledOp::MulConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Div(a, b, c) => PrecompiledOp::Div(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::CursedDiv(a, b, c) => PrecompiledOp::CursedDiv(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Mod(a, b, c) => PrecompiledOp::Mod(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ModEuler(a, b, c) => PrecompiledOp::ModEuler(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Tetration(a, b, c) => PrecompiledOp::Tetration(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Funkcia(a, b, c) => PrecompiledOp::Funkcia(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Max(a, b, c) => PrecompiledOp::Max(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Min(a, b, c) => PrecompiledOp::Min(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Clamp(a, b, c, d) => PrecompiledOp::Clamp(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::Sgn(a, b) => PrecompiledOp::Sgn(f(a, true), f(b, false)),
            PrecompiledOp::AbsFactorial(a, b) => PrecompiledOp::AbsFactorial(f(a, true), f(b, false)),
            PrecompiledOp::Universal2(a, b, c, d) => PrecompiledOp::Universal2(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::Universal1(a, b, c) => PrecompiledOp::Universal1(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::And(a, b, c) => PrecompiledOp::And(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Or(a, b, c) => PrecompiledOp::Or(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Xor(a, b, c) => PrecompiledOp::Xor(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ShiftL(a, b, c) => PrecompiledOp::ShiftL(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ShiftR(a, b, c) => PrecompiledOp::ShiftR(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ShiftConst(a, b, c) => PrecompiledOp::ShiftConst(f(a, true), f(b, false), *c),

            PrecompiledOp::BinNot(a, b) => PrecompiledOp::BinNot(f(a, true), f(b, false)),
            PrecompiledOp::BoolNot(a, b) => PrecompiledOp::BoolNot(f(a, true), f(b, false)),
            PrecompiledOp::Condition(a, condition) =>
                PrecompiledOp::Condition(f(a, true), condition.replace_regs(|r| f(r, false))),

            PrecompiledOp::Select(a, condition, c, d) =>
                PrecompiledOp::Select(f(a, true), condition.replace_regs(|r| f(r, false)), f(c, false), f(d, false)),

            PrecompiledOp::DigitSum(a, b) => PrecompiledOp::DigitSum(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumSmall(a, b) => PrecompiledOp::DigitSumSmall(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumTwice(a, b) => PrecompiledOp::DigitSumTwice(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumDigitSumLensum(a, b) => PrecompiledOp::DigitSumDigitSumLensum(f(a, true), f(b, false)),
            PrecompiledOp::Gcd(a, b, c) => PrecompiledOp::Gcd(f(a, true), f(b, false), f(c, false)),

            PrecompiledOp::StackSwap(a, b, c, d) => PrecompiledOp::StackSwap(f(a, true), f(b, false), f(c, false), *d),
            PrecompiledOp::StackRead(a, b, c) => PrecompiledOp::StackRead(f(a, true), f(b, false), *c),

            PrecompiledOp::LoadConst(a, v) => PrecompiledOp::LoadConst(f(a, true), *v),
            PrecompiledOp::LoadConst64(a, ix) => PrecompiledOp::LoadConst64(f(a, true), *ix),

            PrecompiledOp::Jump(condition, ip) => PrecompiledOp::Jump(condition.replace_regs(|r| f(r, false)), *ip),

            PrecompiledOp::Assert(condition, code) => PrecompiledOp::Assert(condition.replace_regs(|r| f(r, false)), *code),
            PrecompiledOp::DeoptAssert(condition, id) => PrecompiledOp::DeoptAssert(condition.replace_regs(|r| f(r, false)), *id),
            PrecompiledOp::Done(ip) => PrecompiledOp::Done(*ip),

            PrecompiledOp::Median2(a, b, c) => PrecompiledOp::Median2(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MedianCursed2(a, b) => PrecompiledOp::MedianCursed2(f(a, true), f(b, false)),
            PrecompiledOp::Median3(a, b, c, d) => PrecompiledOp::Median3(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::MedianCursed3(a, b, c) => PrecompiledOp::MedianCursed3(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MedianCursed5(a, b, c, d, e) => PrecompiledOp::MedianCursed5(f(a, true), f(b, false), f(c, false), f(d, false), f(e, false)),

            PrecompiledOp::KsplangOp(op) => PrecompiledOp::KsplangOp(*op),
            PrecompiledOp::KsplangOpWithArg(op, a) => PrecompiledOp::KsplangOpWithArg(*op, f(a, false)),

            PrecompiledOp::Spill(value, a) => PrecompiledOp::Spill(*value, f(a, false)),
            PrecompiledOp::Unspill(value, a) => PrecompiledOp::Unspill(*value, f(a, true)),
        }
    }
}


#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Condition<TReg> {
    Eq(TReg, TReg), // a == b
    EqConst(TReg, i16), // a == const
    Neq(TReg, TReg), // a != b
    NeqConst(TReg, i16), // a != const
    Lt(TReg, TReg), // a < b
    LtConst(TReg, i16), // a < const
    Leq(TReg, TReg), // a <= b
    LeqConst(TReg, i16), // a <= const
    Gt(TReg, TReg), // a > b
    GtConst(TReg, i16), // a > const
    Geq(TReg, TReg), // a >= b
    GeqConst(TReg, i16), // a >= const
    Divides(TReg, TReg), // a % b == 0
    DividesConst(TReg, u16), // a % const == 0
    NotDivides(TReg, TReg), // a % b != 0
    NotDividesConst(TReg, u16), // a % const != 0
    True,
    False,
}

// New: map registers in conditions (all reads)
impl<TReg> Condition<TReg> {
    pub fn replace_regs<TReg2, F>(&self, f: F) -> Condition<TReg2>
    where
        F: Fn(&TReg) -> TReg2,
    {
        match self {
            Condition::Eq(a, b) => Condition::Eq(f(a), f(b)),
            Condition::EqConst(a, c) => Condition::EqConst(f(a), *c),
            Condition::Neq(a, b) => Condition::Neq(f(a), f(b)),
            Condition::NeqConst(a, c) => Condition::NeqConst(f(a), *c),
            Condition::Lt(a, b) => Condition::Lt(f(a), f(b)),
            Condition::LtConst(a, c) => Condition::LtConst(f(a), *c),
            Condition::Leq(a, b) => Condition::Leq(f(a), f(b)),
            Condition::LeqConst(a, c) => Condition::LeqConst(f(a), *c),
            Condition::Gt(a, b) => Condition::Gt(f(a), f(b)),
            Condition::GtConst(a, c) => Condition::GtConst(f(a), *c),
            Condition::Geq(a, b) => Condition::Geq(f(a), f(b)),
            Condition::GeqConst(a, c) => Condition::GeqConst(f(a), *c),
            Condition::Divides(a, b) => Condition::Divides(f(a), f(b)),
            Condition::DividesConst(a, c) => Condition::DividesConst(f(a), *c),
            Condition::NotDivides(a, b) => Condition::NotDivides(f(a), f(b)),
            Condition::NotDividesConst(a, c) => Condition::NotDividesConst(f(a), *c),
            Condition::True => Condition::True,
            Condition::False => Condition::False,
        }
    }

    pub fn regs(&self) -> ArrayVec<TReg, 2>
    where TReg: Clone {
        let mut out = ArrayVec::<TReg, 2>::new();
        match self {
            Condition::Eq(a, b) | Condition::Neq(a, b) | Condition::Lt(a, b)
            | Condition::Leq(a, b) | Condition::Gt(a, b) | Condition::Geq(a, b) | Condition::Divides(a, b) | Condition::NotDivides(a, b) => {
                out.push(a.clone());
                out.push(b.clone());
            },
            Condition::EqConst(a, _) | Condition::NeqConst(a, _) | Condition::LtConst(a, _)
            | Condition::LeqConst(a, _) | Condition::GtConst(a, _) | Condition::GeqConst(a, _) | Condition::DividesConst(a, _) | Condition::NotDividesConst(a, _) => {
                out.push(a.clone());
            },
            Condition::True | Condition::False => { }
        }
        out
    }

    pub fn discriminant(&self) -> usize {
        match self {
            Condition::Eq(_, _) => 0,
            Condition::EqConst(_, _) => 1,
            Condition::Neq(_, _) => 2,
            Condition::NeqConst(_, _) => 3,
            Condition::Lt(_, _) => 4,
            Condition::LtConst(_, _) => 5,
            Condition::Leq(_, _) => 6,
            Condition::LeqConst(_, _) => 7,
            Condition::Gt(_, _) => 8,
            Condition::GtConst(_, _) => 9,
            Condition::Geq(_, _) => 10,
            Condition::GeqConst(_, _) => 11,
            Condition::Divides(_, _) => 12,
            Condition::DividesConst(_, _) => 13,
            Condition::NotDivides(_, _) => 14,
            Condition::NotDividesConst(_, _) => 15,
            Condition::True => 16,
            Condition::False => 17,
        }
    }

    pub fn eval(&self, args: &[i64]) -> bool {
        match self {
            Condition::Eq(_, _) => args[0] == args[1],
            Condition::EqConst(_, c) => args[0] == *c as i64,
            Condition::Neq(_, _) => args[0] != args[1],
            Condition::NeqConst(_, c) => args[0] != *c as i64,
            Condition::Lt(_, _) => args[0] < args[1],
            Condition::LtConst(_, c) => args[0] < *c as i64,
            Condition::Leq(_, _) => args[0] <= args[1],
            Condition::LeqConst(_, c) => args[0] <= *c as i64,
            Condition::Gt(_, _) => args[0] > args[1],
            Condition::GtConst(_, c) => args[0] > *c as i64,
            Condition::Geq(_, _) => args[0] >= args[1],
            Condition::GeqConst(_, c) => args[0] >= *c as i64,
            Condition::Divides(_, _) => args[1] != 0 && args[0] % args[1] == 0,
            Condition::DividesConst(_, c) => *c != 0 && args[0] % (*c as i64) == 0,
            Condition::NotDivides(_, _) => args[1] == 0 || args[0] % args[1] != 0,
            Condition::NotDividesConst(_, c) => *c == 0 || args[0] % (*c as i64) != 0,
            Condition::True => true,
            Condition::False => false,
        }
    }

    pub fn neg(self) -> Condition<TReg> {
        match self {
            Condition::Eq(a, b) => Condition::Neq(a, b),
            Condition::EqConst(a, c) => Condition::NeqConst(a, c),
            Condition::Neq(a, b) => Condition::Eq(a, b),
            Condition::NeqConst(a, c) => Condition::EqConst(a, c),
            Condition::Lt(a, b) => Condition::Geq(a, b),
            Condition::LtConst(a, c) => Condition::GeqConst(a, c),
            Condition::Leq(a, b) => Condition::Gt(a, b),
            Condition::LeqConst(a, c) => Condition::GtConst(a, c),
            Condition::Gt(a, b) => Condition::Leq(a, b),
            Condition::GtConst(a, c) => Condition::LeqConst(a, c),
            Condition::Geq(a, b) => Condition::Lt(a, b),
            Condition::GeqConst(a, c) => Condition::LtConst(a, c),
            Condition::Divides(a, b) => Condition::NotDivides(a, b),
            Condition::DividesConst(a, c) => Condition::NotDividesConst(a, c),
            Condition::NotDivides(a, b) => Condition::Divides(a, b),
            Condition::NotDividesConst(a, c) => Condition::DividesConst(a, c),
            Condition::True => Condition::False,
            Condition::False => Condition::True,
        }
    }
}

impl<T: fmt::Display> fmt::Display for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Condition::Eq(a, b) => write!(f, "{} == {}", a, b),
            Condition::EqConst(a, c) => write!(f, "{} == {}", a, c),
            Condition::Neq(a, b) => write!(f, "{} != {}", a, b),
            Condition::NeqConst(a, c) => write!(f, "{} != {}", a, c),
            Condition::Lt(a, b) => write!(f, "{} < {}", a, b),
            Condition::LtConst(a, c) => write!(f, "{} < {}", a, c),
            Condition::Leq(a, b) => write!(f, "{} <= {}", a, b),
            Condition::LeqConst(a, c) => write!(f, "{} <= {}", a, c),
            Condition::Gt(a, b) => write!(f, "{} > {}", a, b),
            Condition::GtConst(a, c) => write!(f, "{} > {}", a, c),
            Condition::Geq(a, b) => write!(f, "{} >= {}", a, b),
            Condition::GeqConst(a, c) => write!(f, "{} >= {}", a, c),
            Condition::Divides(a, b) => write!(f, "{} % {} == 0", a, b),
            Condition::DividesConst(a, c) => write!(f, "{} % {} == 0", a, c),
            Condition::NotDivides(a, b) => write!(f, "{} % {} != 0", a, b),
            Condition::NotDividesConst(a, c) => write!(f, "{} % {} != 0", a, c),
            Condition::True => write!(f, "true"),
            Condition::False => write!(f, "false"),
        }
    }
}
impl<T: fmt::Display> fmt::Debug for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

#[derive(Debug, Clone)]
pub struct DeoptInfo {
    additional_opcodes: Vec<PrecompiledOp<u8>>,
    stack_reconstruction: Vec<u8>,
    ip: usize
}

pub struct PrecompiledBlock {
    pub program: Box<[PrecompiledOp<u8>]>,
    pub stack_space_required: u32,
    pub stack_values_required: u32,
    pub large_constants: Box<[i64]>,
    // pub deopts: HashMap<u32, >
}

// impl PrecompiledBlock {
//     pub fn from_cfg(g: &GraphBuilder) -> PrecompiledBlock {
//         let branching = vec![];
//     }
// }

#[derive(Clone, Debug, Default)]
struct Compiler {
    program: Vec<PrecompiledOp<u8>>,
    constants: Vec<i64>,
    deopts: Vec<DeoptInfo>,
    block_starts: HashMap<u32, u32>,
    register_allocation: HashMap<u8, ValueId>,
    branches: Vec<(u32, u32)>, // position, block number
    value_lifetimes: HashMap<ValueId, Vec<(BlockId, u32, u32)>>,
}

impl Compiler {
    pub fn new() -> Self {
        // let mut c = Compiler::default();
        // for reg in 0..256 {
            
        // }
        todo!()
    }
    fn compile(&mut self, g: &GraphBuilder) {

    }

    fn compile_block(&mut self, g: &GraphBuilder, b: u32) {
        for (id, i) in &g.blocks[b as usize].instructions {
            
        }
    }
}

struct RegisterAllocation {
    regs: HashSet<ValueId, Vec<(InstrId, InstrId, u8)>>,
}

fn allocate_registers(g: &GraphBuilder, reg_count: u32) -> RegisterAllocation {
    // let lifetimes = analyze_value_lifetimes(g);
    // let equivalences = equivalence_preferences(g);
    // let remat_costs = remat_cost(g, &lifetimes, 100);

    // let get_equivalence_preferences = |val: ValueId| equivalences.range((val, ValueId(1))..=(val, ValueId(i32::MAX))).map(|c| (c.0.1, *c.1));
    // let find_already_assigned = |val: ValueId| {
    //     let eqs1 = get_equivalence_preferences(val);
    //     let eqs2 = eqs1.flat_map(|(val, count)| get_equivalence_preferences(val).map(move |(val2, count2)| (val2, count2.saturating_add(count))).chain([(val, count)]));
    //     let mut res = BTreeMap::new();
    //     for (val, count) in eqs2 {
    //         let x = res.entry(val).or_insert(0u32);
    //         *x = x.saturating_add(count);
    //     }
    //     let mut res: Vec<_> = res.into_iter().collect();
    //     res.sort_by_key(|x| cmp::Reverse(x.1));
    //     res
    // };

    // let mut spill_vals = HashMap::<ValueId, u32>::new();
    // let mut spills = Vec::<(ValueId, InstrId)>::new();
    // let mut unspills = Vec::<(ValueId, InstrId)>::new();

    todo!()
}

fn equivalence_preferences(g: &GraphBuilder) -> BTreeMap<(ValueId, ValueId), u32> {
    let mut result = BTreeMap::new();

    for block in &g.blocks {
        for i in block.instructions.values() {
            if i.inputs.len() == 0 { continue; }
            let OptOp::Jump(_, into_block) = i.op else { continue; };

            let into_block = g.block_(into_block);
            for (param, val) in into_block.parameters.iter().zip(i.inputs.iter()) {
                if val.is_computed() {
                    *result.entry((*param, *val)).or_insert(0u32) += 1;
                    *result.entry((*val, *param)).or_insert(0u32) += 1;
                }
            }
        }
    }

    result
}

fn remat_cost(g: &GraphBuilder, lr: &LiveRanges, max_cost: u32) -> HashMap<ValueId, HashMap<InstrId, u32>> {
    let mut rematerializable: HashMap<ValueId, (u32, SmallVec<[ValueId; 4]>)> = HashMap::new();
    let mut pulls_in: HashMap<(ValueId, InstrId), SmallVec<[ValueId;4]>> = HashMap::new();
    for v in g.values.values() {
        let Some(i) = v.assigned_at.and_then(|i| g.get_instruction(i)) else { continue; };
        // if i.effect != OpEffect::None && i.effect != OpEffect::MayFail { }
        let rmat_cost = match i.op {
            OptOp::BinNot | OptOp::ShiftR | OptOp::BoolNot | OptOp::Condition(_) | OptOp::Or | OptOp::And | OptOp::Xor | OptOp::Min | OptOp::Max | OptOp::AbsFactorial | OptOp::Sgn | OptOp::ShiftL | OptOp::DigitSum | OptOp::Add | OptOp::AbsSub | OptOp::Select(_)=>
                10,
            OptOp::Mul => 12,
            OptOp::Div | OptOp::CursedDiv | OptOp::LenSum | OptOp::Mod | OptOp::ModEuclid => 14,
            OptOp::Median => 8 * i.inputs.len() as u32,
            OptOp::Gcd | OptOp::Funkcia | OptOp::Tetration => 19,
            _ => continue
        } + match i.effect {
            OpEffect::MayDeopt => 6,
            OpEffect::MayFail => 4,
            OpEffect::None => 0,
            _ => continue
        };

        let uniq_args: BTreeSet<_> = i.iter_inputs().filter(|i| i.is_computed()).collect();

        for used_at in &v.used_at {
            let unlive_args = uniq_args.iter().copied().filter(|i| !lr.is_live_at(*i, *used_at)).collect();

            pulls_in.insert((v.id, *used_at), unlive_args);
        }
        // free code motion?
        let rmat_cost = if v.used_at.len() == 1 && i.effect == OpEffect::None { 0 } else { rmat_cost };
        rematerializable.insert(v.id, (rmat_cost, uniq_args.iter().copied().collect()));
    }

    fn cost_fn(at: InstrId, val: ValueId, rematerializable: &HashMap<ValueId, (u32, SmallVec<[ValueId; 4]>)>, lr: &LiveRanges, max_cost: u32) -> Option<u32> {
        let Some((mut cost, deps)) = rematerializable.get(&val) else {
            return None
        };
        for dependency in deps {
            if lr.is_live_at(*dependency, at) {
                continue;
            }

            let Some(dep_cost) = cost_fn(at, *dependency, rematerializable, lr, max_cost) else {
                return None;
            };
            cost += dep_cost;
            if cost >= max_cost {
                return None;
            }
        }
        Some(cost)
    }

    let mut result: HashMap<ValueId, HashMap<InstrId, u32>> = HashMap::new();
    for val in g.values.values() {
        if !rematerializable.contains_key(&val.id) {
            continue;
        }
        for at in &val.used_at {
            if let Some(cost) = cost_fn(*at, val.id, &rematerializable, lr, max_cost) {
                result.entry(val.id).or_default().insert(*at, cost);
            }
        }
    }
    result
}

struct LiveRanges {
    pub ranges: HashMap<ValueId, HashMap<BlockId, (InstrId, InstrId)>>,
    pub live_vars: HashMap<BlockId, Vec<(InstrId, InstrId, ValueId)>>,
}

impl LiveRanges {
    fn is_live_at(&self, val: ValueId, i: InstrId) -> bool {
        self.ranges.get(&val).unwrap().get(&i.0)
            .is_some_and(|(from, to)| *from < i && i <= *to)
    }
}

fn analyze_value_lifetimes(g: &GraphBuilder) -> LiveRanges {
    //  defined values -> used values
    let blocks: Vec<(HashSet<ValueId>, HashSet<ValueId>)> =
        g.blocks.iter().map(|b| {
            let mut defined = HashSet::new();
            let mut require = HashSet::new();

            for p in &b.parameters { defined.insert(*p); }

            for i in b.instructions.values() {
                for input in i.iter_inputs() {
                    if input.is_computed() && !defined.contains(&input) {
                        require.insert(input);
                    }
                }
                if i.out.is_computed() { defined.insert(i.out); }
            }

            (defined, require)
        })
        .collect();

    let perblock_req = dataflow(g, /*reverse:*/ true,
        |b| blocks[b.id.0 as usize].1.clone(),
        |b, state, _inputs, outputs| {
            let mut required = state.clone();
            let defines = &blocks[b.id.0 as usize].0;
            for out in outputs {
                for val in *out {
                    if !defines.contains(val) {
                        required.insert(*val);
                    }
                }
            }
            return required
        });

    let mut ranges = HashMap::new();
    let mut live_vars = HashMap::new();
    for block in &g.blocks {
        let mut defined_at = HashMap::new();
        let mut last_use: HashMap<ValueId, u32> = HashMap::new();
        for (&id, i) in block.instructions.iter() {
            for input in i.iter_inputs() {
                if input.is_computed() {
                    last_use.insert(input, id);
                }
            }
            if i.out.is_computed() { defined_at.insert(i.out, id); }
        }

        let mut result = vec![];

        // let mut transfers = HashSet::new();
        // transferred_variables
        for (_, jump_to) in &block.outgoing_jumps {
            for &next_requires in perblock_req.get(&jump_to).iter().flat_map(|x| *x) {
                if let Some(&from) = defined_at.get(&next_requires) {
                    result.push((InstrId(block.id, from), InstrId(block.id, u32::MAX), next_requires));
                } else {
                    result.push((InstrId(block.id, 0), InstrId(block.id, u32::MAX), next_requires));
                }
                last_use.remove(&next_requires);
            }
        }

        for (&var, &last_use) in last_use.iter() {
            if let Some(&from) = defined_at.get(&var) {
                result.push((InstrId(block.id, from), InstrId(block.id, last_use), var));
            } else {
                result.push((InstrId(block.id, 0), InstrId(block.id, u32::MAX), var));
            }
        }

        for (from, to, var) in &result {
            let var_ranges: &mut HashMap<BlockId, (InstrId, InstrId)> = ranges.entry(*var).or_default();
            var_ranges.insert(block.id, (from.clone(), to.clone()));
        }

        live_vars.insert(block.id, result);
    }

    LiveRanges { ranges, live_vars }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BBOrderInfo {
    pub always_before: HashSet<BlockId>,
    pub always_after: HashSet<BlockId>,
}

// fn analyze_order(g: &GraphBuilder) -> Vec<BBOrderInfo> {
//     let forward = dataflow(g,
//         |g| HashSet::new(),
//         |g, state, ins, outs| {
//
//         })
// }

pub fn postorder(g: &GraphBuilder) -> Vec<BlockId> {
    let mut visited = vec![false; g.blocks.len()];
    let mut result = vec![];

    fn core(g: &GraphBuilder, id: BlockId, visited: &mut Vec<bool>, result: &mut Vec<BlockId>) {
        let b = &g.blocks[id.0 as usize];
        visited[id.0 as usize] = true;
        for (_, next) in &b.outgoing_jumps {
            if !visited[next.0 as usize] {
                core(g, *next, visited, result);
            }
        }
        result.push(id);
    }

    core(g, BlockId(0), &mut visited, &mut result);

    return result;
}

fn dataflow<T: PartialEq>(
    g: &GraphBuilder,
    reverse: bool,
    init: impl Fn(&BasicBlock) -> T,
    step: impl Fn(&BasicBlock, &T, &[&T], &[&T]) -> T
) -> HashMap<BlockId, T> {
    let mut order = postorder(g);
    if reverse {
        order.reverse();
    }
    let mut lookup = vec![usize::MAX; order.len()];
    for (i, id) in order.iter().enumerate() {
        lookup[id.0 as usize] = i;
    }
    let mut state: Vec<T> = order.iter().map(|id| init(&g.blocks[id.0 as usize])).collect();

    let mut iters = 0;

    loop {
        let next_state: Vec<T> = state.iter().zip(order.iter()).map(|(s, bid)| {
            let b = g.block_(*bid);
            let ins: SmallVec<[&T; 4]> =
                b.incoming_jumps.iter().map(|i| &state[lookup[i.block_id().0 as usize]]).collect();
            let outs: SmallVec<[&T; 4]> =
                b.outgoing_jumps.iter().map(|(_i, b)| &state[lookup[b.0 as usize]]).collect();
            step(b, s, &ins, &outs)
        }).collect();

        if next_state == state {
            return order.into_iter().zip(next_state.into_iter()).collect();
        }

        state = next_state;

        assert!(iters < g.blocks.len() + 10, "{iters} > {}", g.blocks.len());
        iters += 1;
    }
}

#[test]
fn test_compile() {
    assert_eq!(mem::size_of::<Condition<u8>>(), 4);
    assert_eq!(mem::size_of::<PrecompiledOp<u8>>(), 8);
}

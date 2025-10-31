use core::fmt;
use std::{cmp, collections::{BTreeMap, BTreeSet, HashMap, HashSet}, fmt::Display, u32};
use arrayvec::ArrayVec;
use smallvec::SmallVec;

use crate::compiler::{cfg::{BasicBlock, GraphBuilder}, ops::{BlockId, InstrId, OpEffect, OptInstr, OptOp, ValueId}};
use crate::vm::OperationError;


#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct RegId(pub u8);

impl fmt::Display for RegId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

impl fmt::Debug for RegId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrecompiledOp<TReg: Display> {
    Push(TReg),
    Push2(TReg, TReg),
    Push3(TReg, TReg, TReg),
    Push4(TReg, TReg, TReg, TReg),
    Push5(TReg, TReg, TReg, TReg, TReg),
    Push6(TReg, TReg, TReg, TReg, TReg, TReg),
    Push7(TReg, TReg, TReg, TReg, TReg, TReg, TReg),
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
    AbsSubConst(TReg, TReg, i32), // a <- |b - c|
    Mul(TReg, TReg, TReg), // a <- b * c
    MulConst(TReg, TReg, i32), // a <- b * const
    Div(TReg, TReg, TReg), // a <- b / c
    DivConst(TReg, TReg, i32), // a <- b / c
    CursedDiv(TReg, TReg, TReg), // a <- b % c if non-zero, otherwise b / c
    Mod(TReg, TReg, TReg), // a <- b % c
    ModConst(TReg, TReg, i32), // a <- b % c
    ModEuclid(TReg, TReg, TReg), // a <- b mod c (always non-negative)
    ModEuclidConst(TReg, TReg, i32), // a <- b mod c (always non-negative)
    Tetration(TReg, TReg, TReg), // a <- b tetrated c times
    Funkcia(TReg, TReg, TReg), // a <- funkcia(b, c)
    Max(TReg, TReg, TReg), // a <- max(b, c)
    MaxConst(TReg, TReg, i32), // a <- max(b, c)
    Min(TReg, TReg, TReg), // a <- min(b, c)
    MinConst(TReg, TReg, i32), // a <- min(b, c)
    Clamp(TReg, TReg, TReg, TReg), // a <- min(max(a, b), c)
    ClampConst(TReg, TReg, i16, i16), // a <- min(max(a, b), c)
    Sgn(TReg, TReg), // a <- sgn(b)
    AbsFactorial(TReg, TReg), // a <- |b|!
    Lensum(TReg, TReg, TReg), // a <- lensum(b, c)
    Universal2(TReg, TReg, TReg, TReg), // a <- universal[b](c, d) (or deopt if universal1 should be used instead)
    Universal1(TReg, TReg, TReg), // a <- universal[b](c) (or deopt if universal2 should be used instead)
    And(TReg, TReg, TReg), // a <- b & c
    AndConst(TReg, TReg, i32), // a <- b & c
    Or(TReg, TReg, TReg), // a <- b | c
    OrConst(TReg, TReg, i32), // a <- b | c
    Xor(TReg, TReg, TReg), // a <- b ^ c
    XorConst(TReg, TReg, i32), // a <- b ^ c
    ShiftL(TReg, TReg, TReg), // a <- b << c
    ShiftR(TReg, TReg, TReg), // a <- b >> c
    ShiftConst(TReg, TReg, i8), // a <- b << const OR b >> const (based on sign)

    BinNot(TReg, TReg), // a <- ~b
    BoolNot(TReg, TReg), // a <- !b
    SelectConst(TReg, Condition<TReg>, i8, i8), // a <- condition ? b : c
    SelectConst0(TReg, Condition<TReg>, i16), // a <- condition ? b : 0

    Select(TReg, Condition<TReg>, TReg, TReg), // a <- b ? c : d

    DigitSum(TReg, TReg), // a <- digit_sum(b)
    DigitSumSmall(TReg, TReg), // a <- digit_sum(b); if b > 10_000, deopt
    DigitSumTwice(TReg, TReg), // a <- digit_sum(digit_sum(b))
    DigitSumDigitSumLensum(TReg, TReg), // a <- lensum(digit_sum(digit_sum(b)), digit_sum(b))
    Gcd(TReg, TReg, TReg), // a <- gcd(b, c)

    StackSwap(TReg, TReg, TReg, u8), // a <- stack[b]; stack[b] <- c; if b + d >= stack_size, deopt
    StackWrite(TReg, TReg, u8),      // stack[a] <- b; if a + d >= stack_size, deopt
    StackRead(TReg, TReg, u8),       // a <- stack[b];                if b + c >= stack_size, deopt

    LoadConst(TReg, i32),
    LoadConstPow2Offset(TReg, u8, i32),
    LoadConst64(TReg, u16),

    Jump(Condition<TReg>, u16), // if true: jump to instruction (in this precompiled block)

    Assert(Condition<TReg>, u16, TReg), // error code + argument (optional)
    DeoptAssert(Condition<TReg>, u16), // if false: abort block execution, deopt info number
    Done(u32), // instruction pointer where to continue execution (if it can't fit into u32, then we'll standard deopt)
    Median2(TReg, TReg, TReg), // a <- median(b, c)
    MedianCursed2(TReg, TReg), // a <- median(b, 2)
    Median3(TReg, TReg, TReg, TReg), // a <- median(b, c, d)
    MedianCursed3(TReg, TReg, TReg), // a <- median(b, c, 3)
    MedianCursed5(TReg, TReg, TReg, TReg, TReg), // a <- median(b, c, d, e, 5)
    KsplangOp(crate::ops::Op),
    KsplangOpWithArg(crate::ops::Op, TReg),

    KsplangOpsIncrement(u32), // ksplang_interpreted += c
    KsplangOpsIncrementVar(TReg), // ksplang_interpreted += a
    KsplangOpsIncrementCond(Condition<TReg>, u16), // ksplang_interpreted += c if condition

    Spill(u32, TReg), // somewhere[ix] <- a move to a larger register file, should not really happen but easier to implement this than a proper register allocator...
    Unspill(TReg, u32), // a <- somewhere[ix]
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
            PrecompiledOp::Push5(a, b, c, d, e) => PrecompiledOp::Push5(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false)),
            PrecompiledOp::Push6(a, b, c, d, e, f_) => PrecompiledOp::Push6(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false), f(f_, false)),
            PrecompiledOp::Push7(a, b, c, d, e, f_, g) => PrecompiledOp::Push7(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false), f(f_, false), f(g, false)),

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
            PrecompiledOp::AbsSubConst(a, b, c) => PrecompiledOp::AbsSubConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Mul(a, b, c) => PrecompiledOp::Mul(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MulConst(a, b, c) => PrecompiledOp::MulConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Div(a, b, c) => PrecompiledOp::Div(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::DivConst(a, b, c) => PrecompiledOp::DivConst(f(a, true), f(b, false), *c),
            PrecompiledOp::CursedDiv(a, b, c) => PrecompiledOp::CursedDiv(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Mod(a, b, c) => PrecompiledOp::Mod(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ModConst(a, b, c) => PrecompiledOp::ModConst(f(a, true), f(b, false), *c),
            PrecompiledOp::ModEuclid(a, b, c) => PrecompiledOp::ModEuclid(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ModEuclidConst(a, b, c) => PrecompiledOp::ModEuclidConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Tetration(a, b, c) => PrecompiledOp::Tetration(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Funkcia(a, b, c) => PrecompiledOp::Funkcia(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Max(a, b, c) => PrecompiledOp::Max(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MaxConst(a, b, c) => PrecompiledOp::MaxConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Min(a, b, c) => PrecompiledOp::Min(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MinConst(a, b, c) => PrecompiledOp::MinConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Clamp(a, b, c, d) => PrecompiledOp::Clamp(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::ClampConst(a, b, c, d) => PrecompiledOp::ClampConst(f(a, true), f(b, false), *c, *d),
            PrecompiledOp::Sgn(a, b) => PrecompiledOp::Sgn(f(a, true), f(b, false)),
            PrecompiledOp::AbsFactorial(a, b) => PrecompiledOp::AbsFactorial(f(a, true), f(b, false)),
            PrecompiledOp::Lensum(a, b, c) => PrecompiledOp::Lensum(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::Universal2(a, b, c, d) => PrecompiledOp::Universal2(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::Universal1(a, b, c) => PrecompiledOp::Universal1(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::And(a, b, c) => PrecompiledOp::And(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::AndConst(a, b, c) => PrecompiledOp::AndConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Or(a, b, c) => PrecompiledOp::Or(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::OrConst(a, b, c) => PrecompiledOp::OrConst(f(a, true), f(b, false), *c),
            PrecompiledOp::Xor(a, b, c) => PrecompiledOp::Xor(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::XorConst(a, b, c) => PrecompiledOp::XorConst(f(a, true), f(b, false), *c),
            PrecompiledOp::ShiftL(a, b, c) => PrecompiledOp::ShiftL(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ShiftR(a, b, c) => PrecompiledOp::ShiftR(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::ShiftConst(a, b, c) => PrecompiledOp::ShiftConst(f(a, true), f(b, false), *c),

            PrecompiledOp::BinNot(a, b) => PrecompiledOp::BinNot(f(a, true), f(b, false)),
            PrecompiledOp::BoolNot(a, b) => PrecompiledOp::BoolNot(f(a, true), f(b, false)),

            PrecompiledOp::SelectConst(a, condition, b, c) =>
                PrecompiledOp::SelectConst(f(a, true), condition.replace_regs(|r| f(r, false)), *b, *c),
            PrecompiledOp::SelectConst0(a, condition, b) =>
                PrecompiledOp::SelectConst0(f(a, true), condition.replace_regs(|r| f(r, false)), *b),
            PrecompiledOp::Select(a, condition, c, d) =>
                PrecompiledOp::Select(f(a, true), condition.replace_regs(|r| f(r, false)), f(c, false), f(d, false)),

            PrecompiledOp::DigitSum(a, b) => PrecompiledOp::DigitSum(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumSmall(a, b) => PrecompiledOp::DigitSumSmall(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumTwice(a, b) => PrecompiledOp::DigitSumTwice(f(a, true), f(b, false)),
            PrecompiledOp::DigitSumDigitSumLensum(a, b) => PrecompiledOp::DigitSumDigitSumLensum(f(a, true), f(b, false)),
            PrecompiledOp::Gcd(a, b, c) => PrecompiledOp::Gcd(f(a, true), f(b, false), f(c, false)),

            PrecompiledOp::StackSwap(a, b, c, depth) => PrecompiledOp::StackSwap(f(a, true), f(b, false), f(c, false), *depth),
            PrecompiledOp::StackRead(a, b, depth) => PrecompiledOp::StackRead(f(a, true), f(b, false), *depth),
            PrecompiledOp::StackWrite(a, b, depth) => PrecompiledOp::StackRead(f(a, false), f(b, false), *depth),

            PrecompiledOp::LoadConst(a, v) => PrecompiledOp::LoadConst(f(a, true), *v),
            PrecompiledOp::LoadConst64(a, ix) => PrecompiledOp::LoadConst64(f(a, true), *ix),
            PrecompiledOp::LoadConstPow2Offset(a, pow2, offset) => PrecompiledOp::LoadConstPow2Offset(f(a, true), *pow2, *offset),

            PrecompiledOp::Jump(condition, ip) => PrecompiledOp::Jump(condition.replace_regs(|r| f(r, false)), *ip),

            PrecompiledOp::Assert(condition, code, arg) => PrecompiledOp::Assert(condition.replace_regs(|r| f(r, false)), *code, f(arg, false)),
            PrecompiledOp::DeoptAssert(condition, id) => PrecompiledOp::DeoptAssert(condition.replace_regs(|r| f(r, false)), *id),
            PrecompiledOp::Done(ip) => PrecompiledOp::Done(*ip),

            PrecompiledOp::Median2(a, b, c) => PrecompiledOp::Median2(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MedianCursed2(a, b) => PrecompiledOp::MedianCursed2(f(a, true), f(b, false)),
            PrecompiledOp::Median3(a, b, c, d) => PrecompiledOp::Median3(f(a, true), f(b, false), f(c, false), f(d, false)),
            PrecompiledOp::MedianCursed3(a, b, c) => PrecompiledOp::MedianCursed3(f(a, true), f(b, false), f(c, false)),
            PrecompiledOp::MedianCursed5(a, b, c, d, e) => PrecompiledOp::MedianCursed5(f(a, true), f(b, false), f(c, false), f(d, false), f(e, false)),

            PrecompiledOp::KsplangOp(op) => PrecompiledOp::KsplangOp(*op),
            PrecompiledOp::KsplangOpWithArg(op, a) => PrecompiledOp::KsplangOpWithArg(*op, f(a, false)),

            PrecompiledOp::KsplangOpsIncrement(inc) => PrecompiledOp::KsplangOpsIncrement(*inc),
            PrecompiledOp::KsplangOpsIncrementVar(inc) => PrecompiledOp::KsplangOpsIncrementVar(f(inc, false)),
            PrecompiledOp::KsplangOpsIncrementCond(cond, inc) => PrecompiledOp::KsplangOpsIncrementCond(cond.replace_regs(|r| f(r, false)), *inc),

            PrecompiledOp::Spill(value, a) => PrecompiledOp::Spill(*value, f(a, false)),
            PrecompiledOp::Unspill(a, value) => PrecompiledOp::Unspill(f(a, true), *value),
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

impl<TReg> Condition<TReg> {
    pub fn replace_regs<TReg2, F>(&self, mut f: F) -> Condition<TReg2>
    where
        F: FnMut(&TReg) -> TReg2,
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

    pub fn replace_arr<TReg2>(&self, mut f: Vec<TReg2>) -> Condition<TReg2> {
        f.reverse();
        let c2 = self.replace_regs(|_| f.pop().unwrap());
        assert_eq!(0, f.len());
        c2
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
            Condition::EqConst(a, c) => write!(f, "{} == [{}]", a, c),
            Condition::Neq(a, b) => write!(f, "{} != {}", a, b),
            Condition::NeqConst(a, c) => write!(f, "{} != [{}]", a, c),
            Condition::Lt(a, b) => write!(f, "{} < {}", a, b),
            Condition::LtConst(a, c) => write!(f, "{} < [{}]", a, c),
            Condition::Leq(a, b) => write!(f, "{} <= {}", a, b),
            Condition::LeqConst(a, c) => write!(f, "{} <= [{}]", a, c),
            Condition::Gt(a, b) => write!(f, "{} > {}", a, b),
            Condition::GtConst(a, c) => write!(f, "{} > [{}]", a, c),
            Condition::Geq(a, b) => write!(f, "{} >= {}", a, b),
            Condition::GeqConst(a, c) => write!(f, "{} >= [{}]", a, c),
            Condition::Divides(a, b) => write!(f, "{} % {} == 0", a, b),
            Condition::DividesConst(a, c) => write!(f, "{} % [{}] == 0", a, c),
            Condition::NotDivides(a, b) => write!(f, "{} % {} != 0", a, b),
            Condition::NotDividesConst(a, c) => write!(f, "{} % [{}] != 0", a, c),
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
    pub additional_opcodes: Box<[PrecompiledOp<RegId>]>,
    pub stack_reconstruction: SmallVec<[RegId; 16]>,
    pub ip: usize,
    pub ksplang_ops_increment: u32
}

pub struct PrecompiledBlock {
    pub program: Box<[PrecompiledOp<RegId>]>,
    pub stack_space_required: u32,
    pub stack_values_required: u32,
    pub start_ip: usize,
    pub large_constants: Box<[i64]>,
    pub ip2deopt: Box<[(u32, u32)]>, // IP -> deopt index ordered mapping
    pub deopts: Box<[DeoptInfo]>
}

impl fmt::Display for PrecompiledBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "PrecompiledBlock {{")?;
        writeln!(f, "  start_ip: {}, stack_space_required: {}, stack_values_required: {}", self.start_ip, self.stack_space_required, self.stack_values_required)?;

        if !self.large_constants.is_empty() {
            write!(f, "  large_constants: ")?;
            for (ix, value) in self.large_constants.iter().enumerate() {
                if ix > 0 { write!(f, ", ")?; }
                write!(f, "{ix}: {value}")?;
            }
            writeln!(f)?;
        }

        let mut deopt_iter = self.ip2deopt.iter().peekable();
        writeln!(f, "  program:")?;
        for (ix, op) in self.program.iter().enumerate() {
            write!(f, "    {ix:04}: {op:?}")?;
            while deopt_iter.peek().is_some_and(|&&(ip, _)| ip as usize == ix) {
                let (_, deopt_ix) = deopt_iter.next().unwrap();
                write!(f, " | deopt={}", deopt_ix)?;
            }
            writeln!(f)?;
        }

        if !self.deopts.is_empty() {
            writeln!(f, "  deopts ({}):", self.deopts.len())?;
            for (ix, deopt) in self.deopts.iter().enumerate() {
                writeln!(f, "    #{ix:04}: ip={}, ksplang_ops_increment={}", deopt.ip, deopt.ksplang_ops_increment)?;
                writeln!(f, "            stack reconstruction: {:?}", deopt.stack_reconstruction)?;
                writeln!(f, "            ops: {:?}", deopt.additional_opcodes)?;
            }
        }

        write!(f, "}}")
    }
}

impl fmt::Debug for PrecompiledBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

impl PrecompiledBlock {
    pub fn from_cfg(g: &GraphBuilder) -> PrecompiledBlock {
        let register_allocation = allocate_registers(g, ALLOCATABLE_REG_COUNT);
        println!("Register allocation: {}", register_allocation);
        let mut compiler = Compiler::new(g, register_allocation);
        compiler.compile();
        compiler.finish()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct Compiler<'a> {
    g: &'a GraphBuilder,
    program: Vec<PrecompiledOp<RegId>>,
    large_constants: Vec<i64>,
    large_constant_lookup: HashMap<i64, u16>,
    deopts: Vec<DeoptInfo>,
    block_starts: HashMap<BlockId, u16>,
    register_allocation: RegisterAllocation,
    jump_fixups: Vec<(usize, BlockId)>,
    temp_regs: TempRegPool,
}



#[derive(Clone, Copy, Debug)]
enum OutputSpec {
    Register(RegId),
    Spill { reg: RegId, slot: u32 },
}

impl OutputSpec {
    fn target_reg(&self) -> RegId {
        match self {
            OutputSpec::Register(reg) => *reg,
            OutputSpec::Spill { reg, .. } => *reg,
        }
    }
}

impl<'a> Compiler<'a> {
    fn new(g: &'a GraphBuilder, register_allocation: RegisterAllocation) -> Self {
        Self {
            g,
            program: Vec::new(),
            large_constants: Vec::new(),
            large_constant_lookup: HashMap::new(),
            deopts: Vec::new(),
            block_starts: HashMap::new(),
            register_allocation,
            jump_fixups: Vec::new(),
            temp_regs: TempRegPool::new(),
        }
    }

    fn compile(&mut self) {
        for block in &self.g.blocks {
            let start = self.program.len();
            let start_u16: u16 = start.try_into().expect("precompiled program exceeds 65535 ops");
            self.block_starts.insert(block.id, start_u16);
            self.compile_block(block);
        }
    }

    fn compile_block(&mut self, block: &BasicBlock) {
        let instrs: Vec<_> = block.instructions.values().collect();
        let mut i = 0;
        while i < instrs.len() {
            let consumed = self.compile_instruction(&instrs[i..]);
            assert_ne!(0, consumed);
            i += consumed;
        }
        assert_eq!(i, instrs.len())
    }

    /// Returns the number of instructions consumed (1 or more).
    fn compile_instruction(&mut self, instrs: &[&OptInstr]) -> usize {
        use OptOp::*;
        let instr = instrs[0];
        let mut consumed = 1;

        match &instr.op {
            Const(_) => panic!("Special op, should not be in CfG"),
            Add => self.lower_variadic(instr, |out, a, b| PrecompiledOp::Add(out, a, b), |out, a, c| Some(PrecompiledOp::AddConst(out, a, c.try_into().ok()?))),
            Mul => self.lower_mul(instr),
            Sub => self.lower_binary(instr, |out, a, b| PrecompiledOp::Sub(out, a, b), |_, _, _| None, |out, c, b| Some(PrecompiledOp::SubConst(out, c.try_into().ok()?, b))),
            AbsSub => self.lower_variadic(instr, |out, a, b| PrecompiledOp::AbsSub(out, a, b), |out, a, c| Some(PrecompiledOp::AbsSubConst(out, a, c.try_into().ok()?))),
            Div => return self.lower_div(instrs),
            CursedDiv => self.lower_binary(instr, |out, a, b| PrecompiledOp::CursedDiv(out, a, b), |_, _, _| None, |_, _, _| None),
            Mod => {
                let lhs_range = self.g.val_range_at(instr.inputs[0], instr.id);
                let lhs_non_negative = *lhs_range.start() >= 0;
                self.lower_binary(instr, |out, a, b| PrecompiledOp::Mod(out, a, b), {
                    move |out, a, c| {
                        let c: i32 = c.try_into().ok()?;
                        if c > 0 && (c as u64).is_power_of_two() && lhs_non_negative {
                            Some(PrecompiledOp::AndConst(out, a, c.wrapping_sub(1)))
                        } else {
                            Some(PrecompiledOp::ModConst(out, a, c))
                        }
                    }
                }, |_, _, _| None);
            }
            ModEuclid => {
                self.lower_binary(instr, |out, a, b| PrecompiledOp::ModEuclid(out, a, b), move |out, a, c| {
                    let c: i32 = c.try_into().ok()?;
                    if c > 0 && (c as u64).is_power_of_two() {
                        Some(PrecompiledOp::AndConst(out, a, c.wrapping_sub(1)))
                    } else {
                        Some(PrecompiledOp::ModEuclidConst(out, a, c))
                    }
                }, |_, _, _| None);
            }
            Tetration => self.lower_binary(instr, |out, a, b| PrecompiledOp::Tetration(out, a, b), |_, _, _| None, |_, _, _| None),
            Funkcia => self.lower_binary(instr, |out, a, b| PrecompiledOp::Funkcia(out, a, b), |_, _, _| None, |_, _, _| None),
            Max => consumed = self.lower_max(instrs),
            Min => self.lower_min(instr),
            Sgn => self.lower_unary(instr, |out, a| PrecompiledOp::Sgn(out, a)),
            AbsFactorial => self.lower_unary(instr, |out, a| PrecompiledOp::AbsFactorial(out, a)),
            LenSum => self.lower_binary(instr, |out, a, b| PrecompiledOp::Lensum(out, a, b), |_, _, _| None, |_, _, _| None),
            And => self.lower_variadic(instr, |out, a, b| PrecompiledOp::And(out, a, b), |out, a, c| c.try_into().ok().map(|mask| PrecompiledOp::AndConst(out, a, mask))),
            Or => self.lower_variadic(instr, |out, a, b| PrecompiledOp::Or(out, a, b), |out, a, c| c.try_into().ok().map(|mask| PrecompiledOp::OrConst(out, a, mask))),
            Xor => self.lower_variadic(instr, |out, a, b| PrecompiledOp::Xor(out, a, b), |out, a, c| c.try_into().ok().map(|mask| PrecompiledOp::XorConst(out, a, mask))),
            ShiftL => self.lower_binary(instr, |out, a, b| PrecompiledOp::ShiftL(out, a, b), |out, a, c| Some(PrecompiledOp::ShiftConst(out, a, c.try_into().ok()?)), |_, _, _| None),
            ShiftR => self.lower_binary(instr, |out, a, b| PrecompiledOp::ShiftR(out, a, b), |out, a, c: i64| Some(PrecompiledOp::ShiftConst(out, a, c.checked_neg()?.try_into().ok()?)), |_, _, _| None),
            BinNot => self.lower_unary(instr, |out, a| PrecompiledOp::BinNot(out, a)),
            BoolNot => self.lower_unary(instr, |out, a| PrecompiledOp::BoolNot(out, a)),
            Select(condition) => self.lower_select(instr, condition.clone()),
            DigitSum => consumed = self.lower_digit_sum(instrs),
            Gcd => self.lower_variadic(instr, |out, a, b| PrecompiledOp::Gcd(out, a, b), |_, _, _| None),
            Push => self.lower_push(instr),
            Pop => self.lower_pop(instr),
            StackSwap => self.lower_stack_swap(instr),
            Jump(condition, target) => self.lower_jump(condition.clone(), *target),
            Assert(condition, error) => self.lower_assert(instr, condition.clone(), error.clone()),
            DeoptAssert(_) => todo!(),
            Checkpoint => { },
            Nop => { },
            Median | MedianCursed | Universal => todo!("{instr:?}"),
        }
        self.temp_regs.clear();
        consumed
    }

    fn lower_variadic<F, FC>(&mut self, instr: &OptInstr, op: F, op_const: FC)
    where
        F: Fn(RegId, RegId, RegId) -> PrecompiledOp<RegId>,
        FC: Fn(RegId, RegId, i64) -> Option<PrecompiledOp<RegId>>,
    {
        assert!(!instr.inputs.is_empty());

        let spec = self.prepare_output(instr.out);
        let dest = spec.target_reg();

        let mut inputs = instr.inputs.iter().copied();
        let first_val = inputs.next().unwrap();

        if let Some(second_val) = inputs.next() {
            debug_assert!(!second_val.is_constant());
            let second_reg = self.materialize_value_(second_val);
            // Check if first input is a constant (due to commutative property)
            if let Some(const_op) = self.g.get_constant(first_val).and_then(|v| op_const(dest, second_reg, v)) {
                self.program.push(const_op);
            } else {
                let first_reg = self.materialize_value_(first_val);
                self.program.push(op(dest, first_reg, second_reg));
            }
            for value in inputs {
                let reg = self.materialize_value_(value);
                self.program.push(op(dest, dest, reg));
            }
        } else {
            let first_reg = self.materialize_value_(first_val);
            self.program.push(PrecompiledOp::AddConst(dest, first_reg, 0));
        }

        self.finalize_output(spec);
    }

    fn lower_binary<F, FC1, FC2>(&mut self, instr: &OptInstr, op: F, op_const_rhs: FC1, op_const_lhs: FC2)
    where
        F: Fn(RegId, RegId, RegId) -> PrecompiledOp<RegId>,
        FC1: Fn(RegId, RegId, i64) -> Option<PrecompiledOp<RegId>>,
        FC2: Fn(RegId, i64, RegId) -> Option<PrecompiledOp<RegId>>,
    {
        debug_assert_eq!(instr.inputs.len(), 2, "{instr}");
        let spec = self.prepare_output(instr.out);

        if let Some(const_val) = self.g.get_constant(instr.inputs[0]) {
            if let Some(const_op) = op_const_lhs(spec.target_reg(), const_val, RegId(0)) {
                let rhs = self.materialize_value_(instr.inputs[1]);
                // Replace the dummy register with the actual one
                self.program.push(const_op.replace_regs(|reg, is_write| if is_write { *reg } else { rhs }));
                self.finalize_output(spec);
                return;
            }
        }
        
        if let Some(const_val) = self.g.get_constant(instr.inputs[1]) {
            if let Some(const_op) = op_const_rhs(spec.target_reg(), RegId(0), const_val) {
                let lhs = self.materialize_value_(instr.inputs[0]);
                // Replace the dummy register with the actual one
                self.program.push(const_op.replace_regs(|reg, is_write| if is_write { *reg } else { lhs }));
                self.finalize_output(spec);
                return;
            }
        }
        
        let lhs = self.materialize_value_(instr.inputs[0]);
        let rhs = self.materialize_value_(instr.inputs[1]);
        self.program.push(op(spec.target_reg(), lhs, rhs));

        self.finalize_output(spec);
    }

    fn lower_max(&mut self, instrs: &[&OptInstr]) -> usize {
        let max = instrs[0];
        assert_eq!(2, max.inputs.len());

        if let Some(lo_const) = self.g.get_constant(max.inputs[0]) {
            if let Some(&min) = instrs.get(1) {
                // min(hi_const, max(lo_const, x)) -> clamp(x, lo_const, hi_const)
                if min.op == OptOp::Min && min.inputs.len() == 2 && min.inputs[1] == max.out {
                    if let Some(hi_const) = self.g.get_constant(min.inputs[0]) {
                        assert!(lo_const < hi_const);
                        if let (Ok(lo_i16), Ok(hi_i16)) = (lo_const.try_into(), hi_const.try_into()) {
                            let spec = self.prepare_output(min.out);
                            let value_reg = self.materialize_value_(max.inputs[1]);
                            self.program.push(PrecompiledOp::ClampConst(spec.target_reg(), value_reg, lo_i16, hi_i16));
                            self.finalize_output(spec);
                            return 2; // Consumed Max, Min
                        }
                    }
                }
            }
        }

        self.lower_variadic(max, |out, a, b| PrecompiledOp::Max(out, a, b), |out, a, c| Some(PrecompiledOp::MaxConst(out, a, c.try_into().ok()?)));
        1
    }

    fn lower_min(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| PrecompiledOp::Min(out, a, b), |out, a, c| Some(PrecompiledOp::MinConst(out, a, c.try_into().ok()?)));
    }

    fn lower_div(&mut self, instrs: &[&OptInstr]) -> usize {
        let div = instrs[0];
        assert_eq!(2, div.inputs.len());

        if let Some(divisor) = self.g.get_constant(div.inputs[1]) {
            if let Some(&next) = instrs.get(1) {
                // (a / 2) + 1 -> median a 2
                if divisor == 2 && next.op == OptOp::Add && &next.inputs[..] == &[ValueId::C_ONE, div.out] {
                    let spec = self.prepare_output(next.out);
                    let value_reg = self.materialize_value_(div.inputs[0]);
                    self.program.push(PrecompiledOp::MedianCursed2(spec.target_reg(), value_reg));
                    self.finalize_output(spec);
                    return 2; // Consumed Div, Add
                }
            }
        }

        self.lower_binary(div, |out, a, b| PrecompiledOp::Div(out, a, b), |out, a, c| {
            if c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = -(c.trailing_zeros() as i32) as i8;
                return Some(PrecompiledOp::ShiftConst(out, a, shift_amount));
            }
            Some(PrecompiledOp::DivConst(out, a, c.try_into().ok()?))
        }, |_, _, _| None);
        1
    }

    fn lower_mul(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| PrecompiledOp::Mul(out, a, b), |out, a, c| {
            if c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = c.trailing_zeros() as i8;
                return Some(PrecompiledOp::ShiftConst(out, a, shift_amount));
            }
            Some(PrecompiledOp::MulConst(out, a, c.try_into().ok()?))
        });
    }

    fn lower_digit_sum(&mut self, instrs: &[&OptInstr]) -> usize {
        let ds1 = instrs[0];
        assert_eq!(1, ds1.inputs.len());

        let input_reg = self.materialize_value_(ds1.inputs[0]);

        if let Some(&ds2) = instrs.get(1) {
            // digit_sum(digit_sum(x))
            if ds2.op == OptOp::DigitSum && &ds2.inputs[..] == &[ds1.out] {
                if let Some(&lensum) = instrs.get(2) {
                    // lensum(digit_sum(digit_sum(x)), digit_sum(x))
                    if lensum.op == OptOp::LenSum 
                        && (&lensum.inputs[..] == &[ds2.out, ds1.out] || &lensum.inputs[..] == &[ds1.out, ds2.out]) {
                        let spec = self.prepare_output(lensum.out);
                        self.program.push(PrecompiledOp::DigitSumDigitSumLensum(spec.target_reg(), input_reg));
                        self.finalize_output(spec);
                        return 3; // Consumed DigitSum, DigitSum, LenSum
                    }
                }

                let spec = self.prepare_output(ds2.out);
                self.program.push(PrecompiledOp::DigitSumTwice(spec.target_reg(), input_reg));
                self.finalize_output(spec);
                return 2; // Consumed DigitSum, DigitSum
            }
        }

        let input_range = self.g.val_range(ds1.inputs[0]);
        let spec = self.prepare_output(ds1.out);
        if *input_range.start() >= 0 && *input_range.end() < 10_000 {
            self.program.push(PrecompiledOp::DigitSumSmall(spec.target_reg(), input_reg));
        } else {
            self.program.push(PrecompiledOp::DigitSum(spec.target_reg(), input_reg));
        }
        self.finalize_output(spec);
        1
    }

    fn lower_unary<F>(&mut self, instr: &OptInstr, op: F)
    where
        F: Fn(RegId, RegId) -> PrecompiledOp<RegId>,
    {
        if instr.inputs.is_empty() {
            return;
        }

        let spec = self.prepare_output(instr.out);
        let input = self.materialize_value_(instr.inputs[0]);
        self.program.push(op(spec.target_reg(), input));
        self.finalize_output(spec);
    }

    fn lower_select(&mut self, instr: &OptInstr, condition: Condition<ValueId>) {
        debug_assert_eq!(instr.inputs.len(), 2, "select should have exactly two value inputs");
        let spec = self.prepare_output(instr.out);
        let lowered_condition = self.lower_condition(condition.clone());

        if let (Some(true_const), Some(false_const)) = (self.g.get_constant(instr.inputs[0]), self.g.get_constant(instr.inputs[1])) {
            // select(x == 0, 1, 0) -> BoolNot(x)
            if matches!(lowered_condition, Condition::EqConst(_, 0)) && true_const == 1 && false_const == 0 {
                let Condition::EqConst(val_reg, 0) = &lowered_condition else { unreachable!() };
                self.program.push(PrecompiledOp::BoolNot(spec.target_reg(), *val_reg));
                self.finalize_output(spec);
                return;
            }
            if matches!(lowered_condition, Condition::NeqConst(_, 0)) && true_const == 0 && false_const == 1 {
                let Condition::NeqConst(val_reg, 0) = &lowered_condition else { unreachable!() };
                self.program.push(PrecompiledOp::BoolNot(spec.target_reg(), *val_reg));
                self.finalize_output(spec);
                return;
            }
            
            // select(x == 0, 0, 1) -> Sgn(x) if x >= 0
            // or select(x != 0, 1, 0) -> Sgn(x) if x >= 0
            if (matches!(lowered_condition, Condition::EqConst(_, 0)) && true_const == 0 && false_const == 1)
                || (matches!(lowered_condition, Condition::NeqConst(_, 0)) && true_const == 1 && false_const == 0)
            {
                let cond_val = condition.regs().into_iter().find(|i| i.is_computed()).unwrap();
                let val_range = self.g.val_range(cond_val);
                if *val_range.start() >= 0 {
                    let val_reg = lowered_condition.regs().into_iter().next().unwrap();
                    self.program.push(PrecompiledOp::Sgn(spec.target_reg(), val_reg));
                    self.finalize_output(spec);
                    return;
                }
            }

            if false_const == 0 {
                if let Ok(true_i16) = true_const.try_into() {
                    self.program.push(PrecompiledOp::SelectConst0(spec.target_reg(), lowered_condition, true_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if true_const == 0 {
                if let Ok(false_i16) = false_const.try_into() {
                    self.program.push(PrecompiledOp::SelectConst0(spec.target_reg(), lowered_condition.neg(), false_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if let (Ok(true_i8), Ok(false_i8)) = (true_const.try_into(), false_const.try_into()) {
                self.program.push(PrecompiledOp::SelectConst(spec.target_reg(), lowered_condition, true_i8, false_i8));
                self.finalize_output(spec);
                return;
            }
        }

        let true_reg = self.materialize_value_(instr.inputs[0]);
        let false_reg = self.materialize_value_(instr.inputs[1]);

        self.program.push(PrecompiledOp::Select(spec.target_reg(), lowered_condition, true_reg, false_reg));
        self.finalize_output(spec);
    }

    fn lower_push(&mut self, instr: &OptInstr) {
        let mut remaining = instr.inputs.as_slice();
        
        while !remaining.is_empty() {
            let mut regs: SmallVec<[RegId; 7]> = SmallVec::new();
            
            // Try to materialize up to 7 values, stop if we run out of temp registers
            for &value in remaining.iter().take(7) {
                match self.materialize_value(value) {
                    Ok(reg) => regs.push(reg),
                    Err(()) => break, // Out of temp registers, emit what we have
                }
            }
            
            if regs.is_empty() {
                // No registers available at all - this shouldn't happen with proper register allocation
                panic!("ran out of temp registers completely in lower_push");
            }

            match regs.len() {
                1 => self.program.push(PrecompiledOp::Push(regs[0])),
                2 => self.program.push(PrecompiledOp::Push2(regs[0], regs[1])),
                3 => self.program.push(PrecompiledOp::Push3(regs[0], regs[1], regs[2])),
                4 => self.program.push(PrecompiledOp::Push4(regs[0], regs[1], regs[2], regs[3])),
                5 => self.program.push(PrecompiledOp::Push5(regs[0], regs[1], regs[2], regs[3], regs[4])),
                6 => self.program.push(PrecompiledOp::Push6(regs[0], regs[1], regs[2], regs[3], regs[4], regs[5])),
                7 => self.program.push(PrecompiledOp::Push7(regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6])),
                _ => unreachable!(),
            }

            remaining = &remaining[regs.len()..];
            self.temp_regs.clear();
        }
    }

    fn lower_pop(&mut self, instr: &OptInstr) {
        let spec = self.prepare_output(instr.out);
        self.program.push(PrecompiledOp::Pop(spec.target_reg()));
        self.finalize_output(spec);
    }

    fn lower_stack_swap(&mut self, instr: &OptInstr) {
        debug_assert_eq!(instr.inputs.len(), 2);
        let spec = self.prepare_output(instr.out);

        let index_reg = self.materialize_value_(instr.inputs[0]);
        let value_reg = self.materialize_value_(instr.inputs[1]);

        self.program.push(PrecompiledOp::StackSwap(spec.target_reg(), index_reg, value_reg, 0));
        self.finalize_output(spec);
    }

    fn lower_jump(&mut self, condition: Condition<ValueId>, target: BlockId) {
        let lowered = self.lower_condition(condition);
        self.program.push(PrecompiledOp::Jump(lowered, 0));
        self.jump_fixups.push((self.program.len() - 1, target));
    }

    fn lower_assert(&mut self, instr: &OptInstr, condition: Condition<ValueId>, error: OperationError) {
        let code = Self::encode_error(&error);

        let lowered_condition = self.lower_condition(condition);

        let arg_reg = if instr.inputs.len() > 0 {
            let id = instr.inputs[0];
            self.materialize_value_(id)
        } else {
            RegId(0) // undefined value
        };

        self.program.push(PrecompiledOp::Assert(lowered_condition, code, arg_reg));
    }

    fn lower_condition(
        &mut self,
        condition: Condition<ValueId>,
    ) -> Condition<RegId> {
        use Condition::*;
        fn i16conv(x: i64) -> Option<i16> {
            return x.try_into().ok()
        }
        match condition {
            Eq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    EqConst(self.materialize_value_(b), c)
                } else {
                    Eq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Neq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    NeqConst(self.materialize_value_(b), c)
                } else {
                    Neq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Lt(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a < b  where a is const  =>  b > const
                    GtConst(self.materialize_value_(b), c)
                } else {
                    Lt(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Leq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a <= b  where a is const  =>  b >= const
                    GeqConst(self.materialize_value_(b), c)
                } else {
                    Leq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Gt(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a > b  where a is const  =>  b < const
                    LtConst(self.materialize_value_(b), c)
                } else {
                    Gt(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Geq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a >= b  where a is const  =>  b <= const
                    LeqConst(self.materialize_value_(b), c)
                } else {
                    Geq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Divides(a, b) => {
                if let Some(c) = self.g.get_constant(b).and_then(|c| u16::try_from(c).ok()) {
                    DividesConst(self.materialize_value_(a), c)
                } else {
                    Divides(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            NotDivides(a, b) => {
                if let Some(c) = self.g.get_constant(b).and_then(|c| u16::try_from(c).ok()) {
                    NotDividesConst(self.materialize_value_(a), c)
                } else {
                    NotDivides(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            // Already const variants
            EqConst(a, c) => EqConst(self.materialize_value_(a), c),
            NeqConst(a, c) => NeqConst(self.materialize_value_(a), c),
            LtConst(a, c) => LtConst(self.materialize_value_(a), c),
            LeqConst(a, c) => LeqConst(self.materialize_value_(a), c),
            GtConst(a, c) => GtConst(self.materialize_value_(a), c),
            GeqConst(a, c) => GeqConst(self.materialize_value_(a), c),
            DividesConst(a, c) => DividesConst(self.materialize_value_(a), c),
            NotDividesConst(a, c) => NotDividesConst(self.materialize_value_(a), c),
            True => True,
            False => False,
        }
    }

    fn materialize_value(
        &mut self,
        value: ValueId,
    ) -> Result<RegId, ()> {
        // Check if we already have this value in a temp register
        if let Some(cached_reg) = self.temp_regs.get_cached(value) {
            return Ok(cached_reg);
        }

        let reg = if value.is_constant() {
            let constant = self.g.get_constant_(value);
            let reg = self.temp_regs.alloc().ok_or(())?;
            if constant >= i32::MIN as i64 && constant <= i32::MAX as i64 {
                self.program.push(PrecompiledOp::LoadConst(reg, constant as i32));
            } else {
                let idx = self.get_large_constant_index(constant);
                self.program.push(PrecompiledOp::LoadConst64(reg, idx));
            }
            self.temp_regs.insert_cache(value, reg);
            reg
        } else if let Some(location) = self.register_allocation.location(value) {
            match location {
                ValueLocation::Register(reg) => RegId(reg),
                ValueLocation::Spill(slot) => {
                    let reg = self.temp_regs.alloc().ok_or(())?;
                    self.program.push(PrecompiledOp::Unspill(reg, slot));
                    self.temp_regs.insert_cache(value, reg);
                    reg
                }
            }
        } else {
            panic!("value {:?} has no register allocation", value);
        };

        Ok(reg)
    }

    fn materialize_value_(&mut self, value: ValueId) -> RegId {
        self.materialize_value(value).expect("ran out of temp registers")
    }

    fn get_large_constant_index(&mut self, value: i64) -> u16 {
        if let Some(&idx) = self.large_constant_lookup.get(&value) {
            return idx;
        }

        let idx = self.large_constants.len();
        assert!(idx < u16::MAX as usize, "too many large constants");
        let idx_u16 = idx as u16;
        self.large_constants.push(value);
        self.large_constant_lookup.insert(value, idx_u16);
        idx_u16
    }

    fn prepare_output(&mut self, value: ValueId) -> OutputSpec {
        if !value.is_computed() {
            // Return a dummy temp register that will be discarded
            let reg = self.temp_regs.alloc().expect("ran out of temp registers");
            return OutputSpec::Register(reg);
        }

        match self.register_allocation.location(value) {
            Some(ValueLocation::Register(reg)) => OutputSpec::Register(RegId(reg)),
            Some(ValueLocation::Spill(slot)) => {
                let reg = self.temp_regs.alloc().expect("ran out of scratch registers for spill dest");
                OutputSpec::Spill { reg, slot }
            }
            None => panic!("no register allocation for output value {value}\n{allocation}", allocation = &self.register_allocation),
        }
    }

    fn finalize_output(&mut self, spec: OutputSpec) {
        if let OutputSpec::Spill { reg, slot } = spec {
            self.program.push(PrecompiledOp::Spill(slot, reg));
            self.temp_regs.release(reg);
        }
    }

    fn encode_error(error: &OperationError) -> u16 {
        use OperationError::*;
        match error {
            IntegerOverflow => 0,
            DivisionByZero => 1,
            InvalidArgumentForUniversal { .. } => 2,
            NegativeLength { .. } => 3,
            NegativeIterations { .. } => 4,
            NegativeBitCount { .. } => 5,
            NonpositiveLength { .. } => 6,
            NegativeInstructionIndex { .. } => 7,
            NegativePraiseCount { .. } => 8,
            QeqZeroEqualsZero => 9,
            ArgumentAMustBeNonNegative { .. } => 10,
            ArgumentBMustBeNonNegative { .. } => 11,
            ArgumentCMustBeNonNegative { .. } => 12,
            _ => panic!("Unsupported {error:?}"),
        }
    }

    fn finish(mut self) -> PrecompiledBlock {
        for (pos, target) in self.jump_fixups {
            let target_ip = *self
                .block_starts
                .get(&target)
                .unwrap_or_else(|| panic!("jump target block {:?} was not compiled", target));
            if let Some(PrecompiledOp::Jump(_, ref mut dest)) = self.program.get_mut(pos) {
                *dest = target_ip;
            } else {
                panic!("expected jump at position {}", pos);
            }
        }

        PrecompiledBlock {
            program: self.program.into_boxed_slice(),
            stack_space_required: 0,
            stack_values_required: 0,
            start_ip: self.g.blocks.first().map(|b| b.ksplang_start_ip).unwrap_or(0),
            large_constants: self.large_constants.into_boxed_slice(),
            ip2deopt: Box::new([]),
            deopts: self.deopts.into_boxed_slice(),
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
struct RegisterAllocation {
    locations: HashMap<ValueId, ValueLocation>,
}

impl RegisterAllocation {
    fn location(&self, value: ValueId) -> Option<ValueLocation> {
        self.locations.get(&value).copied()
    }
}

impl fmt::Display for RegisterAllocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut regs: BTreeMap<u8, BTreeSet<ValueId>> = BTreeMap::new();
        let mut spills: Vec<(u32, ValueId)> = Vec::new();

        for (&value, &location) in &self.locations {
            match location {
                ValueLocation::Register(reg) => { regs.entry(reg).or_default().insert(value); },
                ValueLocation::Spill(slot) => spills.push((slot, value)),
            }
        }

        spills.sort_by_key(|(slot, _)| *slot);

        writeln!(f, "RegisterAllocation {{")?;
        for (&value, &location) in &self.locations {
            writeln!(f, "    {value:05}   {location:?}")?
        }
        if !regs.is_empty() {
            writeln!(f, "  registers:")?;
            for (reg, values) in regs {
                writeln!(f, "    r{reg:02}: {values:?}")?;
            }
        }

        if !spills.is_empty() {
            writeln!(f, "  spills:")?;
            for (slot, value) in spills {
                writeln!(f, "    {slot:02}: {value}")?;
            }
        }

        write!(f, "}}")
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueLocation {
    Register(u8),
    Spill(u32),
}

const RESERVED_REG_COUNT: u32 = 8;
const TOTAL_REG_COUNT: u32 = u8::MAX as u32 + 1;
const ALLOCATABLE_REG_COUNT: u32 = TOTAL_REG_COUNT - RESERVED_REG_COUNT;
const FIRST_TEMP_REG: u8 = ALLOCATABLE_REG_COUNT as u8;

#[derive(Clone, Debug)]
struct TempRegPool {
    available: Vec<RegId>,
    cache: HashMap<ValueId, RegId>,
}

impl TempRegPool {
    fn new() -> Self {
        let available: Vec<RegId> = (FIRST_TEMP_REG..=u8::MAX).rev().map(RegId).collect();
        Self { available, cache: HashMap::new() }
    }

    fn alloc(&mut self) -> Option<RegId> {
        self.available.pop()
    }

    fn release(&mut self, reg: RegId) {
        if reg.0 >= FIRST_TEMP_REG {
            self.available.push(reg);
        }
    }

    fn clear(&mut self) {
        self.available.clear();
        self.available.extend((FIRST_TEMP_REG..=u8::MAX).rev().map(RegId));
        self.cache.clear();
    }

    fn get_cached(&self, value: ValueId) -> Option<RegId> {
        self.cache.get(&value).copied()
    }

    fn insert_cache(&mut self, value: ValueId, reg: RegId) {
        self.cache.insert(value, reg);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ValueSegment {
    from: InstrId,
    to: InstrId,
}

impl ValueSegment {
    fn overlap(&self, other: &ValueSegment) -> bool {
        debug_assert_eq!(self.from.block_id(), self.to.block_id());
        debug_assert_eq!(other.from.block_id(), other.to.block_id());
        if self.from.block_id() != other.from.block_id() {
            return false
        }
        let self_start = self.from.instr_ix();
        let self_end = self.to.instr_ix();
        let other_start = other.from.instr_ix();
        let other_end = other.to.instr_ix();

        !(self_end < other_start || other_end < self_start)
    }

    fn weight(&self) -> u64 {
        let start = self.from.instr_ix() as u64;
        let end = self.to.instr_ix() as u64;
        let span_size = end.saturating_add(1).saturating_sub(start);
        span_size.clamp(1, LONG_LIFETIME_WEIGHT)
    }
}

#[derive(Clone, Debug)]
struct ValueCandidate {
    value: ValueId,
    segments: BTreeMap<BlockId, ValueSegment>,
    weight: u64,
    use_count: usize,
}

#[allow(dead_code)]
fn allocate_registers(g: &GraphBuilder, reg_count: u32) -> RegisterAllocation {
    if reg_count == 0 {
        return RegisterAllocation::default();
    }

    assert!(reg_count <= u8::MAX as u32 + 1, "reg_count exceeds register file size");

    let lifetimes = analyze_value_lifetimes(g);

    let mut candidates: Vec<ValueCandidate> = lifetimes
        .ranges
        .iter()
        .filter(|(val, _)| val.is_computed())
        .filter_map(|(val, blocks)| {
            let segments: BTreeMap<BlockId, ValueSegment> =
                blocks.iter().map(|(&block, &(from, to))| (block, ValueSegment { from, to }))
                             .collect();
            if segments.is_empty() {
                return None;
            }
            let weight = segments.values().map(|seg| seg.weight()).sum::<u64>();
            let use_count = g.val_info(*val).map_or(0, |info| info.used_at.len());
            Some(ValueCandidate { value: *val, segments, weight, use_count })
        })
        .collect();

    candidates.sort_by_key(|a|
        (a.weight / cmp::max(a.use_count as u64, 1), usize::MAX - a.use_count, a.value));

    let mut register_segments: Vec<BTreeMap<BlockId, Vec<ValueSegment>>> = (0..reg_count).map(|_| BTreeMap::new()).collect();
    let mut allocation = RegisterAllocation::default();
    let mut next_spill_slot: u32 = 0;

    for candidate in candidates {
        let ValueCandidate { value, segments, weight: _, use_count: _ } = candidate;

        let mut placed = false;
        for (reg_index, reg_segments) in register_segments.iter_mut().enumerate() {
            if !has_conflict(reg_segments, &segments) {
                for (block, segment) in segments.iter() {
                    reg_segments.entry(*block).or_default().push(*segment);
                }
                allocation.locations.insert(value, ValueLocation::Register(reg_index as u8));
                placed = true;
                break;
            }
        }

        if !placed {
            allocation.locations.insert(value, ValueLocation::Spill(next_spill_slot));
            next_spill_slot += 1;
        }
    }

    allocation
}

#[allow(dead_code)]
fn has_conflict(existing: &BTreeMap<BlockId, Vec<ValueSegment>>, candidate: &BTreeMap<BlockId, ValueSegment>) -> bool {
    for (block, candidate_segment) in candidate {
        if let Some(existing_segments) = existing.get(block) {
            for present in existing_segments {
                if candidate_segment.overlap(present) {
                    return true;
                }
            }
        }
    }
    false
}

const LONG_LIFETIME_WEIGHT: u64 = 1_000_000;

#[allow(dead_code)]
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

#[allow(dead_code)]
fn remat_cost(g: &GraphBuilder, lr: &LiveRanges, max_cost: u32) -> HashMap<ValueId, HashMap<InstrId, u32>> {
    let mut rematerializable: HashMap<ValueId, (u32, SmallVec<[ValueId; 4]>)> = HashMap::new();
    let mut pulls_in: HashMap<(ValueId, InstrId), SmallVec<[ValueId;4]>> = HashMap::new();
    for v in g.values.values() {
        let Some(i) = v.assigned_at.and_then(|i| g.get_instruction(i)) else { continue; };
        // if i.effect != OpEffect::None && i.effect != OpEffect::MayFail { }
        let rmat_cost = match i.op {
            OptOp::BinNot | OptOp::ShiftR | OptOp::BoolNot | OptOp::Or | OptOp::And | OptOp::Xor | OptOp::Min | OptOp::Max | OptOp::AbsFactorial | OptOp::Sgn | OptOp::ShiftL | OptOp::DigitSum | OptOp::Add | OptOp::AbsSub | OptOp::Select(_)=>
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
    #[allow(dead_code)]
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

        // Also include values that are defined but never used (output-only values)
        for (&var, &def_at) in defined_at.iter() {
            if !last_use.contains_key(&var) {
                // Value is defined but not used locally - include it with single-instruction range
                result.push((InstrId(block.id, def_at), InstrId(block.id, def_at), var));
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
fn test_struct_size() {
    assert_eq!(core::mem::size_of::<Condition<u8>>(), 4);
    assert_eq!(core::mem::size_of::<PrecompiledOp<u8>>(), 8);
}

#[cfg(test)]
mod lowering_tests {
    use super::*;
    use crate::compiler::{cfg::GraphBuilder, ops::{OptOp, ValueId}};
    use std::ops::RangeInclusive;

    fn graph_with_param(range: RangeInclusive<i64>) -> (GraphBuilder, ValueId) {
        let mut g = GraphBuilder::new(0);

        let param = {
            let info = g.new_value();
            info.range = range;
            info.id
        };

        g.current_block_mut().parameters.push(param);
        (g, param)
    }

    fn compile_binary(op: OptOp<ValueId>, lhs_range: RangeInclusive<i64>, rhs_const: i64) -> Vec<PrecompiledOp<RegId>> {
        let (mut g, lhs) = graph_with_param(lhs_range);

        let rhs = g.store_constant(rhs_const);
        let (out, _instr) = g.push_instr(op, &[lhs, rhs], false, None, None);
        let (_out2, _instr2) = g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);
        println!("CFG: {g}");
        let block = PrecompiledBlock::from_cfg(&g);
        println!("{:?}", block);
        block.program.iter().cloned().collect()
    }

    #[test]
    fn mod_power_of_two_with_non_negative_input_lowers_to_and_const() {
        let program = compile_binary(OptOp::Mod, 0..=100, 8);
        assert!(program.iter().any(|op| matches!(op, PrecompiledOp::AndConst(_, _, 7))));
        assert!(!program.iter().any(|op| matches!(op, PrecompiledOp::ModConst(_, _, _))));
    }

    #[test]
    fn mod_with_possible_negative_input_keeps_mod_const() {
        let program = compile_binary(OptOp::Mod, -5..=5, 8);
        assert!(program.iter().any(|op| matches!(op, PrecompiledOp::ModConst(_, _, 8))));
        assert!(!program.iter().any(|op| matches!(op, PrecompiledOp::AndConst(_, _, _))));
    }

    #[test]
    fn mod_euclid_power_of_two_always_uses_and_const() {
        let program = compile_binary(OptOp::ModEuclid, -10..=10, 8);
        assert!(matches!(&program[..], [
            PrecompiledOp::AndConst(_, _, 7),
            PrecompiledOp::AddConst(_, _, 2),
        ]));
    }

    #[test]
    fn digit_sum_of_digit_sum_fuses_into_digit_sum_twice() {
        let (mut g, param) = graph_with_param(0..=99_999);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, second], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [PrecompiledOp::DigitSumTwice(_, _), PrecompiledOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn digit_sum_lensum_combo_fuses_into_digit_sum_digit_sum_lensum() {
        let (mut g, param) = graph_with_param(0..=1_000_000);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        let (lensum, _) = g.push_instr(OptOp::LenSum, &[second, first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, lensum], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [PrecompiledOp::DigitSumDigitSumLensum(_, _), PrecompiledOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn div_by_two_plus_one_fuses_into_median_cursed2() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [PrecompiledOp::MedianCursed2(_, _) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn div_by_two_plus_one_fuses_into_median_cursed2_no1() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        g.push_instr(OptOp::DigitSum, &[div_out], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [PrecompiledOp::ShiftConst(_, _, -1), PrecompiledOp::AddConst(_, _, 1), PrecompiledOp::DigitSum(_, _) ]), "{block}\n{:?}", block.program);
    }
    #[test]
    fn div_by_two_plus_one_fuses_into_median_cursed2_no() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        let (median_candidate, _) = g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, median_candidate], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [PrecompiledOp::ShiftConst(_, _, -1), PrecompiledOp::AddConst(_, _, 3) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_with_zero_false_branch_uses_select_const0() {
        let (mut g, cond) = graph_with_param(-5..=5);

        let true_val = g.store_constant(6);
        let false_val = g.store_constant(0);
        let condition = Condition::EqConst(cond, 0);
        let (out, _) = g.push_instr(OptOp::Select(condition), &[true_val, false_val], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, PrecompiledOp::SelectConst0(_, _, 6))));
    }

    #[test]
    fn select_with_small_constants_uses_select_const() {
        let (mut g, cond) = graph_with_param(-3..=3);

        let true_val = g.store_constant(3);
        let false_val = g.store_constant(-2);
        let condition = Condition::NeqConst(cond, 0);
        let (out, _) = g.push_instr(OptOp::Select(condition), &[true_val, false_val], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = PrecompiledBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, PrecompiledOp::SelectConst(_, _, 3, -2))));
    }
}

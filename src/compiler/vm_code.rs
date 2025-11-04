use core::fmt;
use std::{cmp, collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet}, fmt::Display, u32};
use arrayvec::ArrayVec;
use smallvec::{SmallVec, smallvec};

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
pub enum OsmibyteOp<TReg: Display> {
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

    Mov2(TReg, TReg, TReg, TReg), // (dst0 <- src0, dst1 <- src1) simultaneous move
    Mov3(TReg, TReg, TReg, TReg, TReg, TReg), // (dst0 <- src0, dst1 <- src1, dst2 <- src2)

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
    SelectConstReg(TReg, Condition<TReg>, i8, TReg), // a <- condition ? const : reg

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

impl<TReg: Display> OsmibyteOp<TReg> {
    pub fn replace_regs<TReg2: Display, F>(&self, f: F) -> OsmibyteOp<TReg2>
        where F: Fn(&TReg, bool) -> TReg2
    {
        match self {
            OsmibyteOp::Push(a) => OsmibyteOp::Push(f(a, false)),
            OsmibyteOp::Push2(a, b) => OsmibyteOp::Push2(f(a, false), f(b, false)),
            OsmibyteOp::Push3(a, b, c) => OsmibyteOp::Push3(f(a, false), f(b, false), f(c, false)),
            OsmibyteOp::Push4(a, b, c, d) => OsmibyteOp::Push4(f(a, false), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::Push5(a, b, c, d, e) => OsmibyteOp::Push5(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false)),
            OsmibyteOp::Push6(a, b, c, d, e, f_) => OsmibyteOp::Push6(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false), f(f_, false)),
            OsmibyteOp::Push7(a, b, c, d, e, f_, g) => OsmibyteOp::Push7(f(a, false), f(b, false), f(c, false), f(d, false), f(e, false), f(f_, false), f(g, false)),

            OsmibyteOp::Pop(a) => OsmibyteOp::Pop(f(a, true)),
            OsmibyteOp::Pop2(a, b) => OsmibyteOp::Pop2(f(a, true), f(b, true)),
            OsmibyteOp::Pop3(a, b, c) => OsmibyteOp::Pop3(f(a, true), f(b, true), f(c, true)),
            OsmibyteOp::Pop4(a, b, c, d) => OsmibyteOp::Pop4(f(a, true), f(b, true), f(c, true), f(d, true)),
            OsmibyteOp::PopSecond(a) => OsmibyteOp::PopSecond(f(a, true)),

            OsmibyteOp::Mov2(dst0, src0, dst1, src1) =>
                OsmibyteOp::Mov2(f(dst0, true), f(src0, false), f(dst1, true), f(src1, false)),
            OsmibyteOp::Mov3(dst0, src0, dst1, src1, dst2, src2) =>
                OsmibyteOp::Mov3(f(dst0, true), f(src0, false), f(dst1, true), f(src1, false), f(dst2, true), f(src2, false)),

            OsmibyteOp::Add(a, b, c) => OsmibyteOp::Add(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::AddConst(a, b, c) => OsmibyteOp::AddConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Sub(a, b, c) => OsmibyteOp::Sub(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::SubConst(a, b, c) => OsmibyteOp::SubConst(f(a, true), *b, f(c, false)),
            OsmibyteOp::AbsSub(a, b, c) => OsmibyteOp::AbsSub(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::AbsSubConst(a, b, c) => OsmibyteOp::AbsSubConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Mul(a, b, c) => OsmibyteOp::Mul(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MulConst(a, b, c) => OsmibyteOp::MulConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Div(a, b, c) => OsmibyteOp::Div(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::DivConst(a, b, c) => OsmibyteOp::DivConst(f(a, true), f(b, false), *c),
            OsmibyteOp::CursedDiv(a, b, c) => OsmibyteOp::CursedDiv(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::Mod(a, b, c) => OsmibyteOp::Mod(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::ModConst(a, b, c) => OsmibyteOp::ModConst(f(a, true), f(b, false), *c),
            OsmibyteOp::ModEuclid(a, b, c) => OsmibyteOp::ModEuclid(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::ModEuclidConst(a, b, c) => OsmibyteOp::ModEuclidConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Tetration(a, b, c) => OsmibyteOp::Tetration(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::Funkcia(a, b, c) => OsmibyteOp::Funkcia(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::Max(a, b, c) => OsmibyteOp::Max(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MaxConst(a, b, c) => OsmibyteOp::MaxConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Min(a, b, c) => OsmibyteOp::Min(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MinConst(a, b, c) => OsmibyteOp::MinConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Clamp(a, b, c, d) => OsmibyteOp::Clamp(f(a, true), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::ClampConst(a, b, c, d) => OsmibyteOp::ClampConst(f(a, true), f(b, false), *c, *d),
            OsmibyteOp::Sgn(a, b) => OsmibyteOp::Sgn(f(a, true), f(b, false)),
            OsmibyteOp::AbsFactorial(a, b) => OsmibyteOp::AbsFactorial(f(a, true), f(b, false)),
            OsmibyteOp::Lensum(a, b, c) => OsmibyteOp::Lensum(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::Universal2(a, b, c, d) => OsmibyteOp::Universal2(f(a, true), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::Universal1(a, b, c) => OsmibyteOp::Universal1(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::And(a, b, c) => OsmibyteOp::And(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::AndConst(a, b, c) => OsmibyteOp::AndConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Or(a, b, c) => OsmibyteOp::Or(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::OrConst(a, b, c) => OsmibyteOp::OrConst(f(a, true), f(b, false), *c),
            OsmibyteOp::Xor(a, b, c) => OsmibyteOp::Xor(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::XorConst(a, b, c) => OsmibyteOp::XorConst(f(a, true), f(b, false), *c),
            OsmibyteOp::ShiftL(a, b, c) => OsmibyteOp::ShiftL(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::ShiftR(a, b, c) => OsmibyteOp::ShiftR(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::ShiftConst(a, b, c) => OsmibyteOp::ShiftConst(f(a, true), f(b, false), *c),

            OsmibyteOp::BinNot(a, b) => OsmibyteOp::BinNot(f(a, true), f(b, false)),
            OsmibyteOp::BoolNot(a, b) => OsmibyteOp::BoolNot(f(a, true), f(b, false)),

            OsmibyteOp::SelectConst(a, condition, b, c) =>
                OsmibyteOp::SelectConst(f(a, true), condition.replace_regs(|r| f(r, false)), *b, *c),
            OsmibyteOp::SelectConst0(a, condition, b) =>
                OsmibyteOp::SelectConst0(f(a, true), condition.replace_regs(|r| f(r, false)), *b),
            OsmibyteOp::SelectConstReg(a, condition, b, c) =>
                OsmibyteOp::SelectConstReg(f(a, true), condition.replace_regs(|r| f(r, false)), *b, f(c, false)),
            OsmibyteOp::Select(a, condition, c, d) =>
                OsmibyteOp::Select(f(a, true), condition.replace_regs(|r| f(r, false)), f(c, false), f(d, false)),

            OsmibyteOp::DigitSum(a, b) => OsmibyteOp::DigitSum(f(a, true), f(b, false)),
            OsmibyteOp::DigitSumSmall(a, b) => OsmibyteOp::DigitSumSmall(f(a, true), f(b, false)),
            OsmibyteOp::DigitSumTwice(a, b) => OsmibyteOp::DigitSumTwice(f(a, true), f(b, false)),
            OsmibyteOp::DigitSumDigitSumLensum(a, b) => OsmibyteOp::DigitSumDigitSumLensum(f(a, true), f(b, false)),
            OsmibyteOp::Gcd(a, b, c) => OsmibyteOp::Gcd(f(a, true), f(b, false), f(c, false)),

            OsmibyteOp::StackSwap(a, b, c, depth) => OsmibyteOp::StackSwap(f(a, true), f(b, false), f(c, false), *depth),
            OsmibyteOp::StackRead(a, b, depth) => OsmibyteOp::StackRead(f(a, true), f(b, false), *depth),
            OsmibyteOp::StackWrite(a, b, depth) => OsmibyteOp::StackRead(f(a, false), f(b, false), *depth),

            OsmibyteOp::LoadConst(a, v) => OsmibyteOp::LoadConst(f(a, true), *v),
            OsmibyteOp::LoadConst64(a, ix) => OsmibyteOp::LoadConst64(f(a, true), *ix),
            OsmibyteOp::LoadConstPow2Offset(a, pow2, offset) => OsmibyteOp::LoadConstPow2Offset(f(a, true), *pow2, *offset),

            OsmibyteOp::Jump(condition, ip) => OsmibyteOp::Jump(condition.replace_regs(|r| f(r, false)), *ip),

            OsmibyteOp::Assert(condition, code, arg) => OsmibyteOp::Assert(condition.replace_regs(|r| f(r, false)), *code, f(arg, false)),
            OsmibyteOp::DeoptAssert(condition, id) => OsmibyteOp::DeoptAssert(condition.replace_regs(|r| f(r, false)), *id),
            OsmibyteOp::Done(ip) => OsmibyteOp::Done(*ip),

            OsmibyteOp::Median2(a, b, c) => OsmibyteOp::Median2(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MedianCursed2(a, b) => OsmibyteOp::MedianCursed2(f(a, true), f(b, false)),
            OsmibyteOp::Median3(a, b, c, d) => OsmibyteOp::Median3(f(a, true), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::MedianCursed3(a, b, c) => OsmibyteOp::MedianCursed3(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MedianCursed5(a, b, c, d, e) => OsmibyteOp::MedianCursed5(f(a, true), f(b, false), f(c, false), f(d, false), f(e, false)),

            OsmibyteOp::KsplangOp(op) => OsmibyteOp::KsplangOp(*op),
            OsmibyteOp::KsplangOpWithArg(op, a) => OsmibyteOp::KsplangOpWithArg(*op, f(a, false)),

            OsmibyteOp::KsplangOpsIncrement(inc) => OsmibyteOp::KsplangOpsIncrement(*inc),
            OsmibyteOp::KsplangOpsIncrementVar(inc) => OsmibyteOp::KsplangOpsIncrementVar(f(inc, false)),
            OsmibyteOp::KsplangOpsIncrementCond(cond, inc) => OsmibyteOp::KsplangOpsIncrementCond(cond.replace_regs(|r| f(r, false)), *inc),

            OsmibyteOp::Spill(value, a) => OsmibyteOp::Spill(*value, f(a, false)),
            OsmibyteOp::Unspill(a, value) => OsmibyteOp::Unspill(f(a, true), *value),
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
    pub additional_opcodes: Box<[OsmibyteOp<RegId>]>,
    pub stack_reconstruction: SmallVec<[RegId; 16]>,
    pub ip: usize,
    pub ksplang_ops_increment: u32
}

pub struct OsmibytecodeBlock {
    pub program: Box<[OsmibyteOp<RegId>]>,
    pub stack_space_required: u32,
    pub stack_values_required: u32,
    pub start_ip: usize,
    pub large_constants: Box<[i64]>,
    pub ip2deopt: Box<[(u32, u32)]>, // IP -> deopt index ordered mapping
    pub deopts: Box<[DeoptInfo]>
}

impl fmt::Display for OsmibytecodeBlock {
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

impl fmt::Debug for OsmibytecodeBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

impl OsmibytecodeBlock {
    pub fn from_cfg(g: &GraphBuilder) -> OsmibytecodeBlock {
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
    program: Vec<OsmibyteOp<RegId>>,
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
            Add => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Add(out, a, b), |out, a, c| Some(OsmibyteOp::AddConst(out, a, c.try_into().ok()?))),
            Mul => self.lower_mul(instr),
            Sub => self.lower_binary(instr, |out, a, b| OsmibyteOp::Sub(out, a, b), |_, _, _| None, |out, c, b| Some(OsmibyteOp::SubConst(out, c.try_into().ok()?, b))),
            AbsSub => self.lower_variadic(instr, |out, a, b| OsmibyteOp::AbsSub(out, a, b), |out, a, c| Some(OsmibyteOp::AbsSubConst(out, a, c.try_into().ok()?))),
            Div => return self.lower_div(instrs),
            CursedDiv => self.lower_binary(instr, |out, a, b| OsmibyteOp::CursedDiv(out, a, b), |_, _, _| None, |_, _, _| None),
            Mod => {
                let lhs_range = self.g.val_range_at(instr.inputs[0], instr.id);
                let lhs_non_negative = *lhs_range.start() >= 0;
                self.lower_binary(instr, |out, a, b| OsmibyteOp::Mod(out, a, b), {
                    move |out, a, c| {
                        let c: i32 = c.try_into().ok()?;
                        if c > 0 && (c as u64).is_power_of_two() && lhs_non_negative {
                            Some(OsmibyteOp::AndConst(out, a, c.wrapping_sub(1)))
                        } else {
                            Some(OsmibyteOp::ModConst(out, a, c))
                        }
                    }
                }, |_, _, _| None);
            }
            ModEuclid => {
                self.lower_binary(instr, |out, a, b| OsmibyteOp::ModEuclid(out, a, b), move |out, a, c| {
                    let c: i32 = c.try_into().ok()?;
                    if c > 0 && (c as u64).is_power_of_two() {
                        Some(OsmibyteOp::AndConst(out, a, c.wrapping_sub(1)))
                    } else {
                        Some(OsmibyteOp::ModEuclidConst(out, a, c))
                    }
                }, |_, _, _| None);
            }
            Tetration => self.lower_binary(instr, |out, a, b| OsmibyteOp::Tetration(out, a, b), |_, _, _| None, |_, _, _| None),
            Funkcia => self.lower_binary(instr, |out, a, b| OsmibyteOp::Funkcia(out, a, b), |_, _, _| None, |_, _, _| None),
            Max => consumed = self.lower_max(instrs),
            Min => self.lower_min(instr),
            Sgn => self.lower_unary(instr, |out, a| OsmibyteOp::Sgn(out, a)),
            AbsFactorial => self.lower_unary(instr, |out, a| OsmibyteOp::AbsFactorial(out, a)),
            LenSum => self.lower_binary(instr, |out, a, b| OsmibyteOp::Lensum(out, a, b), |_, _, _| None, |_, _, _| None),
            And => self.lower_variadic(instr, |out, a, b| OsmibyteOp::And(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::AndConst(out, a, mask))),
            Or => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Or(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::OrConst(out, a, mask))),
            Xor => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Xor(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::XorConst(out, a, mask))),
            ShiftL => self.lower_binary(instr, |out, a, b| OsmibyteOp::ShiftL(out, a, b), |out, a, c| Some(OsmibyteOp::ShiftConst(out, a, c.try_into().ok()?)), |_, _, _| None),
            ShiftR => self.lower_binary(instr, |out, a, b| OsmibyteOp::ShiftR(out, a, b), |out, a, c: i64| Some(OsmibyteOp::ShiftConst(out, a, c.checked_neg()?.try_into().ok()?)), |_, _, _| None),
            BinNot => self.lower_unary(instr, |out, a| OsmibyteOp::BinNot(out, a)),
            BoolNot => self.lower_unary(instr, |out, a| OsmibyteOp::BoolNot(out, a)),
            Select(condition) => self.lower_select(instr, condition.clone()),
            DigitSum => consumed = self.lower_digit_sum(instrs),
            Gcd => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Gcd(out, a, b), |_, _, _| None),
            Push => self.lower_push(instr),
            Pop => self.lower_pop(instr),
            StackSwap => self.lower_stack_swap(instr),
            Jump(condition, target) => self.lower_jump(instr, condition.clone(), *target),
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
        F: Fn(RegId, RegId, RegId) -> OsmibyteOp<RegId>,
        FC: Fn(RegId, RegId, i64) -> Option<OsmibyteOp<RegId>>,
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
            self.program.push(OsmibyteOp::AddConst(dest, first_reg, 0));
        }

        self.finalize_output(spec);
    }

    fn lower_binary<F, FC1, FC2>(&mut self, instr: &OptInstr, op: F, op_const_rhs: FC1, op_const_lhs: FC2)
    where
        F: Fn(RegId, RegId, RegId) -> OsmibyteOp<RegId>,
        FC1: Fn(RegId, RegId, i64) -> Option<OsmibyteOp<RegId>>,
        FC2: Fn(RegId, i64, RegId) -> Option<OsmibyteOp<RegId>>,
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
                if min.op == OptOp::Min && min.inputs.len() == 2 && min.inputs[1] == max.out &&
                    self.used_exactly_at(max.out, &[min.id])
                {
                    if let Some(hi_const) = self.g.get_constant(min.inputs[0]) {
                        assert!(lo_const < hi_const);
                        if let (Ok(lo_i16), Ok(hi_i16)) = (lo_const.try_into(), hi_const.try_into()) {
                            let spec = self.prepare_output(min.out);
                            let value_reg = self.materialize_value_(max.inputs[1]);
                            self.program.push(OsmibyteOp::ClampConst(spec.target_reg(), value_reg, lo_i16, hi_i16));
                            self.finalize_output(spec);
                            return 2; // Consumed Max, Min
                        }
                    }
                }
            }
        }

        self.lower_variadic(max, |out, a, b| OsmibyteOp::Max(out, a, b), |out, a, c| Some(OsmibyteOp::MaxConst(out, a, c.try_into().ok()?)));
        1
    }

    fn lower_min(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| OsmibyteOp::Min(out, a, b), |out, a, c| Some(OsmibyteOp::MinConst(out, a, c.try_into().ok()?)));
    }

    fn lower_div(&mut self, instrs: &[&OptInstr]) -> usize {
        let div = instrs[0];
        assert_eq!(2, div.inputs.len());

        if let Some(divisor) = self.g.get_constant(div.inputs[1]) {
            if let Some(&next) = instrs.get(1) {
                // (a / 2) + 1 -> median a 2
                if divisor == 2 &&
                    next.op == OptOp::Add && &next.inputs[..] == &[ValueId::C_ONE, div.out] &&
                    self.used_exactly_at(div.out, &[next.id])
                {
                    let spec = self.prepare_output(next.out);
                    let value_reg = self.materialize_value_(div.inputs[0]);
                    self.program.push(OsmibyteOp::MedianCursed2(spec.target_reg(), value_reg));
                    self.finalize_output(spec);
                    return 2; // Consumed Div, Add
                }
            }
        }

        self.lower_binary(div, |out, a, b| OsmibyteOp::Div(out, a, b), |out, a, c| {
            if c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = -(c.trailing_zeros() as i32) as i8;
                return Some(OsmibyteOp::ShiftConst(out, a, shift_amount));
            }
            Some(OsmibyteOp::DivConst(out, a, c.try_into().ok()?))
        }, |_, _, _| None);
        1
    }

    fn lower_mul(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| OsmibyteOp::Mul(out, a, b), |out, a, c| {
            if c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = c.trailing_zeros() as i8;
                return Some(OsmibyteOp::ShiftConst(out, a, shift_amount));
            }
            Some(OsmibyteOp::MulConst(out, a, c.try_into().ok()?))
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
                        && (&lensum.inputs[..] == &[ds2.out, ds1.out] || &lensum.inputs[..] == &[ds1.out, ds2.out])
                        && self.used_exactly_at(ds2.out, &[lensum.id])
                        && self.used_exactly_at(ds1.out, &[lensum.id, ds2.id])
                    {
                        let spec = self.prepare_output(lensum.out);
                        self.program.push(OsmibyteOp::DigitSumDigitSumLensum(spec.target_reg(), input_reg));
                        self.finalize_output(spec);
                        return 3; // Consumed DigitSum, DigitSum, LenSum
                    }
                }

                if self.used_exactly_at(ds1.out, &[ds2.id]) {
                    let spec = self.prepare_output(ds2.out);
                    self.program.push(OsmibyteOp::DigitSumTwice(spec.target_reg(), input_reg));
                    self.finalize_output(spec);
                    return 2; // Consumed DigitSum, DigitSum
                }
            }
        }

        let input_range = self.g.val_range(ds1.inputs[0]);
        let spec = self.prepare_output(ds1.out);
        if *input_range.start() >= 0 && *input_range.end() < 10_000 {
            self.program.push(OsmibyteOp::DigitSumSmall(spec.target_reg(), input_reg));
        } else {
            self.program.push(OsmibyteOp::DigitSum(spec.target_reg(), input_reg));
        }
        self.finalize_output(spec);
        1
    }

    fn lower_unary<F>(&mut self, instr: &OptInstr, op: F)
    where
        F: Fn(RegId, RegId) -> OsmibyteOp<RegId>,
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
                self.program.push(OsmibyteOp::BoolNot(spec.target_reg(), *val_reg));
                self.finalize_output(spec);
                return;
            }
            if matches!(lowered_condition, Condition::NeqConst(_, 0)) && true_const == 0 && false_const == 1 {
                let Condition::NeqConst(val_reg, 0) = &lowered_condition else { unreachable!() };
                self.program.push(OsmibyteOp::BoolNot(spec.target_reg(), *val_reg));
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
                    self.program.push(OsmibyteOp::Sgn(spec.target_reg(), val_reg));
                    self.finalize_output(spec);
                    return;
                }
            }

            if false_const == 0 {
                if let Ok(true_i16) = true_const.try_into() {
                    self.program.push(OsmibyteOp::SelectConst0(spec.target_reg(), lowered_condition, true_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if true_const == 0 {
                if let Ok(false_i16) = false_const.try_into() {
                    self.program.push(OsmibyteOp::SelectConst0(spec.target_reg(), lowered_condition.neg(), false_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if let (Ok(true_i8), Ok(false_i8)) = (true_const.try_into(), false_const.try_into()) {
                self.program.push(OsmibyteOp::SelectConst(spec.target_reg(), lowered_condition, true_i8, false_i8));
                self.finalize_output(spec);
                return;
            }
        } else if let Some(true_const) = self.g.get_constant(instr.inputs[0]).and_then(|v| v.try_into().ok()) {
            // True branch is constant, false branch is register or out of range
            let false_reg = self.materialize_value_(instr.inputs[1]);
            self.program.push(OsmibyteOp::SelectConstReg(spec.target_reg(), lowered_condition, true_const, false_reg));
            self.finalize_output(spec);
            return;
        } else if let Some(false_const) = self.g.get_constant(instr.inputs[1]).and_then(|v| v.try_into().ok()) {
            let true_reg = self.materialize_value_(instr.inputs[0]);
            self.program.push(OsmibyteOp::SelectConstReg(spec.target_reg(), lowered_condition.neg(), false_const, true_reg));
            self.finalize_output(spec);
            return;
        }

        let true_reg = self.materialize_value_(instr.inputs[0]);
        let false_reg = self.materialize_value_(instr.inputs[1]);

        self.program.push(OsmibyteOp::Select(spec.target_reg(), lowered_condition, true_reg, false_reg));
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
                1 => self.program.push(OsmibyteOp::Push(regs[0])),
                2 => self.program.push(OsmibyteOp::Push2(regs[0], regs[1])),
                3 => self.program.push(OsmibyteOp::Push3(regs[0], regs[1], regs[2])),
                4 => self.program.push(OsmibyteOp::Push4(regs[0], regs[1], regs[2], regs[3])),
                5 => self.program.push(OsmibyteOp::Push5(regs[0], regs[1], regs[2], regs[3], regs[4])),
                6 => self.program.push(OsmibyteOp::Push6(regs[0], regs[1], regs[2], regs[3], regs[4], regs[5])),
                7 => self.program.push(OsmibyteOp::Push7(regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6])),
                _ => unreachable!(),
            }

            remaining = &remaining[regs.len()..];
            self.temp_regs.clear();
        }
    }

    fn lower_pop(&mut self, instr: &OptInstr) {
        let spec = self.prepare_output(instr.out);
        self.program.push(OsmibyteOp::Pop(spec.target_reg()));
        self.finalize_output(spec);
    }

    fn lower_stack_swap(&mut self, instr: &OptInstr) {
        debug_assert_eq!(instr.inputs.len(), 2);
        let spec = self.prepare_output(instr.out);

        let index_reg = self.materialize_value_(instr.inputs[0]);
        let value_reg = self.materialize_value_(instr.inputs[1]);

        self.program.push(OsmibyteOp::StackSwap(spec.target_reg(), index_reg, value_reg, 0));
        self.finalize_output(spec);
    }

    fn lower_jump(&mut self, instr: &OptInstr, condition: Condition<ValueId>, target: BlockId) {
        if condition == Condition::False { return }

        let condition = self.lower_condition(condition);

        let target_block = self.g.block_(target);
        assert_eq!(target_block.parameters.len(), instr.inputs.len(), "jump {instr} has mismatched argument count");

        let mut register_moves: Vec<(RegId, RegId)> = Vec::new();
        let mut unspills: Vec<(u32, RegId)> = Vec::new();
        let mut spills: Vec<(ValueId, u32)> = Vec::new();
        let mut consts: Vec<(i64, RegId)> = Vec::new();

        for (param, arg) in target_block.parameters.iter().zip(instr.inputs.iter()) {
            match self.register_allocation.location(*param) {
                Some(ValueLocation::Register(dest_reg)) => {
                    if arg.is_constant() {
                        consts.push((self.g.get_constant_(*arg), RegId(dest_reg)));
                        continue;
                    }
                    match self.register_allocation.location(*arg) {
                        Some(ValueLocation::Register(src)) if src == dest_reg => {}
                        Some(ValueLocation::Register(src)) => register_moves.push((RegId(src), RegId(dest_reg))),
                        Some(ValueLocation::Spill(src_spill)) => unspills.push((src_spill, RegId(dest_reg))),
                        None => panic!()
                    }
                }
                Some(ValueLocation::Spill(slot)) => {
                    if self.register_allocation.location(*arg) != Some(ValueLocation::Spill(slot)) {
                        spills.push((*arg, slot))
                    }
                },
                None => {}
            }
        }

        let jump_fixup = if condition != Condition::True && register_moves.len() + unspills.len() + spills.len() + consts.len() > 0 {
            // first check condition, then move values
            self.program.push(OsmibyteOp::Jump(condition.clone().neg(), 0));
            self.temp_regs.clear();
            Some(self.program.len() - 1)
        } else {
            None
        };

        for (value, slot) in spills {
            let reg = self.materialize_value_(value);
            self.program.push(OsmibyteOp::Spill(slot, reg));
            self.temp_regs.release(reg);
        }

        self.emit_register_moves(register_moves);

        for (slot, reg) in unspills {
            self.program.push(OsmibyteOp::Unspill(reg, slot));
        }

        for (value, reg) in consts {
            self.load_constant(reg, value);
        }

        if let Some(jump_fixup) = jump_fixup {
            let current_loc = self.program.len().try_into().unwrap();
            let OsmibyteOp::Jump(_, target) = &mut self.program[jump_fixup] else { panic!() };
            *target = current_loc;
            // condition is already in the first jump
            self.program.push(OsmibyteOp::Jump(Condition::True, 0))
        } else {
            self.program.push(OsmibyteOp::Jump(condition, 0));
        }
        self.jump_fixups.push((self.program.len() - 1, target));
    }

    fn emit_register_moves(&mut self, mut moves: Vec<(RegId, RegId)>) {
        moves.retain(|(from, to)| from != to);
        let mut inputs: BTreeMap<RegId, usize> = BTreeMap::new();
        for (from, _to) in &moves {
            *inputs.entry(*from).or_default() += 1;
        }

        let mut sequential_moves = vec![];
        while let Some(mv_ix) = moves.iter().position(|(_from, to)| *inputs.get(to).unwrap_or(&0) == 0) {
            let mv = moves.swap_remove(mv_ix);
            *inputs.get_mut(&mv.0).unwrap() -= 1;
            sequential_moves.push(mv);
        }
        let mut atomic_moves = moves; // rest has some cycles, we need to be careful
        assert_ne!(1, atomic_moves.len());
        // sequence of swaps
        let mut reg_remap = BTreeMap::new();
        while let Some((from, to)) = atomic_moves.pop() {
            let from = *reg_remap.get(&from).unwrap_or(&from);
            if from == to {
                continue
            }
            self.program.push(OsmibyteOp::Mov2(to, from, from, to));
            // `from` is now temporarily swapped in `to`
            reg_remap.insert(from, to);
        }
        for chunk in sequential_moves.chunks(3) {
            match chunk {
                [a, b, c] => self.program.push(OsmibyteOp::Mov3(a.1, a.0, b.1, b.0, c.1, c.0)),
                [a, b] => self.program.push(OsmibyteOp::Mov2(a.1, a.0, b.1, b.0)),
                [a] => self.program.push(OsmibyteOp::OrConst(a.1, a.0, 0)),
                wtf => unreachable!("{wtf:?}")
            }
        }
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

        self.program.push(OsmibyteOp::Assert(lowered_condition, code, arg_reg));
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

    fn load_constant(&mut self, reg: RegId, value: i64) {
        if value >= i32::MIN as i64 && value <= i32::MAX as i64 {
            self.program.push(OsmibyteOp::LoadConst(reg, value as i32));
        } else { // TODO: pow2 offset
            let idx = self.get_large_constant_index(value);
            self.program.push(OsmibyteOp::LoadConst64(reg, idx));
        }
    }

    fn materialize_value(&mut self, value: ValueId) -> Result<RegId, ()> {
        // Check if we already have this value in a temp register
        if let Some(cached_reg) = self.temp_regs.get_cached(value) {
            return Ok(cached_reg);
        }

        let reg = if value.is_constant() {
            let constant = self.g.get_constant_(value);
            let reg = self.temp_regs.alloc().ok_or(())?;
            self.load_constant(reg, constant);
            self.temp_regs.insert_cache(value, reg);
            reg
        } else if let Some(location) = self.register_allocation.location(value) {
            match location {
                ValueLocation::Register(reg) => RegId(reg),
                ValueLocation::Spill(slot) => {
                    let reg = self.temp_regs.alloc().ok_or(())?;
                    self.program.push(OsmibyteOp::Unspill(reg, slot));
                    self.temp_regs.insert_cache(value, reg);
                    reg
                }
            }
        } else {
            panic!("value {:?} has no register allocation", value);
        };

        Ok(reg)
    }

    fn get_usages(&'_ self, value: ValueId) -> Option<&'_ BTreeSet<InstrId>> {
        if let Some(inf) = self.g.values.get(&value) {
            Some(&inf.used_at)
        } else {
            None
        }
    }

    fn used_exactly_at(&self, value: ValueId, at: &[InstrId]) -> bool {
        let Some(used_at) = self.get_usages(value) else {
            return false;
        };
        return used_at.len() == at.len() && at.iter().all(|i| used_at.contains(i));
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
            self.program.push(OsmibyteOp::Spill(slot, reg));
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

    fn finish(mut self) -> OsmibytecodeBlock {
        for (pos, target) in self.jump_fixups {
            let target_ip = *self
                .block_starts
                .get(&target)
                .unwrap_or_else(|| panic!("jump target block {:?} was not compiled", target));
            if let Some(OsmibyteOp::Jump(_, ref mut dest)) = self.program.get_mut(pos) {
                *dest = target_ip;
            } else {
                panic!("expected jump at position {}", pos);
            }
        }

        OsmibytecodeBlock {
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
    locations: BTreeMap<ValueId, ValueLocation>,
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
        debug_assert!(self_start <= self_end);
        let other_start = other.from.instr_ix();
        let other_end = other.to.instr_ix();
        debug_assert!(other_start <= other_end);

        self_start < other_end && other_start < self_end
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
    has_phi_friends: bool,
}

fn allocate_registers(g: &GraphBuilder, reg_count: u32) -> RegisterAllocation {
    if reg_count == 0 {
        return RegisterAllocation::default();
    }

    assert!(reg_count <= u8::MAX as u32 + 1, "reg_count exceeds register file size");

    let phi_friends = equivalence_preferences(g);

    let lifetimes = analyze_value_lifetimes(g);
    println!("Lifetimes: {lifetimes:?}");

    let mut value_segments: BTreeMap<ValueId, BTreeMap<BlockId, ValueSegment>> = BTreeMap::new();
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
            value_segments.insert(*val, segments.clone());
            let weight = segments.values().map(|seg| seg.weight()).sum::<u64>();
            let use_count = g.val_info(*val).map_or(0, |info| info.used_at.len());
            let has_phi_friends = phi_friends
                .range((*val, ValueId(i32::MIN))..=(*val, ValueId(i32::MAX)))
                .next().is_some();
            Some(ValueCandidate { value: *val, segments, weight, use_count, has_phi_friends })
        })
        .collect();

    candidates.sort_by_key(|a|
        (a.weight / cmp::max(a.use_count as u64, 1), usize::MAX - a.use_count, a.value));

    let mut register_segments: Vec<BTreeMap<BlockId, Vec<ValueSegment>>> = (0..reg_count).map(|_| BTreeMap::new()).collect();
    let mut register_values: Vec<BTreeSet<ValueId>> = (0..reg_count).map(|_| BTreeSet::new()).collect();
    let mut allocation = RegisterAllocation::default();
    let mut next_spill_slot: u32 = 0;

    for candidate in candidates {
        let ValueCandidate { value, segments, weight: _, use_count: _, has_phi_friends } = candidate;
        if allocation.locations.contains_key(&value) {
            continue;
        }

        let mut options = register_segments.iter().enumerate()
            .filter(|(_reg_ix, reg_segments)| !has_conflict(reg_segments, &segments))
            .map(|(reg_ix, _)| reg_ix);

        let (chosen_reg, merged_friends) = if !has_phi_friends {
            (options.next(), smallvec![])
        } else {
            let mut candidate_regs: BTreeSet<usize> = options.collect();
            println!("Choosing regs for {value} out of {candidate_regs:?} with friends {phi_friends:?}");
            let merged_friends = reduce_registers_with_phi_friends(
                value,
                &mut candidate_regs,
                &phi_friends,
                &allocation,
                &value_segments,
                &register_segments,
            );
            println!("Chosen {candidate_regs:?} with friends {merged_friends:?}");
            (candidate_regs.into_iter().next(), merged_friends)
        };
        assert!(!merged_friends.contains(&value));

        let Some(chosen_reg) = chosen_reg else {
            allocation.locations.insert(value, ValueLocation::Spill(next_spill_slot)); // TODO same spill for friends?
            next_spill_slot += 1;
            continue;
        };

        for val in [value].into_iter().chain(merged_friends.clone()) {
            assert!(!allocation.locations.contains_key(&val));

            let segments = &value_segments[&val];
            assert!(!has_conflict(&register_segments[chosen_reg], segments),
                    "Unexpected conflicts between reg {chosen_reg} and {val}:\nAllocating {value} with {merged_friends:?}\nSegments: {value_segments:?}\nCFG: {g}");

            for (block, segment) in segments.iter() {
                register_segments[chosen_reg].entry(*block).or_default().push(*segment);
            }
            allocation.locations.insert(val, ValueLocation::Register(chosen_reg as u8));
            register_values[chosen_reg].insert(val);
        }
    }

    allocation
}

fn has_conflict(existing: &BTreeMap<BlockId, Vec<ValueSegment>>, candidate: &BTreeMap<BlockId, ValueSegment>) -> bool {
    for (block, candidate_segment) in candidate {
        if let Some(existing_segments) = existing.get(block) {
            for present in existing_segments {
                if candidate_segment.overlap(present) {
                    println!("{existing:?} has conflict with {candidate:?}");
                    return true;
                }
            }
        }
    }
    false
}

fn reduce_registers_with_phi_friends(
    value: ValueId,
    candidate_regs: &mut BTreeSet<usize>,
    phi_friends: &BTreeMap<(ValueId, ValueId), u32>,
    allocation: &RegisterAllocation,
    value_segments: &BTreeMap<ValueId, BTreeMap<BlockId, ValueSegment>>,
    register_segments: &[BTreeMap<BlockId, Vec<ValueSegment>>],
) -> SmallVec<[ValueId; 8]> {
    if candidate_regs.is_empty() { return smallvec![] }
    let mut visited: HashSet<ValueId> = HashSet::new();
    let mut queue: BinaryHeap<(u32, ValueId)> = BinaryHeap::new();
    let mut selected_friends: SmallVec<[ValueId; 8]> = SmallVec::new();

    for ((_, friend), weight) in phi_friends.range((value, ValueId(i32::MIN))..=(value, ValueId(i32::MAX))) {
        if *friend != value {
            queue.push((*weight, *friend));
        }
    }

    'main: while let Some((_weight, friend)) = queue.pop() {
        if !visited.insert(friend) {
            continue;
        }

        assert!(!candidate_regs.is_empty());

        if allocation.locations.contains_key(&friend) {
            // already tried to allocate here, but there was a conflict
            continue;
        }

        let friend_segments = &value_segments[&friend];
        // Check no self-conflict with already-selected friends
        for &already_selected in &selected_friends {
            let selected_segments = &value_segments[&already_selected];
            for (block, friend_seg) in friend_segments {
                if let Some(ready_seg) = selected_segments.get(block) {
                    if friend_seg.overlap(ready_seg) {
                        // conflicts with already selected friendly value, skip it
                        continue 'main;
                    }
                }
            }
        }

        let mut to_remove: SmallVec<[usize; 8]> = SmallVec::new();
        for &reg_index in candidate_regs.iter() {
            if has_conflict(&register_segments[reg_index], friend_segments) {
                to_remove.push(reg_index);
            }
        }

        if to_remove.len() == candidate_regs.len() {
            continue;
        }

        for reg in to_remove {
            candidate_regs.remove(&reg);
        }
        selected_friends.push(friend);

        for ((_, next), weight) in phi_friends.range((friend, ValueId(i32::MIN))..=(friend, ValueId(i32::MAX))) {
            if *next != value && !visited.contains(next) {
                queue.push((*weight, *next));
            }
        }
    }

    selected_friends
}

const LONG_LIFETIME_WEIGHT: u64 = 1_000_000;

fn equivalence_preferences(g: &GraphBuilder) -> BTreeMap<(ValueId, ValueId), u32> {
    let mut result = BTreeMap::new();

    for block in &g.blocks {
        for i in block.instructions.values() {
            if i.inputs.len() == 0 { continue; }
            let OptOp::Jump(condition, into_block) = &i.op else { continue; };

            // conditional branches are bit costlier, as we need to add one more jump if there are moves
            let weight = if condition == &Condition::True { 1 } else { 2 };
            let into_block = g.block_(*into_block);
            for (param, val) in into_block.parameters.iter().zip(i.inputs.iter()) {
                if val.is_computed() {
                    *result.entry((*param, *val)).or_insert(0u32) += weight;
                    *result.entry((*val, *param)).or_insert(0u32) += weight;
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

#[derive(Clone, Debug)]
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

    println!("LFB {blocks:?}");

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
    println!("Post dataflow {perblock_req:?}");

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
        // println!("{} last use: {last_use:?}", block.id);

        let mut result = vec![];

        for (_, jump_to) in &block.outgoing_jumps {
            for &next_requires in perblock_req.get(&jump_to).iter().flat_map(|x| *x) {
                let &from = defined_at.get(&next_requires).unwrap_or(&0);
                result.push((InstrId(block.id, from), InstrId(block.id, u32::MAX), next_requires));
                // last_use.remove(&next_requires);
                // defined_at.remove(&next_requires);
            }
        }
        // println!("{} last use: {last_use:?}", block.id);

        for (&var, &last_use) in last_use.iter() {
            let &from = defined_at.get(&var).unwrap_or(&0);
            result.push((InstrId(block.id, from), InstrId(block.id, last_use), var));
        }

        // (output-only values need to get written somewhere)
        for (&var, &def_at) in defined_at.iter() {
            if !last_use.contains_key(&var) {
                result.push((InstrId(block.id, def_at), InstrId(block.id, def_at), var));
            }
        }

        for (from, to, var) in &result {
            let var_ranges: &mut HashMap<BlockId, (InstrId, InstrId)> = ranges.entry(*var).or_default();
            // assert!(!var_ranges.contains_key(&block.id), "{result:?} has duplicated value {var}");
            // var_ranges.insert(block.id, (from.clone(), to.clone()));
            var_ranges.entry(block.id).or_insert((from.clone(), to.clone()));
        }
        // println!("{} result {result:?}\n    {ranges:?}", block.id);

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
    assert_eq!(core::mem::size_of::<OsmibyteOp<u8>>(), 8);
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

    fn compile_binary(op: OptOp<ValueId>, lhs_range: RangeInclusive<i64>, rhs_const: i64) -> Vec<OsmibyteOp<RegId>> {
        let (mut g, lhs) = graph_with_param(lhs_range);

        let rhs = g.store_constant(rhs_const);
        let (out, _instr) = g.push_instr(op, &[lhs, rhs], false, None, None);
        let (_out2, _instr2) = g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);
        println!("CFG: {g}");
        let block = OsmibytecodeBlock::from_cfg(&g);
        println!("{:?}", block);
        block.program.iter().cloned().collect()
    }

    #[test]
    fn mod_bitshift_opt() {
        let program = compile_binary(OptOp::Mod, 0..=100, 8);
        assert!(program.iter().any(|op| matches!(op, OsmibyteOp::AndConst(_, _, 7))));
        assert!(!program.iter().any(|op| matches!(op, OsmibyteOp::ModConst(_, _, _))));
    }

    #[test]
    fn mod_bitshift_opt_no() {
        let program = compile_binary(OptOp::Mod, -5..=5, 8);
        assert!(program.iter().any(|op| matches!(op, OsmibyteOp::ModConst(_, _, 8))));
        assert!(!program.iter().any(|op| matches!(op, OsmibyteOp::AndConst(_, _, _))));
    }

    #[test]
    fn mod_euclid_bitshift_opt() {
        let program = compile_binary(OptOp::ModEuclid, -10..=10, 8);
        assert!(matches!(&program[..], [
            OsmibyteOp::AndConst(_, _, 7),
            OsmibyteOp::AddConst(_, _, 2),
        ]));
    }

    #[test]
    fn fusing_cscs() {
        let (mut g, param) = graph_with_param(0..=99_999);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, second], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DigitSumTwice(_, _), OsmibyteOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_cscslensum() {
        let (mut g, param) = graph_with_param(0..=1_000_000);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        let (lensum, _) = g.push_instr(OptOp::LenSum, &[second, first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, lensum], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DigitSumDigitSumLensum(_, _), OsmibyteOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_median2() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::MedianCursed2(_, _) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_median2_no1() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        g.push_instr(OptOp::DigitSum, &[div_out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::ShiftConst(_, _, -1), OsmibyteOp::AddConst(_, _, 1), OsmibyteOp::DigitSum(_, _) ]), "{block}\n{:?}", block.program);
    }
    #[test]
    fn fusing_median2_no2() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        let (median_candidate, _) = g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        let (add2, _) = g.push_instr(OptOp::Add, &[ValueId::C_TWO, median_candidate], false, None, None);
        g.stack.push(add2);
        g.stack.poped_values.push(median_candidate);
        g.clean_poped_values();

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::ShiftConst(_, _, -1), OsmibyteOp::AddConst(_, _, 3) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_0_branch() {
        let (mut g, cond) = graph_with_param(-5..=5);

        let true_val = g.store_constant(6);
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(cond, 0)), &[true_val, ValueId::C_ZERO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConst0(_, _, 6))));
    }

    #[test]
    fn select_consts() {
        let (mut g, cond) = graph_with_param(-3..=3);

        let true_val = g.store_constant(3);
        let false_val = g.store_constant(-2);
        let (out, _) = g.push_instr(OptOp::Select(Condition::NeqConst(cond, 0)), &[true_val, false_val], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConst(_, _, 3, -2))));
    }

    #[test]
    fn select_const_reg() {
        let (mut g, param) = graph_with_param(0..=100);

        // Test: select(param == 0, 42, param * 2)
        let double = g.push_instr(OptOp::Mul, &[ValueId::C_TWO, param], false, None, None).0;
        let const_val = g.store_constant(42);
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[const_val, double], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConstReg(_, _, 42, _))));
    }

    #[test]
    fn select_to_boolnot_eq() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param == 0, 1, 0) -> BoolNot(param)
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);
        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::BoolNot(_, _), OsmibyteOp::AddConst(_, _, 1)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_boolnot_neq() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param != 0, 0, 1) -> BoolNot(param)
        let (out, _) = g.push_instr(OptOp::Select(Condition::NeqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);
        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::BoolNot(_, _), OsmibyteOp::AddConst(_, _, 1)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_sgn_eq_nonneg() {
        let (mut g, param) = graph_with_param(0..=100);

        // select(param == 0, 0, 1) -> Sgn(param) when param >= 0
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::Sgn(_, _), OsmibyteOp::AddConst(_, _, 1)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_sgn_neq_nonneg() {
        let (mut g, param) = graph_with_param(0..=100);

        // select(param != 0, 1, 0) -> Sgn(param) when param >= 0
        let (out, _) = g.push_instr(OptOp::Select(Condition::NeqConst(param, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::Sgn(_, _), OsmibyteOp::AddConst(_, _, 1)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_no_sgn_with_negative_range() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param == 0, 0, 1) should NOT become Sgn when param can be negative
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::SelectConst0(_, _, 1) | OsmibyteOp::SelectConst(_, _, 0, 1), OsmibyteOp::AddConst(_, _, 1)]),
            "{block}\n{:?}", block.program);
    }
}

#[cfg(test)]
mod register_alloc_tests {
    use super::*;

    fn build_phi_merge_graph() -> (GraphBuilder, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let entry_id = g.current_block;

        let seed = g.new_value().id;

        let (friend, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);

        let phi = g.new_value().id;
        let block1_id = g.new_block(0, true, vec![phi]).id;

        let jump_id = g.push_instr(OptOp::Jump(Condition::True, block1_id), &[friend], false, None, None).1.unwrap().id;

        let block1 = g.block_mut(block1_id).unwrap();
        block1.incoming_jumps.push(jump_id);
        block1.predecessors.insert(entry_id);

        g.switch_to_block(block1_id, 0, vec![]);
        g.push_instr(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[], false, None, None);

        (g, phi, friend)
    }

    fn build_conflicting_phi_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let entry_id = g.current_block;

        let seed = g.new_value().id;

        let (friend, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);

        let phi = g.new_value().id;
        let block1_id = g.new_block(0, true, vec![phi]).id;

        let jump_id = g.push_instr(OptOp::Jump(Condition::True, block1_id), &[friend], false, None, None).1.unwrap().id;

        let block1 = g.block_mut(block1_id).unwrap();
        block1.incoming_jumps.push(jump_id);
        block1.predecessors.insert(entry_id);

        g.switch_to_block(block1_id, 0, vec![]);

        let (block_local, _) = g.push_instr(OptOp::Add, &[phi, ValueId::C_ONE], false, None, None);
        let (_mixed, _) = g.push_instr(OptOp::Add, &[phi, block_local], false, None, None);
        g.push_instr(OptOp::Add, &[block_local, ValueId::C_ONE], false, None, None);

        (g, phi, friend, block_local)
    }

    #[test]
    fn phi_friends_share_register_when_lifetimes_do_not_conflict() {
        let (g, phi, friend) = build_phi_merge_graph();
        let allocation = allocate_registers(&g, 10);

        let phi_location = allocation.location(phi);
        let friend_location = allocation.location(friend);

        assert_eq!(phi_location, Some(ValueLocation::Register(0)));
        assert_eq!(phi_location, friend_location);
    }

    #[test]
    fn pressure_causes_spilling() {
        let (g, phi, friend, block_local) = build_conflicting_phi_graph();
        println!("{g}");
        let allocation = allocate_registers(&g, 1);
        println!("{allocation}");

        // With phi-friend merging, phi and friend share a register
        // So with only 1 register available, block_local must spill
        assert_eq!(allocation.location(phi), allocation.location(friend));
        assert!(matches!(allocation.location(block_local), Some(ValueLocation::Spill(_))));
    }

    #[test]
    fn register_conflict_across_bb() {
        let (g, phi, friend, block_local) = build_conflicting_phi_graph();
        println!("{g}");
        let allocation = allocate_registers(&g, 2);
        println!("{allocation}");

        assert!(matches!(allocation.location(phi), Some(ValueLocation::Register(_))));
        assert!(matches!(allocation.location(friend), Some(ValueLocation::Register(_))));
        assert!(matches!(allocation.location(block_local), Some(ValueLocation::Register(_))));

        // With phi-friend merging, phi and friend SHOULD share a register
        // since they're phi-friends with non-overlapping lifetimes
        assert_eq!(allocation.location(phi), allocation.location(friend));

        // block_local should get a different register since it's live at the same time as phi
        assert_ne!(allocation.location(phi), allocation.location(block_local));
    }

    fn setup_diamond_cfg(g: &mut GraphBuilder, seed: ValueId, val1: ValueId, val2: ValueId) -> (BlockId, BlockId) {
        let entry_id = g.current_block;
        let branch1_id = g.new_block(0, true, vec![]).id;
        let branch2_id = g.new_block(0, true, vec![]).id;

        g.switch_to_block(entry_id, 0, vec![]);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::GtConst(seed, 0), branch1_id), &[val1], false, None, None).1.unwrap().id;
        let jump2_id = g.push_instr(OptOp::Jump(Condition::LeqConst(seed, 0), branch2_id), &[val2], false, None, None).1.unwrap().id;

        g.block_mut(branch1_id).unwrap().predecessors.insert(entry_id);
        g.block_mut(branch1_id).unwrap().incoming_jumps.push(jump1_id);
        g.block_mut(branch2_id).unwrap().predecessors.insert(entry_id);
        g.block_mut(branch2_id).unwrap().incoming_jumps.push(jump2_id);

        (branch1_id, branch2_id)
    }

    fn finalize_diamond_merge(g: &mut GraphBuilder, merge_id: BlockId, branch1_id: BlockId,
                               branch2_id: BlockId, jump1_id: InstrId, jump2_id: InstrId) {
        let merge_block = g.block_mut(merge_id).unwrap();
        merge_block.incoming_jumps.push(jump1_id);
        merge_block.incoming_jumps.push(jump2_id);
        merge_block.predecessors.insert(branch1_id);
        merge_block.predecessors.insert(branch2_id);
    }

    fn build_diamond_phi_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let seed = g.new_value().id;
        g.current_block_mut().parameters.push(seed);

        let phi = g.new_value().id;
        let merge_id = g.new_block(0, true, vec![phi]).id;

        let (branch1_id, branch2_id) = setup_diamond_cfg(&mut g, seed, seed, seed);

        g.switch_to_block(branch1_id, 0, vec![]);
        let (val1, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val1], false, None, None).1.unwrap().id;

        g.switch_to_block(branch2_id, 0, vec![]);
        let (val2, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_TWO], false, None, None);
        let jump2_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val2], false, None, None).1.unwrap().id;

        finalize_diamond_merge(&mut g, merge_id, branch1_id, branch2_id, jump1_id, jump2_id);

        g.switch_to_block(merge_id, 0, vec![]);
        g.push_instr(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[], false, None, None);

        (g, phi, val1, val2)
    }

    #[test]
    fn phi_with_two_incoming_edges_unified() {
        let (g, phi, val1, val2) = build_diamond_phi_graph();
        let allocation = allocate_registers(&g, 10);
        println!("{phi} {val1} {val2}\n{g}\n{allocation}");

        let phi_location = allocation.location(phi);
        let val1_location = allocation.location(val1);
        let val2_location = allocation.location(val2);

        // All three should be allocated to the same register since lifetimes don't overlap
        assert_eq!(phi_location, val1_location);
        assert_eq!(phi_location, val2_location);
    }

    fn build_diamond_conflicting_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);

        let seed = g.new_value().id;
        g.current_block_mut().parameters.push(seed);

        // Create val1 and val2 that have overlapping lifetimes in entry block
        let (val1, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);
        let (val2, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_TWO], false, None, None);

        let phi = g.new_value().id;
        let merge_id = g.new_block(0, true, vec![phi]).id;

        let (branch1_id, branch2_id) = setup_diamond_cfg(&mut g, seed, val1, val2);

        g.switch_to_block(branch1_id, 0, vec![]);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val1], false, None, None).1.unwrap().id;

        g.switch_to_block(branch2_id, 0, vec![]);
        let jump2_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val2], false, None, None).1.unwrap().id;

        finalize_diamond_merge(&mut g, merge_id, branch1_id, branch2_id, jump1_id, jump2_id);

        g.switch_to_block(merge_id, 0, vec![]);
        g.push_instr(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[], false, None, None);

        (g, phi, val1, val2)
    }

    #[test]
    fn phi_with_two_incoming_edges_conflicting() {
        let (g, phi, val1, val2) = build_diamond_conflicting_graph();
        let allocation = allocate_registers(&g, 10);
        println!("{phi} {val1} {val2}\n{g}\n{allocation}");
        println!("{:?}", g.val_info(val1).unwrap());
        println!("{:?}", g.val_info(val2).unwrap());

        let phi_location = allocation.location(phi);
        let val1_location = allocation.location(val1);
        let val2_location = allocation.location(val2);

        assert!(matches!(phi_location, Some(ValueLocation::Register(_))));
        assert!(matches!(val1_location, Some(ValueLocation::Register(_))));
        assert!(matches!(val2_location, Some(ValueLocation::Register(_))));

        assert_ne!(val2_location, val1_location);
        assert!(val2_location == phi_location || val1_location == phi_location);
    }
}

use core::fmt;
use std::{fmt::Debug, process::Output, u32};
use arrayvec::ArrayVec;
use smallvec::SmallVec;

use crate::compiler::{cfg::GraphBuilder, osmibytecode_backend::{ALLOCATABLE_REG_COUNT, Compiler, allocate_registers}};


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


#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OsmibyteOp<TReg: Debug + Clone> {
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
    MovBulk(TReg, TReg, TReg, TReg, TReg, TReg, TReg), // dst0 <- dst1 <- ... <- dst6 <- src0

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
    DebugAssert(Condition<TReg>), // if false: panic (debug only)
    DeoptAssert(Condition<TReg>, u16), // if false: abort block execution, deopt info number
    Done(u32, i16), // target instruction pointer + CTR increment (if it can't fit into u32/i16, then we'll standard deopt)
    Median2(TReg, TReg, TReg), // a <- median(b, c)
    MedianCursed2(TReg, TReg), // a <- median(b, 2)
    Median3(TReg, TReg, TReg, TReg), // a <- median(b, c, d)
    MedianCursed3(TReg, TReg, TReg), // a <- median(b, c, 3)
    MedianCursed5(TReg, TReg, TReg, TReg, TReg), // a <- median(b, c, d, e, 5)
    KsplangOp(crate::ops::Op),
    KsplangOpWithArg(crate::ops::Op, TReg),

    KsplangOpsIncrement(i32), // ksplang_interpreted += c
    KsplangOpsIncrementVar(TReg, i8), // ksplang_interpreted += a * b
    KsplangOpsIncrementCond(Condition<TReg>, i16), // ksplang_interpreted += c if condition
    KsplangOpsIncrementCondVar(Condition<TReg>, TReg, i8, i8), // ksplang_interpreted += a * b + c if condition

    ArrayOp(TReg, OsmibyteArrayOp, u16, bool), // out, op, count, pop : out <- op(stack[..count]); if (pop) stack.pop(count)
    ArrayOp3(TReg, OsmibyteArrayOp, TReg, TReg, TReg), // out <- op([a, b, c])
    ArrayOp4(TReg, OsmibyteArrayOp, TReg, TReg, TReg, TReg), // out <- op([a, b, c, d]);
    ArrayOp5(TReg, OsmibyteArrayOp, TReg, TReg, TReg, TReg, TReg), // out <- op([a, b, c, d, e]);

    Spill(u32, TReg), // somewhere[ix] <- a move to a larger register file, should not really happen but easier to implement this than a proper register allocator...
    Unspill(TReg, u32), // a <- somewhere[ix]
}

impl<TReg: Debug + Clone> OsmibyteOp<TReg> {
    pub fn create_push(regs: &[TReg]) -> OsmibyteOp<TReg> {
        match regs.len() {
            1 => OsmibyteOp::Push(regs[0].clone()),
            2 => OsmibyteOp::Push2(regs[0].clone(), regs[1].clone()),
            3 => OsmibyteOp::Push3(regs[0].clone(), regs[1].clone(), regs[2].clone()),
            4 => OsmibyteOp::Push4(regs[0].clone(), regs[1].clone(), regs[2].clone(), regs[3].clone()),
            5 => OsmibyteOp::Push5(regs[0].clone(), regs[1].clone(), regs[2].clone(), regs[3].clone(), regs[4].clone()),
            6 => OsmibyteOp::Push6(regs[0].clone(), regs[1].clone(), regs[2].clone(), regs[3].clone(), regs[4].clone(), regs[5].clone()),
            7 => OsmibyteOp::Push7(regs[0].clone(), regs[1].clone(), regs[2].clone(), regs[3].clone(), regs[4].clone(), regs[5].clone(), regs[6].clone()),
            _ => unreachable!(),
        }
    }

    pub fn replace_regs<TReg2: Debug + Clone, F>(&self, mut f: F) -> OsmibyteOp<TReg2>
        where F: FnMut(&TReg, bool) -> TReg2
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
            OsmibyteOp::MovBulk(dst0, dst1, dst2, dst3, dst4, dst5, src) =>
                OsmibyteOp::MovBulk(f(dst0, true), f(dst1, true), f(dst2, true), f(dst3, true), f(dst4, true), f(dst5, true), f(src, false)),

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
            OsmibyteOp::DebugAssert(condition) => OsmibyteOp::DebugAssert(condition.replace_regs(|r| f(r, false))),
            OsmibyteOp::DeoptAssert(condition, id) => OsmibyteOp::DeoptAssert(condition.replace_regs(|r| f(r, false)), *id),
            OsmibyteOp::Done(ip, ctr) => OsmibyteOp::Done(*ip, *ctr),

            OsmibyteOp::Median2(a, b, c) => OsmibyteOp::Median2(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MedianCursed2(a, b) => OsmibyteOp::MedianCursed2(f(a, true), f(b, false)),
            OsmibyteOp::Median3(a, b, c, d) => OsmibyteOp::Median3(f(a, true), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::MedianCursed3(a, b, c) => OsmibyteOp::MedianCursed3(f(a, true), f(b, false), f(c, false)),
            OsmibyteOp::MedianCursed5(a, b, c, d, e) => OsmibyteOp::MedianCursed5(f(a, true), f(b, false), f(c, false), f(d, false), f(e, false)),

            OsmibyteOp::KsplangOp(op) => OsmibyteOp::KsplangOp(*op),
            OsmibyteOp::KsplangOpWithArg(op, a) => OsmibyteOp::KsplangOpWithArg(*op, f(a, false)),

            OsmibyteOp::KsplangOpsIncrement(inc) => OsmibyteOp::KsplangOpsIncrement(*inc),
            OsmibyteOp::KsplangOpsIncrementVar(inc, mult) => OsmibyteOp::KsplangOpsIncrementVar(f(inc, false), *mult),
            OsmibyteOp::KsplangOpsIncrementCond(cond, inc) => OsmibyteOp::KsplangOpsIncrementCond(cond.replace_regs(|r| f(r, false)), *inc),
            OsmibyteOp::KsplangOpsIncrementCondVar(cond, a, b, c) => OsmibyteOp::KsplangOpsIncrementCondVar(cond.replace_regs(|r| f(r, false)), f(a, false), *b, *c),

            OsmibyteOp::ArrayOp(out, op, count, pop) => OsmibyteOp::ArrayOp(f(out, true), *op, *count, *pop),
            OsmibyteOp::ArrayOp3(out, op, a, b, c) => OsmibyteOp::ArrayOp3(f(out, true), *op, f(a, false), f(b, false), f(c, false)),
            OsmibyteOp::ArrayOp4(out, op, a, b, c, d) => OsmibyteOp::ArrayOp4(f(out, true), *op, f(a, false), f(b, false), f(c, false), f(d, false)),
            OsmibyteOp::ArrayOp5(out, op, a, b, c, d, e) => OsmibyteOp::ArrayOp5(f(out, true), *op, f(a, false), f(b, false), f(c, false), f(d, false), f(e, false)),

            OsmibyteOp::Spill(value, a) => OsmibyteOp::Spill(*value, f(a, false)),
            OsmibyteOp::Unspill(a, value) => OsmibyteOp::Unspill(f(a, true), *value),
        }
    }

    pub fn read_regs(&self) -> ArrayVec<TReg, 8> {
        let mut out = ArrayVec::<TReg, 8>::new();
        self.replace_regs(|r, write| {
            if !write {
                out.push(r.clone());
            }
            ()
        });
        out
    }

    pub fn write_regs(&self) -> ArrayVec<TReg, 8> {
        let mut out = ArrayVec::<TReg, 8>::new();
        self.replace_regs(|r, write| {
            if write {
                out.push(r.clone());
            }
            ()
        });
        out
    }
}

#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord, Debug)]
pub enum OsmibyteArrayOp {
    Nothing, // just pop or verify stack size >= x
    Add,
    AddWrapping,
    Mul,
    Xor,
    And,
    Or,
    Median,
    MedianCursed,
    Max,
    Min,
    Gcd,
}


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

    pub fn replace_arr<TReg2>(&self, f: impl Into<ArrayVec<TReg2, 2>>) -> Condition<TReg2> {
        let mut f = f.into();
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
            Condition::Divides(_, _) => args[1] != 0 && args[0].unsigned_abs() % args[1].unsigned_abs() == 0,
            Condition::DividesConst(_, c) => *c != 0 && args[0].unsigned_abs() % (*c as u64) == 0,
            Condition::NotDivides(_, _) => args[1] == 0 || args[0].unsigned_abs() % args[1].unsigned_abs() != 0,
            Condition::NotDividesConst(_, c) => *c == 0 || args[0].unsigned_abs() % (*c as u64) != 0,
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

    pub fn neg_if(self, condition: bool) -> Condition<TReg> {
        if condition {
            self.neg()
        } else {
            self
        }
    }
}

impl<T> From<bool> for Condition<T> {
    fn from(value: bool) -> Self {
        if value {
            Condition::True
        } else {
            Condition::False
        }
    }
}

impl<T: fmt::Debug> fmt::Display for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Condition::Eq(a, b) => write!(f, "{:?} == {:?}", a, b),
            Condition::EqConst(a, c) => write!(f, "{:?} == '{}'", a, c),
            Condition::Neq(a, b) => write!(f, "{:?} != {:?}", a, b),
            Condition::NeqConst(a, c) => write!(f, "{:?} != '{}'", a, c),
            Condition::Lt(a, b) => write!(f, "{:?} < {:?}", a, b),
            Condition::LtConst(a, c) => write!(f, "{:?} < '{}'", a, c),
            Condition::Leq(a, b) => write!(f, "{:?} <= {:?}", a, b),
            Condition::LeqConst(a, c) => write!(f, "{:?} <= '{}'", a, c),
            Condition::Gt(a, b) => write!(f, "{:?} > {:?}", a, b),
            Condition::GtConst(a, c) => write!(f, "{:?} > '{}'", a, c),
            Condition::Geq(a, b) => write!(f, "{:?} >= {:?}", a, b),
            Condition::GeqConst(a, c) => write!(f, "{:?} >= '{}'", a, c),
            Condition::Divides(a, b) => write!(f, "{:?} % {:?} == 0", a, b),
            Condition::DividesConst(a, c) => write!(f, "{:?} % '{}' == 0", a, c),
            Condition::NotDivides(a, b) => write!(f, "{:?} % {:?} != 0", a, b),
            Condition::NotDividesConst(a, c) => write!(f, "{:?} % '{}' != 0", a, c),
            Condition::True => write!(f, "true"),
            Condition::False => write!(f, "false"),
        }
    }
}
impl<T: fmt::Debug> fmt::Debug for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeoptInfo {
    pub ip: usize,
    pub stack_reconstruction: SmallVec<[RegId; 16]>,
    pub ksplang_ops_increment: i64,
    pub opcodes: Box<[OsmibyteOp<RegId>]>,
}

impl DeoptInfo {
    pub fn new(ip: usize, stack: &[RegId], ksplang_ops_increment: i64, opcodes: &[OsmibyteOp<RegId>]) -> Self {
        DeoptInfo {
            ip,
            stack_reconstruction: stack.into(),
            ksplang_ops_increment,
            opcodes: opcodes.into()
        }
    }
}

#[derive(Clone)]
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
            for (ix, d) in self.deopts.iter().enumerate() {
                write!(f, "    #{ix:04}: IP = {}", d.ip)?;
                if d.ksplang_ops_increment != 0 {
                    write!(f, ", CTR += {}", d.ksplang_ops_increment)?;
                }
                writeln!(f)?;
                if d.opcodes.len() > 0 {
                    writeln!(f, "           ops: {:?}", d.opcodes)?;
                }
                if d.stack_reconstruction.len() > 0 {
                    writeln!(f, "           stack: {:?}", d.stack_reconstruction)?;
                }
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
        let register_allocation = allocate_registers(g, ALLOCATABLE_REG_COUNT, g.conf.error_as_deopt);
        if g.conf.should_log(16) {
            println!("Register allocation: {}", register_allocation);
        }
        let mut compiler = Compiler::new(g, register_allocation);
        compiler.compile();
        compiler.finish()
    }
}

#[test]
fn test_osmjeosm() {
    assert_eq!(core::mem::size_of::<Condition<u8>>(), 4);
    assert_eq!(core::mem::size_of::<OsmibyteOp<u8>>(), 8);
}


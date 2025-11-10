use std::{cmp, hint::select_unpredictable, mem::MaybeUninit, ops::{Index, IndexMut}, process::exit, u32};

use num_integer::Integer;

use crate::{compiler::{osmibytecode::{Condition, OsmibyteOp, OsmibytecodeBlock, RegId}, utils::{SaturatingInto, sort_tuple}}, digit_sum, funkcia, vm::{self, OperationError}};



fn error_from_code(code: u16, value: i64) -> OperationError {
    match code {
        0 => OperationError::IntegerOverflow,
        1 => OperationError::DivisionByZero,
        2 => OperationError::InvalidArgumentForUniversal { argument: value },
        3 => OperationError::NegativeLength { value },
        4 => OperationError::NegativeIterations { iterations: value },
        5 => OperationError::NegativeBitCount { bits: value },
        6 => OperationError::NonpositiveLength { value },
        7 => OperationError::NegativeInstructionIndex { index: value },
        8 => OperationError::NegativePraiseCount { praises: value },
        9 => OperationError::QeqZeroEqualsZero,
        10 => OperationError::ArgumentAMustBeNonNegative { value },
        11 => OperationError::ArgumentBMustBeNonNegative { value },
        12 => OperationError::ArgumentBMustBeNonNegative { value },
        _ => todo!("code={code}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExitPointId {
    Start,
    Deopt(u32),
    Done(u32)
}
impl ExitPointId {
    pub fn encode(&self) -> u64 {
        match self {
            ExitPointId::Deopt(id) => *id as u64 | (1u64 << 32),
            ExitPointId::Done(id) => *id as u64,
            ExitPointId::Start => 2u64 << 32,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RunBlockResult {
    pub continue_ip: usize,
    pub ksplang_interpreted: u64,
    pub bytecode_interpreted: u64,
    pub exit_point: ExitPointId
}

#[derive(Debug, Clone)]
pub struct RegFile {
    regs: [i64; 256]
}
impl RegFile {
    pub fn new() -> Self { RegFile { regs: [0i64; 256] } }
    // fn new_unsafe() -> Self { unsafe { RegFile { regs: MaybeUninit::uninit().assume_init() } } }
}
impl Index<u8> for RegFile {
    type Output = i64;

    #[inline(always)]
    fn index(&self, index: u8) -> &Self::Output { &self.regs[index as usize] }
}
impl Index<&u8> for RegFile {
    type Output = i64;

    #[inline(always)]
    fn index(&self, index: &u8) -> &Self::Output { &self.regs[*index as usize] }
}
impl IndexMut<u8> for RegFile {
    #[inline(always)]
    fn index_mut(&mut self, index: u8) -> &mut Self::Output { &mut self.regs[index as usize] }
}
impl IndexMut<&u8> for RegFile {
    #[inline(always)]
    fn index_mut(&mut self, index: &u8) -> &mut Self::Output { &mut self.regs[*index as usize] }
}

impl Index<RegId> for RegFile {
    type Output = i64;

    #[inline(always)]
    fn index(&self, index: RegId) -> &Self::Output { &self.regs[index.0 as usize] }
}

impl Index<&RegId> for RegFile {
    type Output = i64;

    #[inline(always)]
    fn index(&self, index: &RegId) -> &Self::Output { &self.regs[index.0 as usize] }
}

impl IndexMut<RegId> for RegFile {
    #[inline(always)]
    fn index_mut(&mut self, index: RegId) -> &mut Self::Output { &mut self.regs[index.0 as usize] }
}

impl IndexMut<&RegId> for RegFile {
    #[inline(always)]
    fn index_mut(&mut self, index: &RegId) -> &mut Self::Output { &mut self.regs[index.0 as usize] }
}

fn eval_cond(regs: &RegFile, cond: Condition<RegId>) -> bool {
    match cond {
        Condition::True => true,
        Condition::False => false,
        Condition::Eq(a, b) => regs[a] == regs[b],
        Condition::EqConst(a, c) => regs[a] == c as i64,
        Condition::Neq(a, b) => regs[a] != regs[b],
        Condition::NeqConst(a, c) => regs[a] != c as i64,
        Condition::Lt(a, b) => regs[a] < regs[b],
        Condition::LtConst(a, c) => regs[a] < c as i64,
        Condition::Leq(a, b) => regs[a] <= regs[b],
        Condition::LeqConst(a, c) => regs[a] <= c as i64,
        Condition::Gt(a, b) => regs[a] > regs[b],
        Condition::GtConst(a, c) => regs[a] > c as i64,
        Condition::Geq(a, b) => regs[a] >= regs[b],
        Condition::GeqConst(a, c) => regs[a] >= c as i64,
        Condition::Divides(a, b) => {
            let divisor = regs[b];
            divisor != 0 && regs[a] % divisor == 0
        }
        Condition::DividesConst(a, divisor) => regs[a] % divisor as i64 == 0,
        Condition::NotDivides(a, b) => {
            let divisor = regs[b];
            divisor == 0 || regs[a] % divisor != 0
        }
        Condition::NotDividesConst(a, divisor) => regs[a] % divisor as i64 != 0
    }
}

#[cold]
fn maybe_cold() { } // not sure if this even works

pub fn interpret_block<const DEOPT_ON_ERROR: bool>(prog: &OsmibytecodeBlock, stack: &mut Vec<i64>, regs: &mut RegFile) -> Result<RunBlockResult, OperationError> {
    if stack.len() <= prog.stack_values_required as usize {
        return Ok(RunBlockResult { continue_ip: prog.start_ip, bytecode_interpreted: 0, ksplang_interpreted: 0, exit_point: ExitPointId::Start })
    }
    // let mut regs = RegFile::new();
    let mut spill: Vec<i64> = Vec::new();
    let mut ip: u32 = 0;
    let mut bytecode_ops_done = 0;
    let mut ksplang_ops_done = 0u64;

    let mut performing_deopt: Option<u32> = None;
    let mut deopt_info: Option<u32> = None;
    let mut deopt_auto = false;
    let mut simply_done: Option<usize> = None;
    let mut exit_point = None;

    macro_rules! deopt_or_error {
        ($err:expr) => {
            if DEOPT_ON_ERROR {
                maybe_cold();
                deopt_auto = true; break;
            } else {
                maybe_cold();
                return Err($err)
            }
        };
    }

    let mut program: &[OsmibyteOp<RegId>] = &prog.program;

    'main: loop {
        '_program: while (ip as usize) < program.len() {
            let op = &program[ip as usize];
            // println!("{bytecode_ops_done}: {ip}: {op:?} ({})",
            //     op.read_regs().iter().map(|r| format!("{r}={}", regs[r])).collect::<Vec<_>>().join(", ")
            // );
            bytecode_ops_done += 1;
            match op {
                OsmibyteOp::Push(a) => { stack.push(regs[a]); },
                OsmibyteOp::Push2(a, b) => { stack.extend_from_slice(&[regs[a], regs[b]]); },
                OsmibyteOp::Push3(a, b, c) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c]]); },
                OsmibyteOp::Push4(a, b, c, d) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d]]); },
                OsmibyteOp::Push5(a, b, c, d, e) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e]]); },
                OsmibyteOp::Push6(a, b, c, d, e, f) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e], regs[f]]); },
                OsmibyteOp::Push7(a, b, c, d, e, f, g) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e], regs[f], regs[g]]); },
                OsmibyteOp::Pop(a) => {
                    let Some(v) = stack.pop() else { deopt_or_error!(OperationError::PopFailed) };
                    regs[a] = v
                },
                OsmibyteOp::Pop2(a, b) => {
                    if stack.len() <= 1 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                },
                OsmibyteOp::Pop3(a, b, c) => {
                    if stack.len() <= 2 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                    regs[c] = stack.pop().unwrap_or(0);
                },
                OsmibyteOp::Pop4(a, b, c, d) => {
                    if stack.len() <= 3 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                    regs[c] = stack.pop().unwrap_or(0);
                    regs[d] = stack.pop().unwrap_or(0);
                },
                OsmibyteOp::PopSecond(a) => {
                    if stack.len() <= 1 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.swap_remove(stack.len() - 2)
                },
                OsmibyteOp::Mov2(dst0, src0, dst1, src1) => {
                    let v0 = regs[src0];
                    let v1 = regs[src1];
                    regs[dst0] = v0;
                    regs[dst1] = v1;
                },
                OsmibyteOp::Mov3(dst0, src0, dst1, src1, dst2, src2) => {
                    let v0 = regs[src0];
                    let v1 = regs[src1];
                    let v2 = regs[src2];
                    regs[dst0] = v0;
                    regs[dst1] = v1;
                    regs[dst2] = v2;
                },
                OsmibyteOp::Add(out, a, b) => {
                    let Some(val) = regs[a].checked_add(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::AddConst(out, a, b) => {
                    let Some(val) = regs[a].checked_add(*b as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::Sub(out, a, b) => {
                    let Some(val) = regs[a].checked_sub(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::SubConst(out, constant, c) => {
                    let const_val = (*constant) as i64;
                    let Some(val) = const_val.checked_sub(regs[c]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::AbsSub(out, a, b) => {
                    let diff = regs[a].abs_diff(regs[b]);
                    if diff > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = diff as i64;
                },
                OsmibyteOp::AbsSubConst(out, a, constant) => {
                    let diff = regs[a].abs_diff(*constant as i64);
                    if diff > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = diff as i64;
                },
                OsmibyteOp::Mul(out, a, b) => {
                    let Some(val) = regs[a].checked_mul(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::MulConst(out, a, constant) => {
                    let Some(val) = regs[a].checked_mul(*constant as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::Div(out, a, b) => {
                    let Some(val) = regs[a].checked_div(regs[b]) else {
                        deopt_or_error!(if regs[b] == 0 { OperationError::DivisionByZero } else { OperationError::IntegerOverflow })
                    };
                    regs[out] = val;
                },
                OsmibyteOp::DivConst(out, a, c) => {
                    debug_assert_ne!(0, *c);
                    let Some(val) = regs[a].checked_div(*c as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::CursedDiv(out, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    let Some(rem) = lhs.checked_rem(rhs) else {
                        deopt_or_error!(OperationError::DivisionByZero)
                    };
                    if rem == 0 {
                        let Some(val) = lhs.checked_div(rhs) else {
                            deopt_or_error!(OperationError::IntegerOverflow)
                        };
                        regs[out] = val;
                    } else {
                        regs[out] = rem;
                    }
                },
                OsmibyteOp::Mod(out, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    let Some(val) = lhs.checked_rem(rhs) else {
                        deopt_or_error!(OperationError::DivisionByZero)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::ModConst(out, a, c) => { regs[out] = regs[a] % *c as i64 },
                OsmibyteOp::ModEuclid(out, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    let Some(val) = lhs.checked_rem_euclid(rhs) else {
                        deopt_or_error!(OperationError::DivisionByZero)
                    };
                    regs[out] = val;
                },
                OsmibyteOp::ModEuclidConst(out, a, c) => { regs[out] = regs[a].rem_euclid(*c as i64); },
                OsmibyteOp::Tetration(out, a, b) => {
                    match vm::tetration(regs[a], regs[b]) {
                        Ok(val) => regs[out] = val,
                        Err(err) => deopt_or_error!(err),
                    }
                },
                OsmibyteOp::Funkcia(out, a, b) => { regs[out] = funkcia::funkcia(regs[a], regs[b]) as i64 },
                OsmibyteOp::Max(out, a, b) => { regs[out] = cmp::max(regs[a], regs[b]); },
                OsmibyteOp::MaxConst(out, a, constant) => { regs[out] = cmp::max(regs[a], *constant as i64); },
                OsmibyteOp::Min(out, a, b) => { regs[out] = cmp::min(regs[a], regs[b]); },
                OsmibyteOp::MinConst(out, a, constant) => { regs[out] = cmp::min(regs[a], *constant as i64); },
                OsmibyteOp::Clamp(out, value, lo, hi) => {
                    let val = regs[value];
                    let (lo, hi) = sort_tuple(regs[lo], regs[hi]);
                    regs[out] = val.clamp(lo, hi);
                },
                OsmibyteOp::ClampConst(out, value, lo, hi) => {
                    regs[out] = regs[value].clamp(*lo as i64, *hi as i64);
                },
                OsmibyteOp::Sgn(out, a) => { regs[out] = regs[a].signum() },
                OsmibyteOp::AbsFactorial(out, a) => {
                    match vm::abs_factorial(regs[a]) {
                        Ok(val) => regs[out] = val,
                        Err(err) => deopt_or_error!(err),
                    }
                },
                OsmibyteOp::Lensum(out, a, b) => {
                    regs[out] = vm::decimal_len(regs[a]) + vm::decimal_len(regs[b]);
                },
                OsmibyteOp::Universal2(out, op_reg, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    match regs[op_reg] {
                        0 => {
                            let Some(val) = lhs.checked_add(rhs) else {
                                deopt_or_error!(OperationError::IntegerOverflow)
                            };
                            regs[out] = val;
                        }
                        1 => {
                            let Some(val) = lhs.checked_sub(rhs).and_then(|diff| diff.checked_abs()) else {
                                deopt_or_error!(OperationError::IntegerOverflow)
                            };
                            regs[out] = val;
                        }
                        2 => {
                            let Some(val) = lhs.checked_mul(rhs) else {
                                deopt_or_error!(OperationError::IntegerOverflow)
                            };
                            regs[out] = val;
                        }
                        3 => {
                            let Some(rem) = lhs.checked_rem(rhs) else {
                                deopt_or_error!(if rhs == 0 { OperationError::DivisionByZero } else { OperationError::IntegerOverflow })
                            };
                            if rem == 0 {
                                let Some(val) = lhs.checked_div(rhs) else {
                                    deopt_or_error!(OperationError::IntegerOverflow)
                                };
                                regs[out] = val;
                            } else {
                                regs[out] = rem;
                            }
                        }
                        4 | 5 => {
                            deopt_auto = true;
                            break;
                        }
                        other => {
                            deopt_or_error!(OperationError::InvalidArgumentForUniversal { argument: other })
                        }
                    }
                },
                OsmibyteOp::Universal1(out, op_reg, a) => {
                    let value = regs[a];
                    match regs[op_reg] {
                        4 => match vm::abs_factorial(value) {
                            Ok(val) => regs[out] = val,
                            Err(err) => deopt_or_error!(err),
                        },
                        5 => regs[out] = value.signum(),
                        0 | 1 | 2 | 3 => {
                            deopt_auto = true;
                            break;
                        }
                        other => {
                            deopt_or_error!(OperationError::InvalidArgumentForUniversal { argument: other })
                        }
                    }
                },
                OsmibyteOp::And(out, a, b) => regs[out] = regs[a] & regs[b],
                OsmibyteOp::AndConst(out, a, mask) => regs[out] = regs[a] & (*mask as i64),
                OsmibyteOp::Or(out, a, b) => regs[out] = regs[a] | regs[b],
                OsmibyteOp::OrConst(out, a, mask) => regs[out] = regs[a] | (*mask as i64),
                OsmibyteOp::Xor(out, a, b) => regs[out] = regs[a] ^ regs[b],
                OsmibyteOp::XorConst(out, a, mask) => regs[out] = regs[a] ^ (*mask as i64),
                OsmibyteOp::ShiftL(out, a, b) => {
                    let shift = regs[b];
                    if shift < 0 { deopt_or_error!(OperationError::NegativeBitCount { bits: shift }) }
                    regs[out] = regs[a].unbounded_shl(shift.saturating_into());
                },
                OsmibyteOp::ShiftR(out, a, b) => {
                    let shift = regs[b];
                    if shift < 0 { deopt_or_error!(OperationError::NegativeBitCount { bits: shift }) }
                    let amount = shift as u64;
                    let value = regs[a];
                    regs[out] = if amount >= i64::BITS as u64 {
                        if value >= 0 { 0 } else { -1 }
                    } else {
                        value >> (amount as u32)
                    };
                },
                OsmibyteOp::ShiftConst(out, a, shift) => { regs[out] = if *shift >= 0 { regs[a] << shift } else { regs[a] >> -shift } },
                OsmibyteOp::BinNot(out, a) => regs[out] = !regs[a],
                OsmibyteOp::BoolNot(out, a) => regs[out] = (regs[a] == 0) as i64,
                OsmibyteOp::SelectConst(out, condition, c1, c2) => regs[out] = select_unpredictable(eval_cond(&regs, condition.clone()), *c1, *c2) as i64,
                OsmibyteOp::SelectConst0(out, condition, c1) => regs[out] = select_unpredictable(eval_cond(&regs, condition.clone()), *c1, 0) as i64,
                OsmibyteOp::SelectConstReg(out, condition, c, a) => regs[out] = if eval_cond(&regs, condition.clone()) { *c as i64 } else { regs[a] },
                OsmibyteOp::Select(out, condition, a, b) => regs[out] = if eval_cond(&regs, condition.clone()) { regs[a] } else { regs[b] },
                OsmibyteOp::DigitSum(out, a) => regs[out] = digit_sum::digit_sum(regs[a]),
                OsmibyteOp::DigitSumSmall(out, a) => {
                    let value = regs[a];
                    if value.unsigned_abs() > 10_000 {
                        maybe_cold();
                        deopt_auto = true;
                        break;
                    }
                    regs[out] = digit_sum::digit_sum(value);
                },
                OsmibyteOp::DigitSumTwice(out, a) => regs[out] = digit_sum::digit_sum_twice(regs[a]).1,
                OsmibyteOp::DigitSumDigitSumLensum(out, a) => {
                    let a = regs[a];
                    regs[out] = if a <= 18 {
                        2
                    } else {
                        let (x, y) = digit_sum::digit_sum_twice(a);
                        vm::decimal_len(x) + vm::decimal_len(y)
                    }
                },
                OsmibyteOp::Gcd(out, a, b) => {
                    let res = regs[a].unsigned_abs().gcd(&regs[b].unsigned_abs());
                    if res > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = res as i64;
                }
                OsmibyteOp::StackSwap(out, ix, val, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break; // we may be missing few elements on the top -> only deopt is safe
                    }
                    let val = regs[val];
                    regs[out] = stack[ix as usize];
                    stack[ix as usize] = val;
                },
                OsmibyteOp::StackWrite(ix, val, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break;
                    }
                    stack[ix as usize] = regs[val];
                },
                OsmibyteOp::StackRead(out, ix, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break;
                    }
                    regs[out] = stack[ix as usize];
                },
                OsmibyteOp::LoadConst(out, c) => regs[out] = *c as i64,
                OsmibyteOp::LoadConstPow2Offset(out, pow, offset) => {
                    let val = (1u64 << pow).overflowing_add_signed(*offset as i64).0;
                    regs[out] = val as i64;
                },
                OsmibyteOp::LoadConst64(out, id) => { regs[out] = prog.large_constants[*id as usize] },
                OsmibyteOp::Jump(condition, new_ip) => {
                    if eval_cond(&regs, condition.clone()) {
                        ip = *new_ip as u32;
                        continue;
                    }
                },
                OsmibyteOp::Assert(condition, err, arg) => {
                    if !eval_cond(&regs, condition.clone()) {
                        deopt_or_error!(error_from_code(*err, regs[arg]))
                    }
                },
                OsmibyteOp::DeoptAssert(condition, di) => {
                    if !eval_cond(&regs, condition.clone()) {
                        maybe_cold();
                        deopt_info = Some(*di as u32);
                        break;
                    }
                },
                OsmibyteOp::Done(continue_at, ctr_inc) => {
                    simply_done = Some(*continue_at as usize);
                    ksplang_ops_done = ksplang_ops_done.overflowing_add_signed(*ctr_inc as i64).0;
                    exit_point.get_or_insert(ExitPointId::Done(ip));
                    break 'main;
                },
                OsmibyteOp::Median2(out, a, b) => {
                    let a = regs[a];
                    let b = regs[b];
                    regs[out] = a / 2 + b / 2 + a % 2 + b % 2;
                },
                OsmibyteOp::MedianCursed2(out, a) => {
                    regs[out] = regs[a] / 2 + 1
                },
                OsmibyteOp::Median3(out, a, b, c) => {
                    let mut arr = [regs[a], regs[b], regs[c]];
                    arr.sort_unstable();
                    regs[out] = arr[1];
                },
                OsmibyteOp::MedianCursed3(out, a, b) => {
                    let mut arr = [3, regs[a], regs[b]];
                    arr.sort_unstable();
                    regs[out] = arr[1];
                },
                OsmibyteOp::MedianCursed5(out, a, b, c, d) => {
                    let mut arr = [5, regs[a], regs[b], regs[c], regs[d]];
                    arr.sort_unstable();
                    regs[out] = arr[2];
                }
                OsmibyteOp::KsplangOp(_op) => panic!("probably does not make sense anymore?"),
                OsmibyteOp::KsplangOpWithArg(_op, _) => todo!("probably does not make sense anymore?"),
                OsmibyteOp::KsplangOpsIncrement(x) => { ksplang_ops_done = ksplang_ops_done.overflowing_add(*x as u64).0 },
                OsmibyteOp::KsplangOpsIncrementVar(x) => { ksplang_ops_done = ksplang_ops_done.overflowing_add(u64::try_from(regs[x]).unwrap()).0 },
                OsmibyteOp::KsplangOpsIncrementCond(condition, x) => {
                    if eval_cond(&regs, condition.clone()) {
                        ksplang_ops_done = ksplang_ops_done.overflowing_add(*x as u64).0
                    }
                },
                OsmibyteOp::Spill(ix, a) => {
                    while spill.len() <= *ix as usize {
                        spill.push(0);
                    }
                    spill[*ix as usize] = regs[a]
                },
                OsmibyteOp::Unspill(a, ix) => { regs[a] = spill[*ix as usize] }
            }

            // println!("{bytecode_ops_done}: {ip}: -> {}",
            //     op.write_regs().iter().map(|r| format!("{r}={}", regs[r])).collect::<Vec<_>>().join(", ")
            // );

            debug_assert!(!deopt_auto && deopt_info.is_none() && simply_done.is_none());
            ip += 1;
        }

        if simply_done.is_some() {
            debug_assert!(!deopt_auto && deopt_info.is_none());
            // println!("done at {ip} {simply_done:?}");
            exit_point.get_or_insert(ExitPointId::Done(ip));
            break;
        }

        // switch to performing deopt
        if deopt_auto {
            debug_assert!(deopt_info.is_none());
            assert!(performing_deopt.is_none(), "auto-deopt is not supported when in a deopt (IP is ambiguous). Deopt instructions must not fail");
            // println!("deopt_auto at {ip}");
            match prog.ip2deopt.binary_search_by_key(&ip, |x| x.0) {
                Err(ix) => panic!("Operation {ip} auto-deopts, but corresponding deopt is not recorded? (closest is {ix} {:?}", prog.ip2deopt[ix]),
                Ok(ix) => deopt_info = Some(prog.ip2deopt[ix].1)
            }
        }

        if let Some(deopt_id) = deopt_info {
            deopt_info = None;
            deopt_auto = false;

            let deopt = &prog.deopts[deopt_id as usize];
            // println!("DEOPT at {ip}: {deopt_id} {:?}", deopt);
            exit_point.get_or_insert(ExitPointId::Deopt(deopt_id));
            performing_deopt = Some(deopt_id);
            ksplang_ops_done = ksplang_ops_done.overflowing_add_signed(deopt.ksplang_ops_increment as i64).0;
            program = &deopt.opcodes;
            ip = 0;
        } else if let Some(deopt_id) = performing_deopt {
            assert_eq!(ip as usize, program.len());
            let deopt = &prog.deopts[deopt_id as usize];
            debug_assert_eq!(&deopt.opcodes[..], program);

            for reg in &deopt.stack_reconstruction {
                stack.push(regs[reg]);
            }

            simply_done = Some(deopt.ip)
        }
    }

    let continue_ip = simply_done.unwrap();
    Ok(RunBlockResult {
        continue_ip,
        ksplang_interpreted: ksplang_ops_done,
        bytecode_interpreted: bytecode_ops_done,
        exit_point: exit_point.unwrap()
    })
}

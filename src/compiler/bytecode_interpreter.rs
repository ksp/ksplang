use std::{cmp, hint::select_unpredictable, ops::{Index, IndexMut}};

use num_integer::Integer;

use crate::{compiler::{utils::sort_tuple, vm_code::{Condition, PrecompiledBlock, PrecompiledOp, RegId}}, digit_sum, funkcia, vm::{self, OperationError}};



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

#[derive(Debug, Clone, PartialEq)]
pub struct RunBlockResult {
    pub continue_ip: usize,
    pub ksplang_interpreted: u64,
    pub bytecode_interpreted: u64,
}

struct RegFile {
    regs: [i64; 256]
}
impl RegFile {
    fn new() -> Self { RegFile { regs: [0i64; 256] } }
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

pub fn interpret_block<const DEOPT_ON_ERROR: bool>(prog: &PrecompiledBlock, stack: &mut Vec<i64>) -> Result<RunBlockResult, OperationError> {
    if stack.len() <= prog.stack_values_required as usize {
        return Ok(RunBlockResult { continue_ip: prog.start_ip, bytecode_interpreted: 0, ksplang_interpreted: 0 })
    }
    let mut regs = RegFile::new();
    let mut spill: Vec<i64> = Vec::new();
    let mut ip: u32 = 0;
    let mut bytecode_ops_done = 0;
    let mut ksplang_ops_done = 0u64;

    let mut performing_deopt: Option<u32> = None;
    let mut deopt_info: Option<u32> = None;
    let mut deopt_auto = false;
    let mut simply_done: Option<usize> = None;

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

    let mut program: &[PrecompiledOp<RegId>] = &prog.program;

    'main: loop {
        'program: while (ip as usize) < program.len() {
            let op = &program[ip as usize];
            bytecode_ops_done += 1;
            match op {
                PrecompiledOp::Push(a) => { stack.push(regs[a]); },
                PrecompiledOp::Push2(a, b) => { stack.extend_from_slice(&[regs[a], regs[b]]); },
                PrecompiledOp::Push3(a, b, c) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c]]); },
                PrecompiledOp::Push4(a, b, c, d) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d]]); },
                PrecompiledOp::Push5(a, b, c, d, e) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e]]); },
                PrecompiledOp::Push6(a, b, c, d, e, f) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e], regs[f]]); },
                PrecompiledOp::Push7(a, b, c, d, e, f, g) => { stack.extend_from_slice(&[regs[a], regs[b], regs[c], regs[d], regs[e], regs[f], regs[g]]); },
                PrecompiledOp::Pop(a) => {
                    let Some(v) = stack.pop() else { deopt_or_error!(OperationError::PopFailed) };
                    regs[a] = v
                },
                PrecompiledOp::Pop2(a, b) => {
                    if stack.len() <= 1 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                },
                PrecompiledOp::Pop3(a, b, c) => {
                    if stack.len() <= 2 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                    regs[c] = stack.pop().unwrap_or(0);
                },
                PrecompiledOp::Pop4(a, b, c, d) => {
                    if stack.len() <= 3 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.pop().unwrap_or(0);
                    regs[b] = stack.pop().unwrap_or(0);
                    regs[c] = stack.pop().unwrap_or(0);
                    regs[d] = stack.pop().unwrap_or(0);
                },
                PrecompiledOp::PopSecond(a) => {
                    if stack.len() <= 1 { deopt_or_error!(OperationError::PopFailed) }
                    regs[a] = stack.swap_remove(stack.len() - 2)
                },
                PrecompiledOp::Add(out, a, b) => {
                    let Some(val) = regs[a].checked_add(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::AddConst(out, a, b) => {
                    let Some(val) = regs[a].checked_add(*b as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::Sub(out, a, b) => {
                    let Some(val) = regs[a].checked_sub(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::SubConst(out, constant, c) => {
                    let const_val = (*constant) as i64;
                    let Some(val) = const_val.checked_sub(regs[c]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::AbsSub(out, a, b) => {
                    let diff = regs[a].abs_diff(regs[b]);
                    if diff > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = diff as i64;
                },
                PrecompiledOp::AbsSubConst(out, a, constant) => {
                    let diff = regs[a].abs_diff(*constant as i64);
                    if diff > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = diff as i64;
                },
                PrecompiledOp::Mul(out, a, b) => {
                    let Some(val) = regs[a].checked_mul(regs[b]) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::MulConst(out, a, constant) => {
                    let Some(val) = regs[a].checked_mul(*constant as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::Div(out, a, b) => {
                    let Some(val) = regs[a].checked_div(regs[b]) else {
                        deopt_or_error!(if regs[b] == 0 { OperationError::DivisionByZero } else { OperationError::IntegerOverflow })
                    };
                    regs[out] = val;
                },
                PrecompiledOp::DivConst(out, a, c) => {
                    debug_assert_ne!(0, *c);
                    let Some(val) = regs[a].checked_div(*c as i64) else {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::CursedDiv(out, a, b) => {
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
                PrecompiledOp::Mod(out, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    let Some(val) = lhs.checked_rem(rhs) else {
                        deopt_or_error!(OperationError::DivisionByZero)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::ModConst(out, a, c) => { regs[out] = regs[a] % *c as i64 },
                PrecompiledOp::ModEuclid(out, a, b) => {
                    let lhs = regs[a];
                    let rhs = regs[b];
                    let Some(val) = lhs.checked_rem_euclid(rhs) else {
                        deopt_or_error!(OperationError::DivisionByZero)
                    };
                    regs[out] = val;
                },
                PrecompiledOp::ModEuclidConst(out, a, c) => { regs[out] = regs[a].rem_euclid(*c as i64); },
                PrecompiledOp::Tetration(out, a, b) => {
                    match vm::tetration(regs[a], regs[b]) {
                        Ok(val) => regs[out] = val,
                        Err(err) => deopt_or_error!(err),
                    }
                },
                PrecompiledOp::Funkcia(out, a, b) => { regs[out] = funkcia::funkcia(regs[a], regs[b]) as i64 },
                PrecompiledOp::Max(out, a, b) => { regs[out] = cmp::max(regs[a], regs[b]); },
                PrecompiledOp::MaxConst(out, a, constant) => { regs[out] = cmp::max(regs[a], *constant as i64); },
                PrecompiledOp::Min(out, a, b) => { regs[out] = cmp::min(regs[a], regs[b]); },
                PrecompiledOp::MinConst(out, a, constant) => { regs[out] = cmp::min(regs[a], *constant as i64); },
                PrecompiledOp::Clamp(out, value, lo, hi) => {
                    let val = regs[value];
                    let (lo, hi) = sort_tuple(regs[lo], regs[hi]);
                    regs[out] = val.clamp(lo, hi);
                },
                PrecompiledOp::ClampConst(out, value, lo, hi) => {
                    regs[out] = regs[value].clamp(*lo as i64, *hi as i64);
                },
                PrecompiledOp::Sgn(out, a) => { regs[out] = regs[a].signum() },
                PrecompiledOp::AbsFactorial(out, a) => {
                    match vm::abs_factorial(regs[a]) {
                        Ok(val) => regs[out] = val,
                        Err(err) => deopt_or_error!(err),
                    }
                },
                PrecompiledOp::Lensum(out, a, b) => {
                    regs[out] = vm::decimal_len(regs[a]) + vm::decimal_len(regs[b]);
                },
                PrecompiledOp::Universal2(out, op_reg, a, b) => {
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
                PrecompiledOp::Universal1(out, op_reg, a) => {
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
                PrecompiledOp::And(out, a, b) => regs[out] = regs[a] & regs[b],
                PrecompiledOp::AndConst(out, a, mask) => regs[out] = regs[a] & (*mask as i64),
                PrecompiledOp::Or(out, a, b) => regs[out] = regs[a] | regs[b],
                PrecompiledOp::OrConst(out, a, mask) => regs[out] = regs[a] | (*mask as i64),
                PrecompiledOp::Xor(out, a, b) => regs[out] = regs[a] ^ regs[b],
                PrecompiledOp::XorConst(out, a, mask) => regs[out] = regs[a] ^ (*mask as i64),
                PrecompiledOp::ShiftL(out, a, b) => {
                    let shift = regs[b];
                    if shift < 0 { deopt_or_error!(OperationError::NegativeBitCount { bits: shift }) }
                    regs[out] = regs[a].unbounded_shl(shift.try_into().unwrap_or(64));
                },
                PrecompiledOp::ShiftR(out, a, b) => {
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
                PrecompiledOp::ShiftConst(out, a, shift) => { regs[out] = if *shift >= 0 { regs[a] << shift } else { regs[a] >> -shift } },
                PrecompiledOp::BinNot(out, a) => regs[out] = !regs[a],
                PrecompiledOp::BoolNot(out, a) => regs[out] = (regs[a] == 0) as i64,
                PrecompiledOp::SelectConst(out, condition, c1, c2) => regs[out] = select_unpredictable(eval_cond(&regs, condition.clone()), *c1, *c2) as i64,
                PrecompiledOp::SelectConst0(out, condition, c1) => regs[out] = select_unpredictable(eval_cond(&regs, condition.clone()), *c1, 0) as i64,
                PrecompiledOp::Select(out, condition, a, b) => regs[out] = if eval_cond(&regs, condition.clone()) { regs[a] } else { regs[b] },
                PrecompiledOp::DigitSum(out, a) => regs[out] = digit_sum::digit_sum(regs[a]),
                PrecompiledOp::DigitSumSmall(out, a) => {
                    let value = regs[a];
                    if value.unsigned_abs() > 10_000 {
                        maybe_cold();
                        deopt_auto = true;
                        break;
                    }
                    regs[out] = digit_sum::digit_sum(value);
                },
                PrecompiledOp::DigitSumTwice(out, a) => regs[out] = digit_sum::digit_sum_twice(regs[a]).1,
                PrecompiledOp::DigitSumDigitSumLensum(out, a) => {
                    let a = regs[a];
                    regs[out] = if a <= 18 {
                        2
                    } else {
                        let (x, y) = digit_sum::digit_sum_twice(a);
                        vm::decimal_len(x) + vm::decimal_len(y)
                    }
                },
                PrecompiledOp::Gcd(out, a, b) => {
                    let res = regs[a].unsigned_abs().gcd(&regs[b].unsigned_abs());
                    if res > i64::MAX as u64 {
                        deopt_or_error!(OperationError::IntegerOverflow)
                    }
                    regs[out] = res as i64;
                }
                PrecompiledOp::StackSwap(out, ix, val, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break; // we may be missing few elements on the top -> only deopt is safe
                    }
                    let val = regs[val];
                    regs[out] = stack[ix as usize];
                    stack[ix as usize] = val;
                },
                PrecompiledOp::StackWrite(ix, val, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break;
                    }
                    stack[ix as usize] = regs[val];
                },
                PrecompiledOp::StackRead(out, ix, depth) => {
                    let ix = regs[ix];
                    if ix < 0 || ix + *depth as i64 >= stack.len() as i64 {
                        maybe_cold(); deopt_auto = true; break;
                    }
                    regs[out] = stack[ix as usize];
                },
                PrecompiledOp::LoadConst(out, c) => regs[out] = *c as i64,
                PrecompiledOp::LoadConstPow2Offset(out, pow, offset) => {
                    let val = (1u64 << pow).overflowing_add_signed(*offset as i64).0;
                    regs[out] = val as i64;
                },
                PrecompiledOp::LoadConst64(out, id) => { regs[out] = prog.large_constants[*id as usize] },
                PrecompiledOp::Jump(condition, new_ip) => {
                    if eval_cond(&regs, condition.clone()) {
                        ip = *new_ip as u32;
                    }
                },
                PrecompiledOp::Assert(condition, err, arg) => {
                    if !eval_cond(&regs, condition.clone()) {
                        deopt_or_error!(error_from_code(*err, regs[arg]))
                    }
                },
                PrecompiledOp::DeoptAssert(condition, di) => {
                    if !eval_cond(&regs, condition.clone()) {
                        maybe_cold();
                        deopt_info = Some(*di as u32);
                        break;
                    }
                },
                PrecompiledOp::Done(continue_at) => {
                    simply_done = Some(*continue_at as usize);
                    break;
                },
                PrecompiledOp::Median2(out, a, b) => {
                    let a = regs[a];
                    let b = regs[b];
                    regs[out] = a / 2 + b / 2 + a % 2 + b % 2;
                },
                PrecompiledOp::MedianCursed2(out, a) => {
                    regs[out] = regs[a] / 2 + 1
                },
                PrecompiledOp::Median3(out, a, b, c) => {
                    let mut arr = [regs[a], regs[b], regs[c]];
                    arr.sort_unstable();
                    regs[out] = arr[1];
                },
                PrecompiledOp::MedianCursed3(out, a, b) => {
                    let mut arr = [3, regs[a], regs[b]];
                    arr.sort_unstable();
                    regs[out] = arr[1];
                },
                PrecompiledOp::MedianCursed5(out, a, b, c, d) => {
                    let mut arr = [5, regs[a], regs[b], regs[c], regs[d]];
                    arr.sort_unstable();
                    regs[out] = arr[2];
                }
                PrecompiledOp::KsplangOp(_op) => panic!("probably does not make sense anymore?"),
                PrecompiledOp::KsplangOpWithArg(_op, _) => todo!("probably does not make sense anymore?"),
                PrecompiledOp::KsplangOpsIncrement(x) => { ksplang_ops_done += *x as u64 },
                PrecompiledOp::KsplangOpsIncrementVar(x) => { ksplang_ops_done += u64::try_from(regs[x]).unwrap() },
                PrecompiledOp::KsplangOpsIncrementCond(condition, x) => {
                    if eval_cond(&regs, condition.clone()) {
                        ksplang_ops_done += *x as u64
                    }
                },
                PrecompiledOp::Spill(ix, a) => {
                    while spill.len() <= *ix as usize {
                        spill.push(0);
                    }
                    spill[*ix as usize] = regs[a]
                },
                PrecompiledOp::Unspill(a, ix) => { regs[a] = spill[*ix as usize] }
            }

            debug_assert!(!deopt_auto && deopt_info.is_none() && simply_done.is_none());
            ip += 1;
        }

        if simply_done.is_some() {
            debug_assert!(!deopt_auto && deopt_info.is_none());
            break;
        }

        // switch to performing deopt
        if deopt_auto {
            debug_assert!(deopt_info.is_none());
            assert!(performing_deopt.is_none(), "auto-deopt is not supported when in a deopt (IP is ambiguous). Deopt instructions must not fail");
            match prog.ip2deopt.binary_search_by_key(&ip, |x| x.0) {
                Err(ix) => panic!("Operation {ip} auto-deopts, but corresponding deopt is not recorded? (closest is {ix} {:?}", prog.ip2deopt[ix]),
                Ok(ix) => deopt_info = Some(prog.ip2deopt[ix].1)
            }
        }

        if let Some(deopt_id) = deopt_info {
            deopt_info = None;
            deopt_auto = false;

            let deopt = &prog.deopts[deopt_id as usize];
            performing_deopt = Some(deopt_id);
            ksplang_ops_done += deopt.ksplang_ops_increment as u64;
            program = &deopt.additional_opcodes;
        } else if let Some(deopt_id) = performing_deopt {
            assert_eq!(ip as usize, program.len());
            let deopt = &prog.deopts[deopt_id as usize];
            debug_assert_eq!(&deopt.additional_opcodes[..], program);

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
    })
}

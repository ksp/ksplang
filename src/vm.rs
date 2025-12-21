//! Functions for executing ksplang programs.
use core::panic;
use std::{collections::{BTreeMap, BTreeSet}, fs::{File, create_dir_all}, io::{BufWriter, Write}, mem, path::Path, sync::Arc};
use rustc_hash::{FxHashMap as HashMap};

use num_integer::{Integer, Roots};
use smallvec::{SmallVec, ToSmallVec};
use thiserror::Error;

use crate::{compiler::{self, cfg::GraphBuilder, cfg_interpreter, config::get_config, osmibytecode::{OsmibyteOp, OsmibytecodeBlock}, osmibytecode_vm, precompiler::{NoTrace, Precompiler, TraceProvider}}, digit_sum::digit_sum, funkcia, ops::Op};

#[cfg(test)]
mod tests;

mod bug_shrinker;

/// An implementation of `StateStats` that does not track any statistics.
///
/// This is the best choice if you do not need track anything while the
/// program is executed.
#[derive(Default, Debug, Clone, Copy)]
pub struct NoStats {}

impl Tracer for NoStats {
    #[inline(always)]
    fn push(&mut self, _: i64) {}
    #[inline(always)]
    fn pop(&mut self) {}
    #[inline(always)]
    fn instruction(&mut self, _ip: usize, _op: Op, _: &Result<Effect, OperationError>) -> Result<(), RunError> { Ok(()) }
    #[inline(always)]
    fn should_continue(&mut self, _r: bool, _ip: usize, _op: Op) -> bool { true }
}

/// A trait for tracking statistics about the state of the VM.
/// Can also be used to track pushed and popped values.
///
/// You can implement this trait to track any statistics you need.
pub trait Tracer {
    fn push(&mut self, value: i64);
    fn pop(&mut self);
    fn instruction(&mut self, ip: usize, op: Op, result: &Result<Effect, OperationError>) -> Result<(), RunError>;
    fn should_continue(&mut self, reversed: bool, ip: usize, op: Op) -> bool;
}

/// The internal state of the VM.
#[derive(Clone, Debug)]
struct State<'a, TTracer: Tracer> {
    pub stack: Vec<i64>,
    pub max_stack_size: usize,
    pub pi_digits: &'a [i8],
    pub instructions_run: u64,
    pub instructions_optimized: u64,
    pub instructions_cfg_run: u64,
    pub instructions_obc_run: u64,
    pub blocks_entered: u64,
    pub ip: usize,
    pub reversed: bool,
    pub reverse_undo_stack: Vec<(usize, usize)>,
    pub ops: Arc<Vec<Op>>,
    pub tracer: TTracer,
    pub conf: &'a compiler::config::JitConfig,
}

/// An error that can occur during the execution of ksplang instructions.
#[derive(Error, Debug, Clone, PartialEq, Eq, Hash)]
pub enum OperationError {
    #[error("Removing from an empty stack")]
    PopFailed,
    #[error("Adding to a full stack")]
    PushFailed,
    #[error("Reading from a position out of bounds (index {index})")]
    PeekFailed { index: i64 },
    #[error("Integer overflow")]
    IntegerOverflow,
    #[error("Division by zero")]
    DivisionByZero,
    #[error("Invalid argument for u: {argument}")]
    InvalidArgumentForUniversal { argument: i64 },
    #[error("Negative value used as a length: {value}")]
    NegativeLength { value: i64 },
    #[error("Not enough elements on the stack: {stack_len} elements, {required} required")]
    NotEnoughElements { stack_len: usize, required: i64 },
    #[error("Index out of range: index {index}, stack length {stack_len}")]
    IndexOutOfRange { stack_len: usize, index: i64 },
    #[error("Sorry, not enough pi digits available: available {digits_available}, index {index}")]
    PiOutOfRange { digits_available: usize, index: usize },
    #[error("Negative iteration count: {iterations}")]
    NegativeIterations { iterations: i64 },
    #[error("Negative bit count: {bits}")]
    NegativeBitCount { bits: i64 },
    #[error("Nonpositive value used as a length: {value}")]
    NonpositiveLength { value: i64 },
    #[error("Negative value used as instruction index: {index}")]
    NegativeInstructionIndex { index: i64 },
    #[error("Value used as instruction index is too large: {index}")]
    InstructionOutOfRange { index: i64 },
    #[error("Return instruction index of a `rev` instruction is too large: {index}")]
    RevReturnInstructionOutOfRange { index: i64 },
    #[error("Value is not a valid instruction id: {id}")]
    InvalidInstructionId { id: i64 },
    #[error("Negative praise count: {praises}. You should praise KSP more!")]
    NegativePraiseCount { praises: i64 },
    #[error("Qeq tried to solve 0 = 0. Too many solutions, giving up.")]
    QeqZeroEqualsZero,
    #[error("Argument `a` must be non-negative, it was {value}")]
    ArgumentAMustBeNonNegative { value: i64 },
    #[error("Argument `b` must be non-negative, it was {value}")]
    ArgumentBMustBeNonNegative { value: i64 },
    #[error("Argument `c` must be non-negative, it was {value}")]
    ArgumentCMustBeNonNegative { value: i64 },
    #[error("Internal error in the runtime")]
    Unreachable
}

impl OperationError {
    pub fn with_value(&self, value: i64) -> Self {
        match self {
            Self::PeekFailed { index: _ } => Self::PeekFailed { index: value },
            Self::InvalidArgumentForUniversal { argument: _ } => Self::InvalidArgumentForUniversal { argument: value },
            Self::NegativeLength { value: _ } => Self::NegativeLength { value },
            Self::IndexOutOfRange { stack_len, index: _ } => Self::IndexOutOfRange { stack_len: *stack_len, index: value },
            Self::PiOutOfRange { digits_available, index: _ } => Self::PiOutOfRange { digits_available: *digits_available, index: value as usize },
            Self::NegativeIterations { iterations: _ } => Self::NegativeIterations { iterations: value },
            Self::NegativeBitCount { bits: _ } => Self::NegativeBitCount { bits: value },
            Self::NonpositiveLength { value: _ } => Self::NonpositiveLength { value },
            Self::NegativeInstructionIndex { index: _ } => Self::NegativeInstructionIndex { index: value },
            Self::InstructionOutOfRange { index: _ } => Self::InstructionOutOfRange { index: value },
            Self::RevReturnInstructionOutOfRange { index: _ } => Self::RevReturnInstructionOutOfRange { index: value },
            Self::InvalidInstructionId { id: _ } => Self::InvalidInstructionId { id: value },
            Self::NegativePraiseCount { praises: _ } => Self::NegativePraiseCount { praises: value },
            Self::ArgumentAMustBeNonNegative { value: _ } => Self::ArgumentAMustBeNonNegative { value },
            Self::ArgumentBMustBeNonNegative { value: _ } => Self::ArgumentBMustBeNonNegative { value },
            Self::ArgumentCMustBeNonNegative { value: _ } => Self::ArgumentCMustBeNonNegative { value },
            _ => panic!("Cannot add value to {self:?}"),
        }
    }
}

#[derive(Debug)]
pub enum Effect {
    None,
    SetInstructionPointer(usize),
    SaveAndSetInstructionPointer(usize),
    AddInstructionPointer(i64),
    Timeout,
    RunSubprogramAndAppendResult(Vec<Op>),
    TemporaryReverse(i64),
}

pub(crate) enum QuadraticEquationResult {
    None,
    One(i64),
    Two(i64, i64),
}

/// Solve the quadratic equation ax^2+bx+c=0 and return
/// integer results sorted from smallest to largest.
pub(crate) fn solve_quadratic_equation(
    a: i64,
    b: i64,
    c: i64,
) -> Result<QuadraticEquationResult, OperationError> {
    let a = a as i128;
    let b = b as i128;
    let c = c as i128;

    fn compute_discriminant(a: i128, b: i128, c: i128) -> Option<i128> {
        Some(b.checked_mul(b)?.checked_sub(a.checked_mul(c)?.checked_mul(4)?)?)
    }

    let results: [Option<i64>; 2] = match compute_discriminant(a, b, c) {
        Some(discriminant) => {
            if discriminant < 0 {
                return Ok(QuadraticEquationResult::None);
            }

            let discriminant_sqrt = discriminant.sqrt();
            if discriminant_sqrt * discriminant_sqrt != discriminant {
                return Ok(QuadraticEquationResult::None);
            }

            let mut result1 = None;
            let mut result2 = None;

            if (-b - discriminant_sqrt) % (2 * a) == 0 {
                let result = (-b - discriminant_sqrt) / (2 * a);
                result1 = Some(result.try_into().map_err(|_| OperationError::IntegerOverflow)?);
            }
            if discriminant != 0 && (-b + discriminant_sqrt) % (2 * a) == 0 {
                let result = (-b + discriminant_sqrt) / (2 * a);
                result2 = Some(result.try_into().map_err(|_| OperationError::IntegerOverflow)?);
            }
            [result1, result2]
        }
        None => {
            // discriminant overflow

            // b and c fit into i64, so we have:
            // c.abs() <= (1 << 63)
            // b.abs() <= (1 << 63)
            // b * b <= (1 << 126)
            //
            // discriminant = b * b - 4 * a * c
            //              <= b * b + 4 * a.abs() * c.abs()
            //              <= (1 << 126) + 4 * a.abs() * (1 << 63)
            //              = (1 << 126) + a.abs() * (1 << 65)
            //
            // discriminant overflowed, so if it's nonnegative, we have:
            // discriminant >= (1 << 127)
            //
            // a.abs() * (1 << 65) >= (1 << 127) - (1 << 126) = (1 << 126)
            // a.abs() >= (1 << 61)
            //
            // b.abs() / (2 * a.abs()) <= (1 << 63) / (2 * (1 << 61)) = 2
            //
            // discriminant / (2 * a.abs())^2 <= (b * b + 4 * a.abs() * c.abs()) / (2 * a.abs())^2
            //                                = (b.abs() / (2 * a.abs()))^2 + c.abs() / a.abs()
            //                                <= 2^2 + (1 << 63) / (1 << 61)
            //                                = 8
            //
            // result.abs() <= (b.abs() + discriminant.sqrt()) / (2 * a.abs())
            //              = b.abs() / (2 * a.abs()) + discriminant.sqrt() / (2 * a.abs())
            //              = b.abs() / (2 * a.abs()) + (discriminant / (2 * a.abs())^2).sqrt()
            //              <= 2 + 8.sqrt()
            //              < 4.9
            //
            // This means that all roots are in the interval (-4.9, 4.9), we can try them all

            let mut roots = (-4..5).filter(|&x| {
                let x = x as i128;
                a * x * x + b * x + c == 0
            });
            [roots.next(), roots.next()]
        }
    };

    match results {
        [Some(result1), Some(result2)] => Ok(QuadraticEquationResult::Two(result1, result2)),
        [Some(result1), None] => Ok(QuadraticEquationResult::One(result1)),
        [None, Some(result2)] => Ok(QuadraticEquationResult::One(result2)),
        [None, None] => Ok(QuadraticEquationResult::None),
    }
}

pub(crate) const FACTORIAL_TABLE: [i64; 21] = [
    1,
    1,
    2,
    6,
    24,
    120,
    720,
    5040,
    40320,
    362880,
    3628800,
    39916800,
    479001600,
    6227020800,
    87178291200,
    1307674368000,
    20922789888000,
    355687428096000,
    6402373705728000,
    121645100408832000,
    2432902008176640000,
    //21 => 51090942171709440000, (does not fit into i64)
];

#[inline]
pub(crate) fn abs_factorial(a: i64) -> Result<i64, OperationError> {
    a.checked_abs().filter(|a| *a < FACTORIAL_TABLE.len() as i64).and_then(|x| FACTORIAL_TABLE.get(x as usize).copied()).ok_or(OperationError::IntegerOverflow)
}


#[inline]
pub(crate) fn tetration(num: i64, iters: i64) -> Result<i64, OperationError> {
    if iters < 0 {
        return Err(OperationError::NegativeIterations { iterations: iters });
    }
    Ok(if iters == 0 {
        1
    } else {
        let mut result = num;
        if num == 0 {
            if iters == 1 {
                result = 0;
            } else {
                result = 1;
            }
        } else if num == 1 {
            result = 1;
        } else {
            for _ in 1..iters {
                result = num
                    .checked_pow(
                        result
                            .try_into()
                            .map_err(|_| OperationError::IntegerOverflow)?,
                    )
                    .ok_or(OperationError::IntegerOverflow)?;
            }
        }
        result
    })
}

pub(crate) fn decimal_len(num: i64) -> i64 {
    num.abs_diff(0).checked_ilog10().map(|x| x + 1).unwrap_or(0) as i64
}

pub(crate) fn median(values: &mut [i64]) -> i64 {
    assert_ne!(values.len(), 0);
    values.sort();
    if values.len() % 2 == 0 {
        ((values[values.len() / 2 - 1] as i128 + (values[values.len() / 2] as i128))
            / 2)
        .try_into()
        .unwrap() // Cannot overflow, sum of two i64 divided by 2 fits into i64
    } else {
        values[values.len() / 2]
    }
}

impl<'a, TTracer: Tracer> State<'a, TTracer> {
    fn new(max_stack_size: usize, pi_digits: &'a [i8], ops: Vec<Op>, stack: Vec<i64>, tracer: TTracer) -> Self {
        State {
            max_stack_size,
            pi_digits,
            instructions_run: 0,
            instructions_cfg_run: 0,
            instructions_optimized: 0,
            instructions_obc_run: 0,
            blocks_entered: 0,
            ip: 0,
            reversed: false,
            reverse_undo_stack: vec![],
            stack,
            ops: Arc::new(ops),
            tracer,
            conf: get_config()
        }
    }

    fn change_tracer<T2: Tracer>(self, new_tracer: impl FnOnce(TTracer) -> T2) -> State<'a, T2> {
         State {
            stack: self.stack,
            max_stack_size: self.max_stack_size,
            pi_digits: self.pi_digits,
            instructions_run: self.instructions_run,
            instructions_cfg_run: self.instructions_cfg_run,
            instructions_optimized: self.instructions_optimized,
            instructions_obc_run: self.instructions_obc_run,
            blocks_entered: self.blocks_entered,
            ip: self.ip,
            reversed: self.reversed,
            reverse_undo_stack: self.reverse_undo_stack,
            ops: self.ops,
            conf: self.conf,
            tracer: new_tracer(self.tracer)
        }
    }

    fn swap_tracer<T2: Tracer>(self, new_tracer: T2) -> (TTracer, State<'a, T2>) {
        let mut old = None;
        let result = self.change_tracer(|old_| {
            old = Some(old_);
            new_tracer
        });
        (old.unwrap(), result)
    }

    fn clear(&mut self) {
        self.stack.clear();
    }

    fn pop(&mut self) -> Result<i64, OperationError> {
        self.tracer.pop();
        self.stack.pop().ok_or(OperationError::PopFailed)
    }

    fn push(&mut self, value: i64) -> Result<(), OperationError> {
        if self.stack.len() >= self.max_stack_size {
            return Err(OperationError::PushFailed);
        }

        self.stack.push(value);
        self.tracer.push(value);
        Ok(())
    }

    fn len(&self) -> usize {
        self.stack.len()
    }

    fn peek(&self) -> Result<i64, OperationError> {
        self.stack
            .last()
            .copied()
            .ok_or(OperationError::PeekFailed { index: self.stack.len() as i64 - 1 })
    }

    fn peek_n(&self, n: i64) -> Result<i64, OperationError> {
        let index =
            (self.stack.len() as i64).checked_sub(1 + n).ok_or(OperationError::IntegerOverflow)?;
        if index < 0 {
            return Err(OperationError::PeekFailed { index });
        }

        self.stack.get(index as usize).copied().ok_or(OperationError::PeekFailed { index })
    }

    fn apply(&mut self, op: Op) -> Result<Effect, OperationError> {
        match op {
            Op::Nop => {}
            Op::Praise => {
                let n = self.pop()?;
                if n < 0 {
                    return Err(OperationError::NegativePraiseCount { praises: n });
                }
                for _ in 0..n {
                    self.push(77)?;
                    self.push(225)?;
                    self.push(109)?;
                    self.push(32)?;
                    self.push(114)?;
                    self.push(225)?;
                    self.push(100)?;
                    self.push(32)?;
                    self.push(75)?;
                    self.push(83)?;
                    self.push(80)?;
                }
            }
            Op::Pop => {
                self.pop()?;
            }
            Op::Pop2 => {
                let top = self.pop()?;
                self.pop()?;
                self.push(top)?;
            }
            Op::Max => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(a.max(b))?;
            }
            Op::LSwap => {
                let stack_len = self.stack.len();
                if stack_len > 1 {
                    self.stack.swap(0, stack_len - 1);
                }
            }
            Op::Roll => {
                let n = self.pop()?;
                let x = self.pop()?;

                if n < 0 {
                    return Err(OperationError::NegativeLength { value: n });
                }

                if n > self.len() as i64 {
                    return Err(OperationError::NotEnoughElements {
                        stack_len: self.len(),
                        required: n,
                    });
                }

                if n == 0 {
                    return Ok(Effect::None);
                }

                // Can only overflow is n = i64:MIN, and we do not allow negative values for n.
                // Division by zero is not possible we return early for that case.
                let rotate_by = x.rem_euclid(n);

                let len = self.len();
                self.stack[(len - n as usize)..len].rotate_right(rotate_by as usize);
            }
            Op::FF => {
                let a = self.pop()?;
                let b = self.pop()?;

                if a == 2 && b == 4 {
                    self.push(b)?;
                    self.push(a)?;
                } else {
                    self.clear();
                    while self.len() < self.max_stack_size {
                        self.push(i64::MIN)?;
                    }
                }
            }
            Op::Swap => {
                let i = self.pop()?;

                let len = self.len();
                if i < 0 || i >= self.len() as i64 {
                    return Err(OperationError::IndexOutOfRange { stack_len: len, index: i });
                }

                self.stack.swap(i as usize, len - 1);
            }
            Op::KPi => {
                let index = self
                    .stack
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|&(i, &value)| value == i as i64)
                    .map(|(i, _)| i);

                if let Some(index) = index {
                    let digit =
                        self.pi_digits.get(index).copied().ok_or(OperationError::PiOutOfRange {
                            digits_available: self.pi_digits.len(),
                            index,
                        })?;
                    self.stack[index] = digit as i64;
                } else {
                    let len = self.len();
                    if len > self.pi_digits.len() {
                        return Err(OperationError::PiOutOfRange {
                            digits_available: self.pi_digits.len(),
                            index: self.pi_digits.len(),
                        })?;
                    }

                    self.clear();

                    // We have removed `len` elements from the stack, so we should be able
                    // to add the same amount back even without checking for stack overflow.
                    assert!(len <= self.max_stack_size);
                    self.stack.extend(self.pi_digits.iter().take(len).map(|&x| x as i64));
                }
            }
            Op::Increment => {
                let a = self.pop()?;
                self.push(a.checked_add(1).ok_or(OperationError::IntegerOverflow)?)?;
            }
            Op::Universal => {
                let op = self.pop()?;
                match op {
                    0 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(a.checked_add(b).ok_or(OperationError::IntegerOverflow)?)?;
                    }
                    1 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(
                            a.checked_sub(b)
                                .ok_or(OperationError::IntegerOverflow)?
                                .checked_abs()
                                .ok_or(OperationError::IntegerOverflow)?,
                        )?;
                    }
                    2 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(a.checked_mul(b).ok_or(OperationError::IntegerOverflow)?)?;
                    }
                    3 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        let rem = a.checked_rem(b).ok_or_else(|| {
                            if b == 0 {
                                OperationError::DivisionByZero
                            } else {
                                OperationError::IntegerOverflow
                            }
                        })?;
                        if rem == 0 {
                            self.push(a.checked_div(b).ok_or_else(|| {
                                if b == 0 {
                                    OperationError::DivisionByZero
                                } else {
                                    OperationError::IntegerOverflow
                                }
                            })?)?;
                        } else {
                            self.push(rem)?;
                        }
                    }
                    4 => {
                        let a = self.pop()?;

                        self.push(abs_factorial(a)?)?;
                    }
                    5 => {
                        let a = self.pop()?;
                        let result = if a < 0 {
                            -1
                        } else if a == 0 {
                            0
                        } else {
                            1
                        };

                        self.push(result)?;
                    }
                    other => {
                        return Err(OperationError::InvalidArgumentForUniversal { argument: other })
                    }
                }
            }
            Op::DigitSum => {
                let a = self.peek()?;

                let result = digit_sum(a);
                self.push(result)?;
            }
            Op::Remainder => {
                let a = self.pop()?;
                let b = self.pop()?;
                let rem = a.checked_rem(b).ok_or_else(|| {
                    if b == 0 {
                        OperationError::DivisionByZero
                    } else {
                        OperationError::IntegerOverflow
                    }
                })?;
                self.push(rem)?;
            }
            Op::Modulo => {
                let a = self.pop()?;
                let b = self.pop()?;
                let rem = a.checked_rem_euclid(b).ok_or_else(|| {
                    if b == 0 {
                        OperationError::DivisionByZero
                    } else {
                        OperationError::IntegerOverflow
                    }
                })?;
                self.push(rem)?;
            }
            Op::TetrationNumIters => {
                let num = self.pop()?;
                let iters = self.pop()?;
                let result = tetration(num, iters)?;
                self.push(result)?;
            }
            Op::TetrationItersNum => {
                let iters = self.pop()?;
                let num = self.pop()?;
                let result = tetration(num, iters)?;
                self.push(result)?;
            }
            Op::Median => {
                let n: i64 = self.peek()?;
                let mut values = Vec::new();
                if n <= 0 {
                    return Err(OperationError::NonpositiveLength { value: n });
                }
                if (self.len() as i64) < n {
                    return Err(OperationError::NotEnoughElements {
                        stack_len: self.len(),
                        required: n,
                    });
                }

                for i in 0..n {
                    values.push(self.peek_n(i)?);
                }

                let result = median(&mut values);
                self.push(result)?;
            }
            Op::LenSum => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(decimal_len(a) + decimal_len(b))?;
            }
            Op::Bitshift => {
                let bits = self.pop()?;
                let num = self.pop()?;
                if bits < 0 {
                    return Err(OperationError::NegativeBitCount { bits });
                }

                let result = if bits < i64::BITS as i64 { num << bits } else { 0 };

                self.push(result)?;
            }
            Op::And => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(a & b)?;
            }
            Op::Sum => {
                let mut sum: i128 = 0;
                for value in &self.stack {
                    // Integer overflow can never happen here unless we are summing
                    // more values than can fit in any real RAM.
                    sum = sum.checked_add(*value as i128).ok_or(OperationError::IntegerOverflow)?;
                }
                self.clear();

                self.push(sum.try_into().map_err(|_| OperationError::IntegerOverflow)?)?;
            }
            Op::Gcd2 => {
                // If a or b is i64::MIN, then the result can end up being
                // i64::MAX+1, which overflows, or panics in debug mode.
                // See also https://github.com/rust-num/num-integer/issues/55
                // To avoid this, compute gcd in unsigned numbers
                let a = self.pop()?.unsigned_abs();
                let b = self.pop()?.unsigned_abs();

                let result = a.gcd(&b);
                self.push(result.try_into().map_err(|_| OperationError::IntegerOverflow)?)?;
            }
            Op::GcdN => {
                let n = self.pop()?;
                if n <= 0 {
                    return Err(OperationError::NonpositiveLength { value: n });
                }
                if (self.len() as i64) < n {
                    return Err(OperationError::NotEnoughElements {
                        stack_len: self.len(),
                        required: n,
                    });
                }

                // See note on Gcd2 for why we need unsigned_abs.
                let mut result = self.pop()?.unsigned_abs();

                for _ in 1..n {
                    let value = self.pop()?.unsigned_abs();
                    result = result.gcd(&value);
                }

                self.push(result.try_into().map_err(|_| OperationError::IntegerOverflow)?)?;
            }
            Op::Qeq => {
                let a = self.pop()?;
                let b = self.pop()?;
                let c = self.pop()?;

                // This is a c == 0 equation.
                if a == 0 && b == 0 {
                    // For c == 0, this is true for any x. We generate an error outright
                    // as it would produce too many values.
                    if c == 0 {
                        return Err(OperationError::QeqZeroEqualsZero);
                    }
                    // For c != 0, this is false for any x, so we add nothing.
                    return Ok(Effect::None);
                }
                // If a is zero, this is a linear equation and we need to calculate it differently.
                if a == 0 {
                    if c % b == 0 {
                        let result =
                            (c / b).checked_neg().ok_or(OperationError::IntegerOverflow)?;
                        self.push(result)?;
                    }
                    return Ok(Effect::None);
                }

                // Solve the quadratic equation ax^2+bx+c=0 and put integer results on the stack.
                match solve_quadratic_equation(a, b, c)? {
                    QuadraticEquationResult::None => {}
                    QuadraticEquationResult::One(result) => self.push(result)?,
                    QuadraticEquationResult::Two(result1, result2) => {
                        self.push(result1)?;
                        self.push(result2)?;
                    }
                }
            }
            Op::Funkcia => {
                let a = self.pop()?;
                let b = self.pop()?;
                let result = funkcia::funkcia(a, b) as i64;
                self.push(result)?;
            }
            Op::BulkXor => {
                let n = self.pop()?;
                if (self.len() as i64) < 2 * n {
                    return Err(OperationError::NotEnoughElements {
                        stack_len: self.len(),
                        required: 2 * n,
                    });
                }
                let mut xors = Vec::new();
                for _ in 0..n {
                    let a = if self.pop()? > 0 { 1 } else { 0 };
                    let b = if self.pop()? > 0 { 1 } else { 0 };
                    xors.push(a ^ b);
                }

                for xor in xors.iter().rev() {
                    self.push(*xor)?;
                }
            }
            Op::BranchIfZero => {
                let c = self.peek()?;

                if c != 0 {
                    return Ok(Effect::None);
                }

                let i = self.peek_n(1)?;

                if i < 0 {
                    return Err(OperationError::NegativeInstructionIndex { index: i });
                }

                // The try_into() should only fail in case when usize has a smaller range
                // than i64, in which case this is the correct behavior - we cannot have this
                // amount of instructions anyway.
                return Ok(Effect::SetInstructionPointer(
                    i.try_into().map_err(|_| OperationError::InstructionOutOfRange { index: i })?,
                ));
            }
            Op::Call => {
                let i = self.peek()?;

                if i < 0 {
                    return Err(OperationError::NegativeInstructionIndex { index: i });
                }
                if i >= self.ops.len() as i64 {
                    return Err(OperationError::InstructionOutOfRange { index: i });
                }

                let ip = (self.ip as i64) + if self.reversed { -1 } else { 1 };

                
                self.stack.push(ip);
                return Ok(Effect::SetInstructionPointer(
                     i.try_into().map_err(|_| OperationError::InstructionOutOfRange { index: i })?,
                ));

                // The try_into() should only fail in case when usize has a smaller range
                // than i64, in which case this is the correct behavior - we cannot have this
                // amount of instructions anyway.
                // return Ok(Effect::SaveAndSetInstructionPointer(
                //     i.try_into().map_err(|_| OperationError::InstructionOutOfRange { index: i })?,
                // ));
            }
            Op::Goto => {
                let i = self.peek()?;

                if i < 0 {
                    return Err(OperationError::NegativeInstructionIndex { index: i });
                }

                // The try_into() should only fail in case when usize has a smaller range
                // than i64, in which case this is the correct behavior - we cannot have this
                // amount of instructions anyway.
                return Ok(Effect::SetInstructionPointer(
                    i.try_into().map_err(|_| OperationError::InstructionOutOfRange { index: i })?,
                ));
            }
            Op::Jump => {
                let i = self.peek()?;
                return Ok(Effect::AddInstructionPointer(i + 1));
            }
            Op::Rev => {
                let a = self.pop()?;
                if a < 0 {
                    return Err(OperationError::ArgumentAMustBeNonNegative { value: a });
                }
                let b = self.pop()?;
                if b < 0 {
                    return Err(OperationError::ArgumentBMustBeNonNegative { value: b });
                }

                let offset = if a == 0 {
                    b
                } else {
                    let c = self.pop()?;
                    if c < 0 {
                        return Err(OperationError::ArgumentCMustBeNonNegative { value: c });
                    }
                    match solve_quadratic_equation(a, b, c)? {
                        QuadraticEquationResult::None => b,
                        QuadraticEquationResult::One(x) => x,
                        QuadraticEquationResult::Two(smaller, larger) => {
                            assert!(smaller < larger);
                            larger
                        }
                    }
                };

                return Ok(Effect::TemporaryReverse(offset));
            }
            Op::Sleep => return Ok(Effect::Timeout),
            Op::Deez => {
                let n = self.pop()?;
                if n < 0 {
                    return Err(OperationError::NegativeLength { value: n });
                }
                if (self.len() as i64) < n {
                    return Err(OperationError::NotEnoughElements {
                        stack_len: self.len(),
                        required: n,
                    });
                }
                let mut ops = Vec::new();

                for _ in 0..n {
                    let id = self.pop()?;
                    if id < 0 {
                        return Err(OperationError::InvalidInstructionId { id });
                    }
                    let op = Op::by_id(id as usize)
                        .ok_or(OperationError::InvalidInstructionId { id })?;
                    ops.push(op);
                }

                return Ok(Effect::RunSubprogramAndAppendResult(ops));
            }
        }

        Ok(Effect::None)
    }
}

/// Options for the ksplang virtual machine.
#[derive(Debug, Clone)]
pub struct VMOptions<'a> {
    /// The initial stack of the program.
    initial_stack: &'a [i64],
    /// The maximum size of the stack.
    max_stack_size: usize,
    /// The pi digits to use for the [`Op::KPi`] instruction.
    pi_digits: &'a [i8],
    /// The maximum number of operations to run, if this is reached,
    /// the program will stop with an error.
    ///
    /// Set to [`u64::MAX`] to disable this limit.
    max_op_count: u64,
    /// The maximum number of instructions to run, if this is reached,
    /// the program will stop with a success.
    ///
    /// Set to [`u64::MAX`] to disable this limit.
    stop_after: u64,
}

impl<'a> VMOptions<'a> {
    /// Create a new set of VM options.
    pub fn new(
        stack: &'a [i64],
        max_stack_size: usize,
        pi_digits: &'a [i8],
        max_op_count: u64,
        stop_after: u64,
    ) -> Self {
        Self { initial_stack: stack, max_stack_size, pi_digits, max_op_count, stop_after }
    }
}

impl<'a> Default for VMOptions<'a> {
    fn default() -> Self {
        Self {
            initial_stack: &[],
            max_stack_size: usize::MAX,
            pi_digits: &[],
            max_op_count: u64::MAX,
            stop_after: u64::MAX,
        }
    }
}

/// An error that happened while running a ksplang program.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum RunError {
    /// The stack overflowed. This error should generally not happen,
    /// as this will usually happen within an instruction and trigger
    /// a [`RunError::InstructionFailed`] error instead.
    ///
    /// This is can only be triggered if the sanity check between instruction fails.
    #[error("Stack Overflow")]
    StackOverflow,
    /// A specific instruction failed.
    #[error("Instruction {index} ({instruction}) failed (instruction counter {instruction_counter}): {error}")]
    InstructionFailed {
        /// The instruction which failed
        instruction: Op,
        /// The 0-based index of this instruction in the source code.
        index: usize,
        /// The number of instructions which have been run before this one
        /// May differ from index in case of loops/jumps being present.
        instruction_counter: u64,
        /// The specific error within the instruction.
        error: OperationError,
    },
    /// The program executed more instructions than the maximum instruction limit specified within [`VMOptions`].
    #[error("The program ran for too long ({instruction_counter} instructions had been run).")]
    RunTooLong {
        /// The number of instructions which have been run
        instruction_counter: u64,
    },
    /// The program ran for too long (this is a result of the [`Op::Sleep`] instruction).
    #[error("The program ran for too long (SPANEK).")]
    Timeout,
    /// Tracer interupted the run with custom data
    #[error("Tracer interrupted program execution.")]
    TracerInterrupt(u64, String)
}

/// The succesful result of running a ksplang program.
#[derive(Debug, Clone)]
pub struct RunResult<T: Tracer> {
    /// The resulting stack after the program has finished.
    pub stack: Vec<i64>,
    /// The number of instructions which have been run.
    pub instruction_counter: u64,
    /// The instruction pointer at the end of the program.
    pub instruction_pointer: usize,
    /// Whether the program was reversed at the end (due to [`Op::Rev`]).
    pub reversed: bool,
    /// The internal VM statistics.
    pub tracer: T,
}

impl<T: Tracer> From<State<'_, T>> for RunResult<T> {
    fn from(s: State<T>) -> Self {
        RunResult {
            stack: s.stack,
            instruction_counter: s.instructions_run,
            instruction_pointer: s.ip,
            reversed: s.reversed,
            tracer: s.tracer
        }
    }
}

/// Run a ksplang program with the given options.
///
/// # Example
/// ```
/// use ksplang::ops::Op;
/// use ksplang::vm::{NoStats, run, VMOptions};
/// use ksplang::vm::RunError;
///
/// let ops = vec![Op::Pop, Op::Increment];
/// let stack = vec![1, 4];
/// let options = VMOptions::new(&stack, 10_000, &[3, 1, 4], u64::MAX, u64::MAX);
/// let result = run(&ops, options);
/// assert!(result.is_ok());
/// assert_eq!(result.unwrap().stack, vec![2]);
pub fn run(ops: &[Op], options: VMOptions) -> Result<RunResult<NoStats>, RunError> {
    run_with_stats::<NoStats>(ops, options, NoStats::default())
}

/// Run a ksplang program with the given options and collect statistics.
/// If you do not need statistics, use the [`run`] function instead.
///
/// This may be useful if you want to collect statistics about the state of the program
/// during execution.
pub fn run_with_stats<T: Tracer>(
    ops: &[Op],
    options: VMOptions,
    tracer: T
) -> Result<RunResult<T>, RunError> {
    let mut s: State<T> = State::new(options.max_stack_size, options.pi_digits, ops.to_vec(), options.initial_stack.to_vec(), tracer);
    run_state(&mut s, &options)?;
    Ok(s.into())
}

#[inline]
fn run_state<'a, T: Tracer>(
    s: &mut State<'a, T>,
    options: &VMOptions
) -> Result<(), RunError> {

    enum IPChange {
        Increment,
        Set(usize),
        Add(i64),
    }

    loop {
        while let Some((reverse_ip, return_ip)) = s.reverse_undo_stack.last() {
            if *reverse_ip == s.ip {
                s.reversed = !s.reversed;
                s.ip = *return_ip;
                s.stack.reverse();
                s.reverse_undo_stack.pop();
            } else {
                break;
            }
        }

        if let Some(&op) = s.ops.get(s.ip) {
            if s.instructions_run >= options.stop_after || !s.tracer.should_continue(s.reversed, s.ip, op) {
                return Ok(());
            }
            let ip = s.ip;
            let instruction_counter = s.instructions_run;
            let build_err = |error| RunError::InstructionFailed {
                instruction: op,
                index: ip,
                instruction_counter,
                error,
            };

            let result = s.apply(op);

            s.tracer.instruction(s.ip, op, &result)?;

            let (ip_change, instruction_counter_change) = match result {
                Err(error) => return Err(build_err(error)),
                Ok(Effect::None) => (IPChange::Increment, 1),
                Ok(Effect::SetInstructionPointer(new_ip)) => (IPChange::Set(new_ip), 1),
                Ok(Effect::AddInstructionPointer(offset)) => (IPChange::Add(offset), 1),
                Ok(Effect::SaveAndSetInstructionPointer(new_ip)) => {
                    // This should never overflow for any realistically
                    // possible amount of instructions.
                    let saved_ip = s.ip as i64 + if s.reversed { -1 } else { 1 };
                    s.push(saved_ip).map_err(build_err)?;
                    (IPChange::Set(new_ip), 1)
                }
                Ok(Effect::Timeout) => {
                    return Err(RunError::Timeout);
                }
                Ok(Effect::RunSubprogramAndAppendResult(subprogram_ops)) => {
                    let remaining_ops = options.max_op_count - s.instructions_run;
                    let result = run(
                        &subprogram_ops,
                        VMOptions {
                            initial_stack: &[],
                            max_stack_size: options.max_stack_size,
                            pi_digits: options.pi_digits,
                            max_op_count: remaining_ops,
                            stop_after: options.stop_after - s.instructions_run,
                        },
                    )?;
                    let mut ops_mut = Arc::unwrap_or_clone(mem::take(&mut s.ops));
                    for value in result.stack {
                        let op = Op::by_id(value as usize)
                            .ok_or(build_err(OperationError::InvalidInstructionId { id: value }))?;
                        ops_mut.push(op);
                    }
                    s.ops = Arc::new(ops_mut);
                    (IPChange::Increment, 1 + result.instruction_counter)
                }
                Ok(Effect::TemporaryReverse(offset)) => {
                    let return_ip = if s.reversed {
                        (s.ip as i64)
                            .checked_sub(offset + 1)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    } else {
                        (s.ip as i64)
                            .checked_add(offset + 1)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    };

                    if return_ip < 0 || return_ip >= s.ops.len() as i64 {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: return_ip,
                        }));
                    }

                    s.reversed = !s.reversed;
                    s.reverse_undo_stack.push((s.ip, return_ip as usize));
                    s.stack.reverse();
                    (IPChange::Add(-offset), 1)
                }
            };

            match ip_change {
                IPChange::Increment => {
                    if s.reversed {
                        if s.ip == 0 {
                            s.ip = usize::MAX;
                        } else {
                            s.ip -= 1;
                        }
                    } else {
                        s.ip += 1;
                    }
                }
                IPChange::Set(new_ip) => {
                    if new_ip > s.ops.len() {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: new_ip as i64,
                        }));
                    }
                    if s.conf.should_log(25) {
                        println!("Branching {}->{} {:?} (set) Stack {}, top3: {:?}", s.ip, new_ip, s.ops.get(new_ip), s.stack.len(), s.stack.iter().rev().copied().take(3).collect::<Vec<i64>>());
                    }
                    s.ip = new_ip;
                }
                IPChange::Add(offset) => {
                    let new_ip = if s.reversed {
                        (s.ip as i64)
                            .checked_sub(offset)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    } else {
                        (s.ip as i64)
                            .checked_add(offset)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    };

                    if new_ip < 0 || new_ip > s.ops.len() as i64 {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: new_ip,
                        }));
                    }
                    if s.conf.should_log(25) {
                        println!("Branching {}->{} {:?} (add {}) Stack {}, top3: {:?}", s.ip, new_ip, s.ops.get(new_ip as usize), offset, s.stack.len(), s.stack.iter().rev().copied().take(3).collect::<Vec<i64>>());
                    }
                    s.ip = new_ip as usize;
                }
            }

            s.instructions_run += instruction_counter_change;
            if s.instructions_run >= options.max_op_count {
                return Err(RunError::RunTooLong { instruction_counter: s.instructions_run });
            }

            // Sanity check; instructions should be doing their own checking.
            if s.stack.len() > options.max_stack_size {
                return Err(RunError::StackOverflow);
            }
        } else {
            break;
        }
    }

    Ok(())
}

#[derive(Clone, Debug, PartialEq, Default)]
struct VisitCounter {
    counter: u32,
    supressed: bool,
}

#[derive(Clone, Debug)]
struct OptimizedBlock {
    start_ip: usize,
    reversed: bool,

    stats: BlockStats,

    osmibytecode: Option<OsmibytecodeBlock>,
    cfg: Option<Box<GraphBuilder>>,
    original_tracer: Option<Box<ActualTracer>>,
}

#[derive(Clone, Debug, Default)]
struct BlockStats {
    pub exit_count: HashMap<u64, usize>,
    pub entry_count: usize,
    pub cfg_op_count: u64,
    pub ksplang_op_count: u64,
}

#[derive(Clone, Debug, Default)]
struct Optimizer {
    // last_ip: usize,
    visit_counter: HashMap<usize, VisitCounter>,
    optimized_blocks: HashMap<usize, OptimizedBlock>,
    has_jumped: u8,
    // should_optimize: bool,
    has_interrupted: bool,
    trigger_count: u32,
    // is_fake_state: bool,
}
impl Optimizer {
    fn get_block(&self, rev: bool, ip: usize) -> Option<&OptimizedBlock> {
        let k = if rev { !ip } else { ip };
        self.optimized_blocks.get(&k)
    }

    fn get_block_mut(&mut self, rev: bool, ip: usize) -> Option<&mut OptimizedBlock> {
        let k = if rev { !ip } else { ip };
        self.optimized_blocks.get_mut(&k)
    }

    fn insert_block(&mut self, b: OptimizedBlock) {
        let k = if b.reversed { !b.start_ip } else { b.start_ip };
        self.optimized_blocks.insert(k, b);
    }

    #[inline]
    fn get_visit_counter(&mut self, rev: bool, ip: usize) -> &mut VisitCounter {
        let k = if rev { !ip } else { ip };
        self.visit_counter.entry(k).or_default()
    }
}

impl Tracer for Optimizer {
    #[inline]
    fn push(&mut self, _value: i64) {}

    #[inline]
    fn pop(&mut self) {}

    #[inline]
    fn instruction(&mut self, ip: usize, _op: Op, result: &Result<Effect, OperationError>) -> Result<(), RunError> {
        if !matches!(result, Ok(Effect::None)) {
            match &result {
                // short jumps (you can't really do anything useful with 20 instructions)
                Ok(Effect::AddInstructionPointer(x)) if x.abs() < 20 => {
                    self.has_jumped = 1;
                }
                Ok(Effect::SetInstructionPointer(ip2)) | Ok(Effect::SaveAndSetInstructionPointer(ip2)) if ip2.abs_diff(ip) < 20 => {
                    self.has_jumped = 1;
                }
                Ok(Effect::TemporaryReverse(_)) => {
                    self.has_jumped = 1;
                }
                // back jumps (probably loops)
                Ok(Effect::AddInstructionPointer(x)) if *x < 0 => {
                    self.has_jumped = 3;
                }
                Ok(Effect::SetInstructionPointer(ip2)) | Ok(Effect::SaveAndSetInstructionPointer(ip2)) if *ip2 < ip => {
                    self.has_jumped = 3;
                }
                Ok(Effect::AddInstructionPointer(_)) | Ok(Effect::SetInstructionPointer(_)) | Ok(Effect::SaveAndSetInstructionPointer(_)) => {
                    self.has_jumped = 2;
                }
                _ => { self.has_jumped = 0; }
            }
        }
        Ok(())
    }

    #[inline]
    fn should_continue(&mut self, reversed: bool, ip: usize, op: Op) -> bool {
        fn mark_visit(this: &mut Optimizer, reversed: bool, ip: usize, jump_quality: u8) -> bool {
            let k = if reversed { !ip } else { ip };
            // if this.optimized_blocks.contains_key(&k) {
            //     return false;
            // }

            let ctr = this.visit_counter.entry(k).or_default();
            ctr.counter = ctr.counter.saturating_add(1);
            let trigger_count = if jump_quality >= 3 {
                this.trigger_count
            } else if jump_quality == 2 {
                this.trigger_count.saturating_mul(2)
            } else {
                this.trigger_count.saturating_mul(4)
            };
            if ctr.supressed || ctr.counter < trigger_count {
                this.has_jumped = 0;
                return true;
            }
            this.has_interrupted = true;
            false
        }
        if self.has_jumped != 0 && op == Op::DigitSum {
            mark_visit(self, reversed, ip, self.has_jumped)
        } else {
            true
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ActualTracer {
    pub initial_stack_sample: Box<[i64]>,
    pub values: Vec<i64>,
    pub ips: Vec<usize>,
    pub pop_push_counts: Vec<(u32, u32)>,
    // only stored when we branch:
    // branch address -> (from address. range of instruction index)
    pub ip_lookup: BTreeMap<usize, Vec<(usize, (usize, usize))>>,
    pub total_pushes: u32,
    pub total_pops: u32,
    pub max_count: u32,
    pub record_jump_location: bool,
    pub start_block_location: usize,
    pub start_block_ix: usize,
    pub reversed: bool,
    // pub lazymode: bool,
}

impl Tracer for ActualTracer {
    fn push(&mut self, value: i64) {
        // println!("ActualTracer: push({value})");
        self.values.push(value);
        self.total_pushes = self.total_pushes.saturating_add(1);
    }

    fn pop(&mut self) {
        self.total_pops = self.total_pops.saturating_add(1);
    }

    fn instruction(&mut self, ip: usize, op: Op, result: &Result<Effect, OperationError>) -> Result<(), RunError> {
        // println!("ActualTracer: {ip} {op} {result:?} {} {}", self.total_pops, self.total_pushes);
        if self.total_pops == u32::MAX || self.total_pops == u32::MAX {
            return Err(RunError::TracerInterrupt(0, format!("trace size overflow")))
        }

        if matches!(result, Ok(Effect::SaveAndSetInstructionPointer(_))) {
            todo!("should not happen, hacked elsewhere");
        }

        self.ips.push(ip);
        self.pop_push_counts.push((self.total_pops, self.total_pushes));
        if matches!(result, Ok(Effect::RunSubprogramAndAppendResult(_) | Effect::TemporaryReverse(_))) {
            panic!("nooo")
        }
        if matches!(op, Op::Jump | Op::Goto | Op::BranchIfZero | Op::Call) {
            // record IP change
            self.record_jump_location = true;
            let entry = (self.start_block_location, (self.start_block_ix, self.ips.len()));
            assert_eq!(entry.0.abs_diff(ip) + 1, entry.1.0.abs_diff(entry.1.1), "{ip} {:?}", entry);
            let v = self.ip_lookup.entry(ip).or_default();
            v.push(entry);
        }

        Ok(())
    }

    fn should_continue(&mut self, reversed: bool, ip: usize, op: Op) -> bool {
        assert_eq!(reversed, self.reversed);
        if matches!(op, Op::Sum | Op::Sleep | Op::Rev | Op::Deez | Op::KPi | Op::FF) {
            return false;
        }
        if self.max_count == 0 || self.values.len() > i32::MAX as usize {
            return false;
        }
        self.max_count -= 1;
        if self.record_jump_location {
            self.start_block_location = ip;
            self.start_block_ix = self.ips.len();
        }
        return true;
    }
}

impl ActualTracer {
    pub fn new(init_stack: &[i64], max_count: u32) -> Self {
        Self {
            initial_stack_sample: init_stack.into(),
            max_count,
            ..Default::default()
        }
    }
    fn find_trace_ix<'a>(&'a self, ip: usize) -> impl Iterator<Item = usize> + 'a {
        let rev = self.reversed;
        let dir = if rev { -1 } else { 1 };

        let opt = if rev {
            self.ip_lookup.range(..=ip).rev().next()
        } else {
            self.ip_lookup.range(ip..).next()
        };

        let current_block_ix: Option<usize> = if (self.ips.len() as i64 - self.start_block_ix as i64) < dir * (ip as i64 - self.start_block_location as i64) {
            Some((dir * (ip as i64 - self.start_block_location as i64)) as usize + self.start_block_ix)
        } else {
            None
        };
        let len = self.ips.len();

        current_block_ix.into_iter().chain(
            opt.into_iter().flat_map(|(_block_end, traces)| traces.iter().cloned())
                .filter(move |(block_start, _)| if rev { *block_start >= ip } else { *block_start <= ip })
                .map(move |(block_start, (trace_start, trace_end))| {
                    let offset = if rev { block_start - ip } else { ip - block_start };
                    assert!(trace_start + offset < trace_end);
                    trace_start + offset
                })
        ).filter(move |ix| *ix < len)
    }

    fn get_pushes(&self, trace_ix: usize) -> (u32, SmallVec<[i64; 2]>) {
        let prev = if trace_ix != 0 { self.pop_push_counts[trace_ix - 1] } else { (0, 0) };
        let current = self.pop_push_counts[trace_ix];
        (current.0 - prev.0, self.values[prev.1 as usize..current.1 as usize].to_smallvec())
    }

    fn get_next_ip(&self, trace_ix: usize) -> Option<usize> {
        self.ips.get(trace_ix + 1).copied()
    }
}

impl TraceProvider for ActualTracer {
    fn get_results<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = (u32, smallvec::SmallVec<[i64; 2]>)> + 'a {
        assert_eq!(self.ips.len(), self.pop_push_counts.len());
        self.find_trace_ix(ip).map(|ix: usize| {
            assert!(ix < self.ips.len(), "Tracer translated to invalid index {ix}");
            self.get_pushes(ix)
        })
    }
    fn get_observed_stack_values<'a>(&'a mut self, ip: usize, depths: &[usize]) -> Vec<Vec<i64>> {
        let mut results = Vec::new();
        // for trace_ix in self.find_trace_ix(ip) {
        //     for 
        // }

        // FIXME: vibecoded garbage bruteforce solution
        let mut stack: Vec<i64> = self.initial_stack_sample.to_vec();

        for i in 0..self.ips.len() {
            let curr_ip = self.ips[i];

            if curr_ip == ip {
                let mut combination = Vec::new();
                let mut valid = true;
                for &depth in depths {
                    if depth >= stack.len() {
                        valid = false;
                        break;
                    }
                    // stack is 0..top, depth is from top (0 is top)
                    let index = stack.len() - 1 - depth;
                    combination.push(stack[index]);
                }
                if valid {
                    results.push(combination);
                }
            }

            let (pops, pushes) = self.get_pushes(i);
            let pops = pops as usize;
            if pops > stack.len() {
                stack.clear();
            } else {
                stack.truncate(stack.len() - pops);
            }
            stack.extend(pushes);
        }
        results
    }
    fn is_lazy(&self) -> bool { false }

    fn get_branch_targets<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = usize> {
        self.find_trace_ix(ip).flat_map(|ix| self.get_next_ip(ix))
    }
}

// #[derive(Debug, Clone)]
// pub struct LazyTracer<'a> {
//     state: State<'a, ActualTracer>
// }

#[derive(Debug, Clone)]
struct BlockInterpretResult {
    executed_ksplang: u64,
    executed_obc_ops: u64,
    executed_cfg_ops: u64,
    next_ip: usize,
    exit_point_id: u64,
}

#[derive(Debug, Clone)]
pub struct OptimizingVM {
    program: Vec<Op>,
    allow_deez: bool,
    opt: Optimizer,
    conf: &'static compiler::config::JitConfig,
    obc_regs: osmibytecode_vm::RegFile
}

impl OptimizingVM {
    pub fn new(program: Vec<Op>, allow_deez: bool) -> Self {
        let conf = compiler::config::get_config();
        let mut opt = Optimizer::default();
        opt.trigger_count = conf.trace_trigger_count;
        Self { program, allow_deez, opt, conf, obc_regs: osmibytecode_vm::RegFile::new() }
    }

    pub fn run(&mut self, input_stack: Vec<i64>, opt: VMOptions) -> Result<RunResult<NoStats>, RunError> {
        if let Some(dump_dir) = &self.conf.info_dump_dir {
            create_dir_all(Path::new(dump_dir)).unwrap();
        }
        let program_len = self.program.len();
        let mut s: State<Optimizer> = State::new(opt.max_stack_size, opt.pi_digits, self.program.to_vec(), input_stack, Optimizer::default());
        s.tracer = mem::take(&mut self.opt);
        self.optimize_start(&mut s, &opt);

        let (s, result) = self.run_internal(s, &opt);

        // restore state
        if s.ops.len() > program_len {
            todo!("deez cleanup {}", self.allow_deez);
        }
        let mut s = s.change_tracer(|old| {
            self.opt = old;
            NoStats::default()
        });
        s.ops = Arc::new(vec![]);
        s.pi_digits = &[];
        println!("final state: {:?}", s);

        if let Some(dump_dir) = &self.conf.info_dump_dir {
            let mut stats_file = BufWriter::new(File::create(Path::new(dump_dir).join("stats.csv")).unwrap());
            writeln!(stats_file, "ip,rev,optimized,supressed,hits,cfg_bbs,cfg_ops,cfg_values,osmibyte_ops,osmibyte_jumps,osmibyte_deopts,osmibyte_regs,stat_entries,stat_opt_ops,stat_ksplang_ops,stat_exit_count,stat_exits").unwrap();
            let ip_keys: BTreeSet<usize> = self.opt.visit_counter.keys().chain(self.opt.optimized_blocks.keys()).copied().collect();
            for &key in &ip_keys {
                let rev = key > (isize::MAX as usize);
                let ip = if rev { !key } else { key };
                let opt_block = self.opt.optimized_blocks.get(&key);
                let visit_ctr = self.opt.visit_counter.get(&key);

                write!(stats_file, "{ip},{rev},{},{},{}", opt_block.is_some(), visit_ctr.map_or(false, |x| x.supressed), visit_ctr.map_or(-1, |x| x.counter as i64)).unwrap();

                if let Some(cfg) = opt_block.and_then(|b| b.cfg.as_ref()) {
                    write!(stats_file, ",{},{},{}",
                           cfg.reachable_blocks().count(),
                           cfg.reachable_blocks().map(|b| b.instructions.len()).sum::<usize>(),
                           cfg.values.len()
                    ).unwrap();
                } else {
                    write!(stats_file, ",,,").unwrap();
                }
                if let Some(obc) = opt_block.and_then(|b| b.osmibytecode.as_ref()) {
                    write!(stats_file, ",{},{},{},{}",
                           obc.program.len(),
                           obc.program.iter().filter(|p| matches!(p, OsmibyteOp::Jump(_, _))).count(),
                           obc.deopts.len(),
                           obc.program.iter().flat_map(|p| p.read_regs().into_iter()).collect::<BTreeSet<_>>().len()
                    ).unwrap();
                } else {
                    write!(stats_file, ",,,,").unwrap();
                }
                if let Some(stats) = opt_block.map(|b| &b.stats) {
                    let exits = stats.exit_count.iter().map(|(x, y)| format!("{}_{}:{}", x / u32::MAX as u64, x % u32::MAX as u64, y)).collect::<Vec<_>>();
                    write!(stats_file, ",{},{},{},{},\"{}\"",
                        stats.entry_count,
                        stats.cfg_op_count,
                        stats.ksplang_op_count,
                        stats.exit_count.len(),
                        exits.join(", ")
                    ).unwrap()
                } else {
                    write!(stats_file, ",,,,,").unwrap()
                }

                writeln!(stats_file).unwrap();
            }
        }

        match result {
            Ok(()) => {
                Ok(s.into())
            },
            Err(e) => Err(e)
        }
    }

    fn interpret_block(block: &OptimizedBlock, stack: &mut Vec<i64>, regfile: &mut osmibytecode_vm::RegFile, error_is_deopt: bool) -> Result<BlockInterpretResult, OperationError> {
        if let Some(ob) = &block.osmibytecode {
            let r = if error_is_deopt {
                osmibytecode_vm::interpret_block::<true>(ob, stack, regfile)?
            } else {
                osmibytecode_vm::interpret_block::<false>(ob, stack, regfile)?
            };
            Ok(BlockInterpretResult { executed_ksplang: r.ksplang_interpreted, executed_cfg_ops: 0, next_ip: r.continue_ip, executed_obc_ops: r.bytecode_interpreted, exit_point_id: r.exit_point.encode() })
        } else {
            let r = cfg_interpreter::interpret_cfg(block.cfg.as_ref().unwrap(), stack, error_is_deopt)?;
            Ok(BlockInterpretResult { executed_ksplang: r.executed_ksplang, executed_cfg_ops: r.executed_cfg_ops, next_ip: r.next_ip, executed_obc_ops: 0, exit_point_id: r.exit_point_id  } )
        }
    }

    fn run_internal<'a>(&mut self, mut s: State<'a, Optimizer>, options: &VMOptions) -> (State<'a, Optimizer>, Result<(), RunError>) {
        let should_log_runtime = self.conf.should_log(10);
        let mut last_opt_ops = 1; // avoid infinite loop if ksplang_ops == 0
        loop {
            s.tracer.has_interrupted = false;

            if last_opt_ops == 0 || s.tracer.get_block(s.reversed, s.ip).is_none() {
                if last_opt_ops == 0 {
                    s.tracer.has_jumped = 0; // hack supress breaking
                }
                if should_log_runtime {
                    println!("Running normal interpreter at {} {}", s.ip, s.reversed);
                }
                let r = self::run_state(&mut s, options);
                if r.is_err() || !s.tracer.has_interrupted {
                    return (s, r);
                }
            }

            // add or utilize optimized block:
            if let Some(opt_block) = s.tracer.get_block(s.reversed, s.ip) {
                if should_log_runtime {
                    println!("Running optimized block at {} {} c={}", s.ip, s.reversed, s.instructions_run);
                }
                let verify = self.conf.verify > 1 || (self.conf.verify == 1 && opt_block.stats.entry_count == 0);
                let result = if verify {
                    let (result, state_ret) = bug_shrinker::verify_block(self, s.reversed, s.ip, s, options);
                    s = state_ret;
                    result
                } else {
                    self.obc_regs.clear_debug_set_bitmap();
                    Self::interpret_block(&opt_block, &mut s.stack, &mut self.obc_regs, self.conf.error_as_deopt)
                };

                if should_log_runtime {
                    println!("Optimized block result: {:?}", result);
                }

                match result {
                    Err(_) => todo!("Will be deopt"),
                    Ok(result) => {
                        {
                            let block_stats = s.tracer.get_block_mut(s.reversed, s.ip).unwrap();
                            block_stats.stats.exit_count.entry(result.exit_point_id).and_modify(|c| *c += 1).or_insert(1);
                            block_stats.stats.ksplang_op_count += result.executed_ksplang;
                            block_stats.stats.cfg_op_count += result.executed_cfg_ops + result.executed_obc_ops;
                            block_stats.stats.entry_count += 1;
                        }
                        s.instructions_run += result.executed_ksplang;
                        s.instructions_optimized += result.executed_ksplang;
                        s.instructions_cfg_run += result.executed_cfg_ops;
                        s.instructions_obc_run += result.executed_obc_ops;
                        s.blocks_entered += 1;
                        s.ip = result.next_ip;
                        last_opt_ops = result.executed_ksplang;
                    }
                }
            } else {
                let (s2, result) = self.optimize(s, options);
                s = s2;
                if result.is_err() {
                    return (s, result)
                }
                last_opt_ops = 1;
            }
        }
    }

    fn optimize<'a>(&mut self, s: State<'a, Optimizer>, options: &VMOptions) -> (State<'a, Optimizer>, Result<(), RunError>) {
        // let limit = if s.ip == 167 { 2806 } else { 10_000 };
        let limit = self.conf.adhoc_interpret_limit as usize;
        let start_ip = s.ip;
        let start_stack_size = s.stack.len();
        let reversed = s.reversed;

        let (trace, mut s) = if self.conf.trace_limit == 0 {
            (ActualTracer::default(), s)
        } else {
            let (optimizer, mut st) = s.swap_tracer(ActualTracer::default());
            st.tracer.start_block_location = st.ip;
            st.tracer.max_count = self.conf.trace_limit;
            if st.conf.should_log(2) {
                println!("Starting tracing at {start_ip}");
            }
            let result = run_state(&mut st, options);
            if result.as_ref().is_err_and(|e| !matches!(e, RunError::TracerInterrupt(_, _))) {
                println!("Error while tracing: {:?}", result.as_ref().err().unwrap());
                return (st.swap_tracer(optimizer).1, result);
            }
            if st.conf.should_log(2) {
                println!("Collected trace {start_ip} {}..{} {}: {} IPs, {} values, {} branches", st.ops[start_ip], st.ip, st.ops[st.ip], st.tracer.ips.len(), st.tracer.values.len(), st.tracer.ip_lookup.len());
            }
            if st.tracer.ips.len() < 100 && st.tracer.ips.len() < self.conf.trace_limit as usize {
                println!("ehh tracing interrupted only after {} at {}", st.tracer.ips.len(), st.ip);
                return (st.swap_tracer(optimizer).1, Ok(()));
            }

            st.swap_tracer(optimizer)
        };

        let mut p = Precompiler::new(&s.ops, start_stack_size, reversed, start_ip, limit, self.conf.soften_limits, None, GraphBuilder::new(start_ip), trace);
        p.bb_limit = self.conf.adhoc_branch_limit as usize;
        p.instr_limit = self.conf.adhoc_instr_limit as usize;
        p.interpret();
        let g = p.g;
        let instr_interpreted_count = p.instr_interpreted_count;
        let t = p.tracer;

        self.save_block(&mut s, start_ip, reversed, g, instr_interpreted_count, Some(t));

        (s, Ok(()))
    }

    fn optimize_start<'a>(&self, s: &mut State<'a, Optimizer>, _options: &VMOptions) {
        // try to optimistically optimize from the start
        // makes debugging easier as the VM will just try to optimize the code I give it...
        // let limit = 50_000;
        let limit = self.conf.start_instr_limit as usize;
        if limit == 0 {
            return;
        }
        let mut p = Precompiler::new(&s.ops, s.stack.len(), s.reversed, s.ip, limit, self.conf.soften_limits, None, GraphBuilder::new(s.ip), NoTrace());
        p.bb_limit = self.conf.start_branch_limit as usize;
        p.instr_limit = self.conf.start_instr_limit as usize;
        p.interpret();

        self.save_block(s, 0, false, p.g, p.instr_interpreted_count, None);
    }

    fn save_block(&self, s: &mut State<'_, Optimizer>, start_ip: usize, reversed: bool, cfg: GraphBuilder, gain_from: usize, tracer: Option<ActualTracer>) {
        let cfg_instr_count = cfg.reachable_blocks().map(|b| b.instructions.len()).count();
        if self.conf.min_gain_mul as usize * cfg_instr_count + (self.conf.min_gain_const as usize) > gain_from {
            if self.conf.should_log(2) {
                println!("Not optimized enough at {start_ip} {reversed}: From {gain_from} ksplang to {cfg_instr_count} min gain = {} + {}x", self.conf.min_gain_const, self.conf.min_gain_mul);
            }
            let ctr = s.tracer.get_visit_counter(reversed, start_ip);
            ctr.supressed = true;
            return;
        }
        let osmibytecode =
            self.conf.allow_osmibyte_backend.then(|| OsmibytecodeBlock::from_cfg(&cfg));

        if let Some(dump_dir) = &self.conf.info_dump_dir {
            use std::io::Write;
            let mut f = BufWriter::new(File::create(Path::new(dump_dir).join(&format!("compiled-{}{}-cfg.txt", start_ip, if reversed { "-rev" } else { "" }))).unwrap());
            writeln!(f, "Optimized at {start_ip} rev={reversed}: {cfg_instr_count} instructions, from {gain_from} ksplang").unwrap();
            writeln!(f, "{cfg}").unwrap();
            if let Some(obc) = &osmibytecode {
                writeln!(f, "{obc}").unwrap();
            }
        }

        if self.conf.should_log(2) {
            println!("Optimized at {}{}:", start_ip, reversed.then_some(" reversed").unwrap_or(""));
            println!("{}", cfg);
            println!("");
            if let Some(obc) = &osmibytecode {
                println!("Osmibytecode:");
                println!("{}", obc);
                println!("");
            }
            println!("===================================================================");
        }

        let b = OptimizedBlock {
            cfg: (osmibytecode.is_none() || self.conf.verify > 0).then(|| Box::new(cfg)),
            osmibytecode: osmibytecode,
            original_tracer: (self.conf.verify >= 3 && tracer.is_some()).then(|| Box::new(tracer.unwrap())),
            reversed: reversed,
            start_ip: start_ip,
            stats: BlockStats::default(),
        };
        s.tracer.insert_block(b);
    }
}

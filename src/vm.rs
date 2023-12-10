use num_integer::{Integer, Roots};
use std::collections::HashMap;
use thiserror::Error;

use crate::ops::Op;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
struct State<'a> {
    stack: Vec<i64>,
    max_stack_size: usize,
    pi_digits: &'a [i8],
}

#[derive(Error, Debug, PartialEq, Eq)]
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
}

enum Effect {
    None,
    SetInstructionPointer(usize),
    SaveAndSetInstructionPointer(usize),
    AddInstructionPointer(i64),
    Timeout,
    RunSubprogramAndAppendResult(Vec<Op>),
    TemporaryReverse(i64),
}

enum QuadraticEquationResult {
    None,
    One(i64),
    Two(i64, i64),
}

/// Solve the quadratic equation ax^2+bx+c=0 and return
/// integer results sorted from smallest to largest.
fn solve_quadratic_equation(
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

impl<'a> State<'a> {
    fn new(max_stack_size: usize, pi_digits: &'a [i8]) -> Self {
        State { stack: Vec::new(), max_stack_size, pi_digits }
    }

    fn clear(&mut self) {
        self.stack.clear();
    }

    fn pop(&mut self) -> Result<i64, OperationError> {
        self.stack.pop().ok_or(OperationError::PopFailed)
    }

    fn push(&mut self, value: i64) -> Result<(), OperationError> {
        if self.stack.len() >= self.max_stack_size {
            return Err(OperationError::PushFailed);
        }

        self.stack.push(value);
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
                    while self.stack.len() < self.max_stack_size {
                        self.stack.push(i64::MIN);
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
                        let factorial =
                            match a.checked_abs().ok_or(OperationError::IntegerOverflow)? {
                                0 => 1,
                                1 => 1,
                                2 => 2,
                                3 => 6,
                                4 => 24,
                                5 => 120,
                                6 => 720,
                                7 => 5040,
                                8 => 40320,
                                9 => 362880,
                                10 => 3628800,
                                11 => 39916800,
                                12 => 479001600,
                                13 => 6227020800,
                                14 => 87178291200,
                                15 => 1307674368000,
                                16 => 20922789888000,
                                17 => 355687428096000,
                                18 => 6402373705728000,
                                19 => 121645100408832000,
                                20 => 2432902008176640000,
                                //21 => 51090942171709440000, (does not fit into i64)
                                _ => return Err(OperationError::IntegerOverflow),
                            };

                        self.push(factorial)?;
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
                fn digit_sum(num: i64) -> i64 {
                    // This is a workaround for i64::MIN.abs() not being a valid i64 value.
                    if num == i64::MIN {
                        return 89;
                    }
                    let mut num = num.abs();
                    let mut sum = 0;
                    while num > 0 {
                        sum += num % 10;
                        num /= 10;
                    }
                    sum
                }

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
                if iters < 0 {
                    return Err(OperationError::NegativeIterations { iterations: iters });
                }
                let result = if iters == 0 {
                    1
                } else {
                    let mut result = num;
                    for _ in 1..iters {
                        result = num
                            .checked_pow(
                                result.try_into().map_err(|_| OperationError::IntegerOverflow)?,
                            )
                            .ok_or(OperationError::IntegerOverflow)?;
                    }
                    result
                };
                self.push(result)?;
            }
            Op::TetrationItersNum => {
                let iters = self.pop()?;
                let num = self.pop()?;
                if iters < 0 {
                    return Err(OperationError::NegativeIterations { iterations: iters });
                }
                let result = if iters == 0 {
                    1
                } else {
                    let mut result = num;
                    for _ in 1..iters {
                        result = num
                            .checked_pow(
                                result.try_into().map_err(|_| OperationError::IntegerOverflow)?,
                            )
                            .ok_or(OperationError::IntegerOverflow)?;
                    }
                    result
                };
                self.push(result)?;
            }
            Op::Median => {
                let n = self.peek()?;
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

                values.sort();
                let result: i64 = if values.len() % 2 == 0 {
                    ((values[values.len() / 2 - 1] as i128 + (values[values.len() / 2] as i128))
                        / 2)
                    .try_into()
                    .map_err(|_| OperationError::IntegerOverflow)?
                } else {
                    values[values.len() / 2]
                };
                self.push(result)?;
            }
            Op::LenSum => {
                let a = self.pop()?;
                let b = self.pop()?;
                fn len(num: i64) -> i64 {
                    // We cannot use .abs() on i64::MIN
                    if num == i64::MIN {
                        return 19;
                    }

                    num.abs().checked_ilog10().map(|x| x + 1).unwrap_or(0) as i64
                }
                self.push(len(a) + len(b))?;
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
                    let b = b as i128;
                    let c = c as i128;

                    if -c % b == 0 {
                        let result =
                            (-c / b).try_into().map_err(|_| OperationError::IntegerOverflow)?;
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
                const MOD: i64 = 1_000_000_007;

                let a = self.pop()?;
                let b = self.pop()?;

                fn factorize(mut a: i64) -> HashMap<i64, usize> {
                    let mut counts_by_divisor = HashMap::new();
                    let mut i = 2;
                    while (i * i) as i128 <= a as i128 {
                        while a % i == 0 {
                            counts_by_divisor.entry(i).and_modify(|x| *x += 1).or_insert(1);
                            a /= i;
                        }

                        i += 1;
                    }
                    if a > 1 {
                        counts_by_divisor.entry(a).and_modify(|x| *x += 1).or_insert(1);
                    }
                    counts_by_divisor
                }

                let a_factors = factorize(a);
                let b_factors = factorize(b);

                let mut result = 1i64;
                let mut apply_factors = |factors: &HashMap<i64, usize>,
                                         the_other_factors: &HashMap<i64, usize>|
                 -> Result<(), OperationError> {
                    for (factor, count) in factors {
                        if the_other_factors.contains_key(&factor) {
                            continue;
                        }
                        for _ in 0..*count {
                            result = (result
                                .checked_mul(factor % MOD)
                                .ok_or(OperationError::IntegerOverflow)?
                                % MOD)
                                % MOD;
                        }
                    }
                    Ok(())
                };

                apply_factors(&a_factors, &b_factors)?;
                apply_factors(&b_factors, &a_factors)?;

                if result == 1 {
                    result = 0
                }
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

                // The try_into() should only fail in case when usize has a smaller range
                // than i64, in which case this is the correct behavior - we cannot have this
                // amount of instructions anyway.
                return Ok(Effect::SaveAndSetInstructionPointer(
                    i.try_into().map_err(|_| OperationError::InstructionOutOfRange { index: i })?,
                ));
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

pub struct VMOptions<'a> {
    initial_stack: &'a [i64],
    max_stack_size: usize,
    pi_digits: &'a [i8],
    max_op_count: u64,
}

impl<'a> VMOptions<'a> {
    pub fn new(
        stack: &'a [i64],
        max_stack_size: usize,
        pi_digits: &'a [i8],
        max_op_count: u64,
    ) -> Self {
        Self { initial_stack: stack, max_stack_size, pi_digits, max_op_count }
    }
}

impl<'a> Default for VMOptions<'a> {
    fn default() -> Self {
        Self {
            initial_stack: &[],
            max_stack_size: usize::MAX,
            pi_digits: &[],
            max_op_count: u64::MAX,
        }
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum RunError {
    #[error("Stack Overflow")]
    StackOverflow,
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
    #[error("The program ran for too long ({instruction_counter} instructions had been run).")]
    RunTooLong {
        /// The number of instructions which have been run
        instruction_counter: u64,
    },
}

#[derive(Debug, Clone)]
pub struct RunResult {
    pub stack: Vec<i64>,
    pub instruction_counter: u64,
}

pub fn run(ops: &[Op], options: VMOptions) -> Result<RunResult, RunError> {
    let mut state = State::new(options.max_stack_size, options.pi_digits);
    state.stack = options.initial_stack.to_vec();

    let mut ops = ops.to_vec();

    let mut reverse_undo_stack = Vec::new();

    let mut instructions_run = 0u64;
    let mut ip = 0usize;
    let mut reversed = false;

    enum IPChange {
        Increment,
        Set(usize),
        Add(i64),
    }

    loop {
        while let Some((reverse_ip, return_ip)) = reverse_undo_stack.last() {
            if *reverse_ip == ip {
                reversed = !reversed;
                ip = *return_ip;
                state.stack.reverse();
                reverse_undo_stack.pop();
            } else {
                break
            }
        }

        if let Some(&op) = ops.get(ip) {
            let build_err = |error| RunError::InstructionFailed {
                instruction: op,
                index: ip,
                instruction_counter: instructions_run,
                error,
            };

            let (ip_change, instruction_counter_change) = match state.apply(op) {
                Err(error) => return Err(build_err(error)),
                Ok(Effect::None) => (IPChange::Increment, 1),
                Ok(Effect::SetInstructionPointer(new_ip)) => (IPChange::Set(new_ip), 1),
                Ok(Effect::AddInstructionPointer(offset)) => (IPChange::Add(offset), 1),
                Ok(Effect::SaveAndSetInstructionPointer(new_ip)) => {
                    // This should never overflow for any realistically
                    // possible amount of instructions.
                    let saved_ip = ip as i64 + if reversed { -1 } else { 1 };
                    state.push(saved_ip).map_err(build_err)?;
                    (IPChange::Set(new_ip), 1)
                }
                Ok(Effect::Timeout) => {
                    return Err(RunError::RunTooLong { instruction_counter: instructions_run + 1 });
                }
                Ok(Effect::RunSubprogramAndAppendResult(subprogram_ops)) => {
                    let remaining_ops = options.max_op_count - instructions_run;
                    let result = run(
                        &subprogram_ops,
                        VMOptions {
                            initial_stack: &[],
                            max_stack_size: options.max_stack_size,
                            pi_digits: options.pi_digits,
                            max_op_count: remaining_ops,
                        },
                    )?;
                    for value in result.stack {
                        let op = Op::by_id(value as usize)
                            .ok_or(build_err(OperationError::InvalidInstructionId { id: value }))?;
                        ops.push(op);
                    }
                    (IPChange::Increment, 1 + result.instruction_counter)
                }
                Ok(Effect::TemporaryReverse(offset)) => {
                    let return_ip = if reversed {
                        (ip as i64)
                            .checked_sub(offset + 1)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    } else {
                        (ip as i64)
                            .checked_add(offset + 1)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    };

                    if return_ip < 0 || return_ip >= ops.len() as i64 {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: return_ip,
                        }));
                    }

                    reversed = !reversed;
                    reverse_undo_stack.push((ip, return_ip as usize));
                    state.stack.reverse();
                    (IPChange::Add(-offset), 1)
                }
            };

            match ip_change {
                IPChange::Increment => {
                    if reversed {
                        if ip == 0 {
                            ip = usize::MAX;
                        } else {
                            ip -= 1;
                        }
                    } else {
                        ip += 1;
                    }
                }
                IPChange::Set(new_ip) => {
                    if new_ip >= ops.len() {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: new_ip as i64,
                        }));
                    }
                    ip = new_ip;
                }
                IPChange::Add(offset) => {
                    let new_ip = if reversed {
                        (ip as i64)
                            .checked_sub(offset)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    } else {
                        (ip as i64)
                            .checked_add(offset)
                            .ok_or(build_err(OperationError::IntegerOverflow))?
                    };

                    if new_ip < 0 || new_ip >= ops.len() as i64 {
                        return Err(build_err(OperationError::InstructionOutOfRange {
                            index: new_ip,
                        }));
                    }
                    ip = new_ip as usize;
                }
            }

            instructions_run += instruction_counter_change;
            if instructions_run >= options.max_op_count {
                return Err(RunError::RunTooLong { instruction_counter: instructions_run });
            }

            // Sanity check; instructions should be doing their own checking.
            if state.stack.len() > options.max_stack_size {
                return Err(RunError::StackOverflow);
            }
        } else {
            break;
        }
    }

    Ok(RunResult { stack: state.stack, instruction_counter: instructions_run })
}

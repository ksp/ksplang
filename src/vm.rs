use num_integer::{Integer, Roots};
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
}

enum Effect {
    None,
    SetInstructionPointer(usize),
    SaveAndSetInstructionPointer(usize),
    AddInstructionPointer(i64),
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
        if self.stack.len() >= self.max_stack_size - 1 {
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

    /// Indexed from the bottom of the stack
    fn get(&self, index: usize) -> Option<i64> {
        self.stack.get(index).copied()
    }

    fn apply(&mut self, op: Op) -> Result<Effect, OperationError> {
        match op {
            Op::Nop => {}
            Op::Praise => {
                let n = self.pop()?;
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
                    self.clear();
                    while self.stack.len() < self.max_stack_size {
                        self.stack.push(i64::MIN);
                    }
                } else {
                    self.push(b)?;
                    self.push(a)?;
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
                    // TODO: fix overflow with i64::MIN
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
                if n < 0 {
                    return Err(OperationError::NegativeLength { value: n });
                }
                if n == 0 {
                    return Err(OperationError::DivisionByZero);
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
                let result = if values.len() % 2 == 0 {
                    (values[values.len() / 2 - 1] + values[values.len() / 2]) / 2
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
                let a = self.pop()?;
                let b = self.pop()?;

                // If a or b is i64::MIN and the other value 0, then the result ends up being
                // i64::MAX+1, which overflows, or panics in debug mode.
                // See also https://github.com/rust-num/num-integer/issues/55
                if a == 0 && b == i64::MIN || b == 0 && a == i64::MIN {
                    return Err(OperationError::IntegerOverflow);
                } else {
                    self.push(a.gcd(&b))?;
                }
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

                let mut result = match self.pop()? {
                    i64::MIN => return Err(OperationError::IntegerOverflow),
                    value => value.abs(),
                };

                for _ in 1..n {
                    let value = self.pop()?;
                    // See note on Gcd2 for reasoning why this check is necessary.
                    if result == 0 && value == i64::MIN || result == i64::MIN && value == 0 {
                        return Err(OperationError::IntegerOverflow);
                    }
                    result = result.gcd(&value);
                }

                self.push(result)?;
            }
            Op::Qeq => {
                let a = self.pop()? as i128;
                let b = self.pop()? as i128;
                let c = self.pop()? as i128;

                // Solve the quadratic equation ax^2+bx+c=0 and put integer results on the stack.

                let discriminant = b * b - 4 * a * c;
                if discriminant < 0 {
                    return Ok(Effect::None);
                }

                let discriminant_sqrt = discriminant.sqrt();
                if discriminant_sqrt * discriminant_sqrt != discriminant {
                    return Ok(Effect::None);
                }

                if (-b - discriminant_sqrt) % (2 * a) == 0 {
                    let result = (-b - discriminant_sqrt) / (2 * a);
                    self.push(result.try_into().map_err(|_| OperationError::IntegerOverflow)?)?;
                }
                if discriminant != 0 && (-b + discriminant_sqrt) % (2 * a) == 0 {
                    let result = (-b + discriminant_sqrt) / (2 * a);
                    self.push(result.try_into().map_err(|_| OperationError::IntegerOverflow)?)?;
                }
            }
            Op::Funkcia => {
                todo!()
            }
            Op::BulkPairwiseOfSomethingBinary => {
                todo!()
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
                return Ok(Effect::AddInstructionPointer(i));
            }
            Op::Rev => {
                todo!()
            }
            Op::Sleep => {
                todo!()
            }
            Op::Deez => {
                todo!()
            }
        }

        Ok(Effect::None)
    }
}

pub struct VMOptions<'a> {
    initial_stack: &'a [i64],
    max_stack_size: usize,
    pi_digits: &'a [i8],
}

impl<'a> VMOptions<'a> {
    pub fn new(stack: &'a [i64], max_stack_size: usize, pi_digits: &'a [i8]) -> Self {
        Self { initial_stack: stack, max_stack_size, pi_digits }
    }
}

impl<'a> Default for VMOptions<'a> {
    fn default() -> Self {
        Self { initial_stack: &[], max_stack_size: usize::MAX, pi_digits: &[] }
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum RunError {
    #[error("Stack Overflow")]
    StackOverflow,
    #[error("Instruction {index:?} ({instruction:?}) failed (instruction counter {instruction_counter:?}): {error}")]
    InstructionFailed {
        /// The instruction which failed
        instruction: Op,
        /// The 0-based index of this instruction in the source code.
        index: usize,
        /// The number of instructions which have been run before this one
        /// May differ from index in case of loops/jumps being present.
        instruction_counter: usize,
        /// The specific error within the instruction.
        error: OperationError,
    },
}

pub fn run(ops: &[Op], options: VMOptions) -> Result<Vec<i64>, RunError> {
    let mut state = State::new(options.max_stack_size, options.pi_digits);
    state.stack = options.initial_stack.to_vec();

    let mut instructions_run = 0;
    let mut ip = 0;
    loop {
        if let Some(op) = ops.get(ip) {
            match state.apply(*op) {
                Err(error) => {
                    return Err(RunError::InstructionFailed {
                        instruction: *op,
                        index: ip,
                        instruction_counter: instructions_run,
                        error,
                    });
                }
                Ok(Effect::None) => ip += 1,
                Ok(Effect::SetInstructionPointer(new_ip)) => {
                    if new_ip >= ops.len() {
                        return Err(RunError::InstructionFailed {
                            instruction: *op,
                            index: ip,
                            instruction_counter: instructions_run,
                            error: OperationError::InstructionOutOfRange { index: new_ip as i64 },
                        });
                    }
                    ip = new_ip;
                }
                Ok(Effect::AddInstructionPointer(offset)) => {
                    let new_ip = ip as i64 + 1 + offset;

                    if new_ip < 0 || new_ip >= ops.len() as i64 {
                        return Err(RunError::InstructionFailed {
                            instruction: *op,
                            index: ip,
                            instruction_counter: instructions_run,
                            error: OperationError::InstructionOutOfRange { index: new_ip},
                        });
                    }
                    ip = new_ip as usize;
                }
                Ok(Effect::SaveAndSetInstructionPointer(new_ip)) => {
                    let build_err = |error| {
                        RunError::InstructionFailed {
                            instruction: *op,
                            index: ip,
                            instruction_counter: instructions_run,
                            error
                        }
                    };

                    if new_ip >= ops.len() {
                        return Err(build_err(OperationError::InstructionOutOfRange { index: new_ip as i64 }));
                    }
                    let saved_ip = (ip as i64).checked_add(1).ok_or(build_err(OperationError::IntegerOverflow))?;
                    state.push(saved_ip).map_err(build_err)?;
                    ip = new_ip;
                }
            }

            // Sanity check; instructions should be doing their own checking.
            if state.stack.len() > options.max_stack_size {
                return Err(RunError::StackOverflow);
            }
        } else {
            break;
        }

        instructions_run += 1;
    }

    Ok(state.stack)
}

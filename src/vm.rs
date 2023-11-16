use thiserror::Error;

use crate::ops::Op;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug)]
struct State {
    stack: Vec<i64>,
    max_stack_size: usize,
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
}

impl State {
    fn new(max_stack_size: usize) -> Self {
        State { stack: Vec::new(), max_stack_size }
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

    fn apply(&mut self, op: Op) -> Result<(), OperationError> {
        match op {
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
                todo!()
            }
            Op::LRoll => {
                todo!()
            }
            Op::FF => {
                todo!()
            }
            Op::Swap => {
                todo!()
            }
            Op::KPi => {
                todo!()
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
                        // TODO: document this is rem, not rem_euclid
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
                    other => return Err(OperationError::InvalidArgumentForUniversal { argument: other })
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
            Op::Tetration => {
                let m = self.pop()?;
                let n = self.pop()?;
                let mut result = m;
                for _ in 1..n {
                    result = m
                        .checked_pow(
                            result.try_into().map_err(|_| OperationError::IntegerOverflow)?,
                        )
                        .ok_or(OperationError::IntegerOverflow)?;
                }
                self.push(result)?;
            }
            Op::Median => {
                let n = self.peek()?;
                let mut values = Vec::new();
                for i in 0..n {
                    values.push(self.peek_n(i)?);
                }

                values.sort();
                let result = if values.len() % 2 == 0 {
                    (values[values.len() / 2] + values[values.len() / 2 + 1]) / 2
                } else {
                    values[values.len() / 2]
                };
                self.push(result)?;
            }
            Op::LenSum => {
                todo!()
            }
            Op::Sum => {
                let mut sum: i64 = 0;
                for value in &self.stack {
                    sum = sum.checked_add(*value).ok_or(OperationError::IntegerOverflow)?;
                }
                self.clear();
                self.push(sum)?;
            }
            Op::Bitshift => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(a << b)?;
            }
            Op::Gcd2 => {
                todo!()
            }
            Op::GcdN => {
                todo!()
            }
            Op::Qeq => {
                todo!()
            }
            Op::Funkcia => {
                todo!()
            }
            Op::BulkPairwiseOfSomethingBinary => {
                todo!()
            }
            Op::BranchIfZero => {
                todo!()
            }
            Op::Call => {
                todo!()
            }
            Op::Goto => {
                todo!()
            }
            Op::Jump => {
                todo!()
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

        Ok(())
    }
}

pub struct VMOptions {
    stack: Vec<i64>,
    max_stack_size: usize,
}

impl VMOptions {
    pub fn new(stack: &[i64], max_stack_size: usize) -> Self {
        Self { stack: stack.to_vec(), max_stack_size }
    }
}

impl Default for VMOptions {
    fn default() -> Self {
        Self { stack: Vec::new(), max_stack_size: usize::MAX }
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
    let mut state = State::new(options.max_stack_size);
    state.stack = options.stack;

    let mut instructions_run = 0;
    for (i, op) in ops.iter().enumerate() {
        if let Err(error) = state.apply(*op) {
            return Err(RunError::InstructionFailed {
                instruction: *op,
                index: i,
                instruction_counter: instructions_run,
                error,
            });
        }

        // Sanity check; instructions should be doing their own checking.
        if state.stack.len() > options.max_stack_size {
            return Err(RunError::StackOverflow);
        }

        instructions_run += 1;
    }

    Ok(state.stack)
}

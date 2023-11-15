use thiserror::Error;

use crate::ops::Op;

#[derive(Clone, Debug)]
struct State {
    stack: Vec<i64>,
}

impl State {
    fn new() -> Self {
        State { stack: Vec::new() }
    }

    fn clear(&mut self) {
        self.stack.clear();
    }

    fn pop(&mut self) -> Option<i64> {
        self.stack.pop()
    }

    fn push(&mut self, value: i64) -> Option<()> {
        self.stack.push(value);
        Some(())
    }

    fn len(&self) -> usize {
        self.stack.len()
    }

    fn peek(&self) -> Option<i64> {
        self.stack.last().copied()
    }

    fn peek_n(&self, n: usize) -> Option<i64> {
        self.stack.get(self.stack.len().checked_sub(1 + n)?).copied()
    }

    /// Indexed from the bottom of the stack
    fn get(&self, index: usize) -> Option<i64> {
        self.stack.get(index).copied()
    }

    fn apply(&mut self, op: Op) -> Option<()> {
        match op {
            Op::Praise => {
                let n = self.pop()?;
                // TODO: document that this is unicode, not ascii
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
                self.push(top);
            }
            Op::Max => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(a.max(b));
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
                self.push(a.checked_add(1)?);
            }
            Op::Universal => {
                let op = self.pop()?;
                match op {
                    0 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(a.checked_add(b)?)?;
                    }
                    1 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(a.checked_sub(b)?.abs())?;
                    }
                    2 => {
                        let a = self.pop()?;
                        let b = self.pop()?;
                        self.push(a.checked_mul(b)?)?;
                    }
                    3 => {
                        // TODO: document this is rem, not rem_euclid
                        let a = self.pop()?;
                        let b = self.pop()?;
                        let rem = a.checked_rem(b)?;
                        if rem == 0 {
                            self.push(a.checked_div(b)?)?;
                        } else {
                            self.push(rem)?;
                        }
                    }
                    4 => {
                        let a = self.pop()?;
                        let factorial = match a.abs() {
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
                            //21 =>  51090942171709440000,
                            _ => return None,
                        };

                        self.push(factorial)?;
                        ()
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

                        self.push(result);
                        ()
                    }
                    _ => return None,
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
                self.push(result);
            }
            Op::Remainder => {
                let a = self.pop()?;
                let b = self.pop()?;
                self.push(a.checked_rem(b)?)?;
            }
            Op::Tetration => {
                let m = self.pop()?;
                let n = self.pop()?;
                let mut result = m;
                for _ in 1..n {
                    result = m.checked_pow(result.try_into().ok()?)?;
                }
                self.push(result)?;
            }
            Op::Median => {
                let n = self.peek()?;
                let mut values = Vec::new();
                for i in 0..n {
                    values.push(self.peek_n(i as usize)?);
                }

                values.sort();
                let result = if values.len() % 2 == 0 {
                    (values[values.len() / 2] + values[values.len() / 2 + 1]) / 2
                } else {
                    values[values.len() / 2]
                };
                self.push(result);
            }
            Op::LenSum => {
                todo!()
            }
            Op::Sum => {
                let mut sum: i64 = 0;
                for value in &self.stack {
                    sum = sum.checked_add(*value)?;
                }
                self.clear();
                self.push(sum);
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

        Some(())
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
    #[error("Instruction {index:?} ({instruction:?}) failed (instruction counter {instruction_counter:?})")]
    InstructionFailed {
        /// The instruction which failed
        instruction: Op,
        /// The 0-based index of this instruction in the source code.
        index: usize,
        /// The number of instructions which have been run before this one
        /// May differ from index in case of loops/jumps being present.
        instruction_counter: usize,
    },
}

pub fn run(ops: &[Op], options: VMOptions) -> Result<Vec<i64>, RunError> {
    let mut state = State::new();
    state.stack = options.stack;

    let mut instructions_run = 0;
    for (i, op) in ops.iter().enumerate() {
        if state.apply(*op).is_none() {
            return Err(RunError::InstructionFailed {
                instruction: *op,
                index: i,
                instruction_counter: instructions_run,
            });
        }
        if state.stack.len() > options.max_stack_size {
            return Err(RunError::StackOverflow);
        }
        instructions_run += 1;
    }

    Ok(state.stack)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(initial_stack: Vec<i64>, ops: Vec<Op>) -> Vec<i64> {
        super::run(&ops, VMOptions::new(&initial_stack, usize::MAX)).unwrap()
    }

    fn run_is_ok(initial_stack: Vec<i64>, ops: Vec<Op>) -> bool {
        super::run(&ops, VMOptions::new(&initial_stack, usize::MAX)).is_ok()
    }

    fn run_op(initial_stack: Vec<i64>, op: Op) -> Vec<i64> {
        run(initial_stack, vec![op])
    }

    fn run_op_is_ok(initial_stack: Vec<i64>, op: Op) -> bool {
        run_is_ok(initial_stack, vec![op])
    }

    #[test]
    fn test_empty() {
        assert_eq!(run(vec![], vec![]), vec![]);
    }

    #[test]
    fn test_praise() {
        // Not enough parameters
        assert!(!run_op_is_ok(vec![], Op::Praise));
        // Negative parameters are invalid.
        assert!(!run_op_is_ok(vec![-1], Op::Praise));

        let i_like_ksp: Vec<_> = "Mám rád KSP".chars().map(|x| x as i64).collect();
        for i in 0..10 {
            assert_eq!(run_op(vec![i], Op::Praise), i_like_ksp.repeat(i as usize));
        }

        fn run_praise_with_stack_size(
            initial_stack: Vec<i64>,
            stack_size: usize,
        ) -> Result<Vec<i64>, RunError> {
            super::run(&vec![Op::Praise], VMOptions::new(&initial_stack, stack_size))
        }

        // 1 -> 11 chars
        assert_eq!(run_praise_with_stack_size(vec![1], 11), Ok(i_like_ksp.repeat(1)));
        assert_eq!(run_praise_with_stack_size(vec![1], 10), Err(RunError::StackOverflow));

        // 9091 -> 100001 chars
        assert_eq!(run_praise_with_stack_size(vec![9091], 100001), Ok(i_like_ksp.repeat(9091)));
        assert_eq!(run_praise_with_stack_size(vec![9091], 100000), Err(RunError::StackOverflow));

        // This should fail in reasonable time.
        assert_eq!(run_praise_with_stack_size(vec![i64::MAX], 10), Err(RunError::StackOverflow));
    }

    #[test]
    fn test_pop() {
        assert!(!run_op_is_ok(vec![], Op::Pop));

        assert_eq!(run_op(vec![1, 2, 3], Op::Pop), vec![1, 2]);
    }

    #[test]
    fn test_pop2() {
        assert!(!run_op_is_ok(vec![], Op::Pop2));
        assert!(!run_op_is_ok(vec![1], Op::Pop2));

        assert_eq!(run_op(vec![1, 2], Op::Pop2), vec![2]);
        assert_eq!(run_op(vec![1, 2, 3, 4], Op::Pop2), vec![1, 2, 4]);
    }

    #[test]
    fn test_max() {
        assert!(!run_op_is_ok(vec![], Op::Max));
        assert!(!run_op_is_ok(vec![1], Op::Max));

        assert_eq!(run_op(vec![0, 0], Op::Max), [0]);
        assert_eq!(run_op(vec![1, 2], Op::Max), [2]);
        assert_eq!(run_op(vec![2, 1], Op::Max), [2]);
        assert_eq!(run_op(vec![1, 2, 3], Op::Max), [1, 3]);
        assert_eq!(run_op(vec![1, 3, 2], Op::Max), [1, 3]);
        assert_eq!(run_op(vec![i64::MIN, i64::MAX], Op::Max), [i64::MAX]);
    }

    #[test]
    fn test_lswap() {
        assert!(!run_op_is_ok(vec![], Op::LSwap));

        assert_eq!(run_op(vec![1], Op::LSwap), [1]);
        assert_eq!(run_op(vec![1, 2, 3, 4], Op::LSwap), [4, 2, 3, 1]);
    }

    #[test]
    fn test_lroll() {
        // Not enough parameters
        assert!(!run_op_is_ok(vec![], Op::LRoll));
        assert!(!run_op_is_ok(vec![0], Op::LRoll));
        // Not enough elements
        assert!(!run_op_is_ok(vec![1, 1], Op::LRoll));
        assert!(!run_op_is_ok(vec![1, 2, 3, 1, 4], Op::LRoll));

        assert_eq!(run_op(vec![0, 0], Op::LRoll), []);
        assert_eq!(run_op(vec![1, 0], Op::LRoll), []);
        assert_eq!(run_op(vec![1, 2, 3, 4, 1, 4], Op::LRoll), [4, 1, 2, 3]);
        assert_eq!(run_op(vec![1, 2, 3, 4, -1, 4], Op::LRoll), [2, 3, 4, 1]);
        assert_eq!(run_op(vec![0, 1, 2, 3, 4, 2, 4], Op::LRoll), [0, 3, 4, 1, 2]);

        assert_eq!(run_op(vec![1, 2, 3, 4, i64::MAX, 4], Op::LRoll), [2, 3, 4, 1]);
        assert_eq!(run_op(vec![1, 2, 3, 4, i64::MIN, 4], Op::LRoll), [1, 2, 3, 4]);
    }

    #[test]
    fn test_ff() {
        fn run_ff(initial_stack: Vec<i64>, stack_size: usize) -> Vec<i64> {
            super::run(&vec![Op::FF], VMOptions::new(&initial_stack, stack_size)).unwrap()
        }

        assert!(!run_op_is_ok(vec![], Op::FF));
        assert!(!run_op_is_ok(vec![1], Op::FF));

        assert_eq!(run_ff(vec![1, 2, 3, 4, 5], 1000), [1, 2, 3, 4, 5]);
        assert_eq!(run_ff(vec![4, 2], 8), vec![i64::MIN; 8]);
        assert_eq!(run_ff(vec![1, 2, 3, 4, 2], 8), vec![i64::MIN; 8]);
    }

    #[test]
    fn test_swap() {
        assert!(!run_op_is_ok(vec![], Op::Swap));
        // Negative index is invalid.
        assert!(!run_op_is_ok(vec![1, 2, 3, 4, -1], Op::Swap));
        // Index out of bounds is invalid.
        assert!(!run_op_is_ok(vec![1, 2, 3, 4, 4], Op::Swap));

        assert_eq!(run_op(vec![1, 2, 3, 4, 0], Op::Swap), [4, 2, 3, 1]);
        assert_eq!(run_op(vec![1, 2, 3, 4, 1], Op::Swap), [1, 4, 3, 2]);
        assert_eq!(run_op(vec![1, 2, 3, 4, 2], Op::Swap), [1, 2, 4, 3]);
        assert_eq!(run_op(vec![1, 2, 3, 4, 3], Op::Swap), [1, 2, 3, 4]);

        assert_eq!(run_op(vec![1, 2, 3, 4, 5, 6, 7, 8, 3], Op::Swap), [1, 2, 3, 8, 5, 6, 7, 4]);
    }

    #[test]
    fn test_kpi() {
        todo!()
    }

    #[test]
    fn test_increment() {
        todo!()
    }

    #[test]
    fn test_universal() {
        todo!()
    }

    #[test]
    fn test_remainder() {
        todo!()
    }

    #[test]
    fn test_tetration() {
        todo!()
    }

    #[test]
    fn test_median() {
        todo!()
    }

    #[test]
    fn test_digitsum() {
        assert_eq!(run_op(vec![0], Op::DigitSum), [0, 0]);
        assert_eq!(run_op(vec![1], Op::DigitSum), [1, 1]);
        assert_eq!(run_op(vec![-1], Op::DigitSum), [-1, 1]);
        assert_eq!(run_op(vec![10], Op::DigitSum), [10, 1]);
        assert_eq!(run_op(vec![-10], Op::DigitSum), [-10, 1]);
        assert_eq!(run_op(vec![333], Op::DigitSum), [333, 9]);
        assert_eq!(run_op(vec![-333], Op::DigitSum), [-333, 9]);
        assert_eq!(run_op(vec![i64::MIN], Op::DigitSum), [i64::MIN, 89]);
        assert_eq!(run_op(vec![i64::MAX], Op::DigitSum), [i64::MAX, 88]);
    }

    #[test]
    fn test_lensum() {
        todo!()
    }

    #[test]
    fn test_bitshift() {
        todo!()
    }

    #[test]
    fn test_sum() {
        todo!()
    }

    #[test]
    fn test_gcd2() {
        todo!()
    }

    #[test]
    fn test_gcdn() {
        todo!()
    }

    #[test]
    fn test_qeq() {
        todo!()
    }

    #[test]
    fn test_funkcia() {
        todo!()
    }

    #[test]
    fn test_bulkpairwiseofsomethingbinary() {
        todo!()
    }

    #[test]
    fn test_branchifzero() {
        todo!()
    }

    #[test]
    fn test_call() {
        todo!()
    }

    #[test]
    fn test_goto() {
        todo!()
    }

    #[test]
    fn test_jump() {
        todo!()
    }

    #[test]
    fn test_rev() {
        todo!()
    }

    #[test]
    fn test_sleep() {
        todo!()
    }

    #[test]
    fn test_deez() {
        todo!()
    }
}

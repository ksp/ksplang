use crate::vm::RunError::InstructionFailed;
use super::*;

const PI_TEST_VALUES: [i8; 42] = [
    3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5,
    0, 2, 8, 8, 4, 1, 9, 7, 1, 6,
];

fn run(initial_stack: &[i64], ops: &[Op]) -> Vec<i64> {
    super::run(ops, VMOptions::new(initial_stack, usize::MAX, &PI_TEST_VALUES, u64::MAX)).unwrap().stack
}

fn run_is_ok(initial_stack: &[i64], ops: &[Op]) -> bool {
    super::run(ops, VMOptions::new(initial_stack, usize::MAX, &PI_TEST_VALUES, u64::MAX)).is_ok()
}

fn run_op(initial_stack: &[i64], op: Op) -> Vec<i64> {
    run(initial_stack, &[op])
}

fn run_op_is_ok(initial_stack: &[i64], op: Op) -> bool {
    run_is_ok(initial_stack, &[op])
}

#[test]
fn test_empty() {
    assert_eq!(run(&[], &[]), &[]);
}

#[test]
fn test_praise() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Praise));
    // Negative parameters are invalid.
    assert!(!run_op_is_ok(&[-1], Op::Praise));

    let i_like_ksp: Vec<_> = "Mám rád KSP".chars().map(|x| x as i64).collect();
    for i in 0..10 {
        assert_eq!(run_op(&[i], Op::Praise), i_like_ksp.repeat(i as usize));
    }

    fn run_praise_with_stack_size(
        initial_stack: &[i64],
        stack_size: usize,
    ) -> Result<Vec<i64>, RunError> {
        super::run(&[Op::Praise], VMOptions::new(&initial_stack, stack_size, &PI_TEST_VALUES, u64::MAX))
            .map(|x| x.stack)
    }

    // 1 -> 11 chars
    assert_eq!(run_praise_with_stack_size(&[1], 11), Ok(i_like_ksp.repeat(1)));
    assert!(matches!(run_praise_with_stack_size(&[1], 10), Err(InstructionFailed { error: OperationError::PushFailed, .. })));

    // 9091 -> 100001 chars
    assert_eq!(run_praise_with_stack_size(&[9091], 100001), Ok(i_like_ksp.repeat(9091)));
    assert!(matches!(run_praise_with_stack_size(&[9091], 100000), Err(InstructionFailed { error: OperationError::PushFailed, .. })));

    // This should fail in reasonable time.
    assert!(matches!(run_praise_with_stack_size(&[i64::MAX], 10), Err(InstructionFailed { error: OperationError::PushFailed, .. })));
}

#[test]
fn test_nop() {
    assert_eq!(run_op(&[], Op::Nop), &[]);
    assert_eq!(run_op(&[1, 2, 3], Op::Nop), &[1, 2, 3]);
}

#[test]
fn test_pop() {
    assert!(!run_op_is_ok(&[], Op::Pop));

    assert_eq!(run_op(&[1, 2, 3], Op::Pop), &[1, 2]);
}

#[test]
fn test_pop2() {
    assert!(!run_op_is_ok(&[], Op::Pop2));
    assert!(!run_op_is_ok(&[1], Op::Pop2));

    assert_eq!(run_op(&[1, 2], Op::Pop2), &[2]);
    assert_eq!(run_op(&[1, 2, 3, 4], Op::Pop2), &[1, 2, 4]);
}

#[test]
fn test_lswap() {
    assert_eq!(run_op(&[], Op::LSwap), []);
    assert_eq!(run_op(&[1], Op::LSwap), [1]);
    assert_eq!(run_op(&[1, 2, 3, 4], Op::LSwap), [4, 2, 3, 1]);
}

#[test]
fn test_lroll() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Roll));
    assert!(!run_op_is_ok(&[0], Op::Roll));
    // Not enough elements
    assert!(!run_op_is_ok(&[1, 1], Op::Roll));
    assert!(!run_op_is_ok(&[1, 2, 3, 1, 4], Op::Roll));

    assert_eq!(run_op(&[0, 0], Op::Roll), []);
    assert_eq!(run_op(&[1, 0], Op::Roll), []);
    assert_eq!(run_op(&[1, 2, 3, 4, 1, 4], Op::Roll), [4, 1, 2, 3]);
    assert_eq!(run_op(&[1, 2, 3, 4, -1, 4], Op::Roll), [2, 3, 4, 1]);
    assert_eq!(run_op(&[0, 1, 2, 3, 4, 2, 4], Op::Roll), [0, 3, 4, 1, 2]);

    assert_eq!(run_op(&[1, 2, 3, 4, i64::MAX, 4], Op::Roll), [2, 3, 4, 1]);
    assert_eq!(run_op(&[1, 2, 3, 4, i64::MIN, 4], Op::Roll), [1, 2, 3, 4]);
}

#[test]
fn test_ff() {
    fn run_ff(initial_stack: &[i64], stack_size: usize) -> Vec<i64> {
        super::run(&[Op::FF], VMOptions::new(&initial_stack, stack_size, &PI_TEST_VALUES, u64::MAX)).unwrap().stack
    }

    assert!(!run_op_is_ok(&[], Op::FF));
    assert!(!run_op_is_ok(&[1], Op::FF));

    assert_eq!(run_ff(&[1, 2], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[0; 8], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[i64::MIN; 8], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[i64::MAX; 8], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[1, 2, 3, 4, 5], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[4, 2], 8), &[4, 2]);
    assert_eq!(run_ff(&[1, 2, 3, 4, 2], 8), [1, 2, 3, 4, 2]);
}

#[test]
fn test_swap() {
    assert!(!run_op_is_ok(&[], Op::Swap));
    // Negative index is invalid.
    assert!(!run_op_is_ok(&[1, 2, 3, 4, -1], Op::Swap));
    // Index out of bounds is invalid.
    assert!(!run_op_is_ok(&[1, 2, 3, 4, 4], Op::Swap));

    assert_eq!(run_op(&[1, 2, 3, 4, 0], Op::Swap), [4, 2, 3, 1]);
    assert_eq!(run_op(&[1, 2, 3, 4, 1], Op::Swap), [1, 4, 3, 2]);
    assert_eq!(run_op(&[1, 2, 3, 4, 2], Op::Swap), [1, 2, 4, 3]);
    assert_eq!(run_op(&[1, 2, 3, 4, 3], Op::Swap), [1, 2, 3, 4]);

    assert_eq!(run_op(&[1, 2, 3, 4, 5, 6, 7, 8, 3], Op::Swap), [1, 2, 3, 8, 5, 6, 7, 4]);
}

#[test]
fn test_kpi() {
    assert_eq!(run_op(&[], Op::KPi), []);
    assert_eq!(run_op(&[0], Op::KPi), [3]);
    assert_eq!(run_op(&[1, 2, 3, 4, 5], Op::KPi), [3, 1, 4, 1, 5]);
    assert_eq!(run_op(&[2, 2, 2, 2, 2], Op::KPi), [2, 2, 4, 2, 2]);
    assert_eq!(run_op(&[0, 1, 2, 3, 4], Op::KPi), [0, 1, 2, 3, 5]);
}

#[test]
fn test_increment() {
    assert!(!run_op_is_ok(&[], Op::Increment));
    assert!(!run_op_is_ok(&[i64::MAX], Op::Increment));

    for i in -10..10 {
        assert_eq!(run_op(&[i], Op::Increment), [i + 1]);
        assert_eq!(run_op(&[1, 2, 3, 4, i], Op::Increment), [1, 2, 3, 4, i + 1]);
    }
}

#[test]
fn test_max() {
    assert!(!run_op_is_ok(&[], Op::Max));
    assert!(!run_op_is_ok(&[1], Op::Max));

    assert_eq!(run_op(&[0, 0], Op::Max), [0]);
    assert_eq!(run_op(&[1, 2], Op::Max), [2]);
    assert_eq!(run_op(&[2, 1], Op::Max), [2]);
    assert_eq!(run_op(&[1, 2, 3], Op::Max), [1, 3]);
    assert_eq!(run_op(&[1, 3, 2], Op::Max), [1, 3]);
    assert_eq!(run_op(&[i64::MIN, i64::MAX], Op::Max), [i64::MAX]);
}

#[test]
fn test_universal() {
    assert!(!run_op_is_ok(&[], Op::Universal));

    // 0 = Addition, [a, b] -> a + b
    assert!(!run_op_is_ok(&[0], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[1, 0], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[i64::MAX, 1, 0], Op::Universal)); // Overflow
    assert!(!run_op_is_ok(&[i64::MIN, -1, 0], Op::Universal)); // Overflow
    assert_eq!(run_op(&[1, 2, 3, 8, 4, 0], Op::Universal), [1, 2, 3, 12]);
    assert_eq!(run_op(&[8, 4, 0], Op::Universal), [12]);
    assert_eq!(run_op(&[8, -9, 0], Op::Universal), [-1]);

    // 1 = Subtraction (absolute value of result), [a, b] -> |b - a|
    assert!(!run_op_is_ok(&[1], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[1, 1], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[i64::MIN, 0, 1], Op::Universal)); // Overflow
    assert_eq!(run_op(&[1, 2, 3, 8, 4, 1], Op::Universal), [1, 2, 3, 4]);
    assert_eq!(run_op(&[8, 4, 1], Op::Universal), [4]);
    assert_eq!(run_op(&[4, 8, 1], Op::Universal), [4]);
    assert_eq!(run_op(&[-4, -8, 1], Op::Universal), [4]);
    assert_eq!(run_op(&[0, 0, 1], Op::Universal), [0]);
    assert_eq!(run_op(&[i64::MAX, i64::MAX, 1], Op::Universal), [0]);
    assert_eq!(run_op(&[i64::MAX, 0, 1], Op::Universal), [i64::MAX]);

    // 2 = Multiplication [a, b] -> a * b
    assert!(!run_op_is_ok(&[2], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[1, 2], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[i64::MIN, -1, 2], Op::Universal)); // Overflow
    assert!(!run_op_is_ok(&[i64::MAX, 2, 2], Op::Universal)); // Overflow
    assert_eq!(run_op(&[1, 2, 3, 8, 4, 2], Op::Universal), [1, 2, 3, 8 * 4]);
    assert_eq!(run_op(&[8, 4, 2], Op::Universal), [8 * 4]);
    assert_eq!(run_op(&[8, -4, 2], Op::Universal), [8 * -4]);
    assert_eq!(run_op(&[-8, 4, 2], Op::Universal), [-8 * 4]);
    assert_eq!(run_op(&[-8, -4, 2], Op::Universal), [-8 * -4]);
    assert_eq!(run_op(&[0, 8, 2], Op::Universal), [0]);
    assert_eq!(run_op(&[8, 0, 2], Op::Universal), [0]);
    assert_eq!(run_op(&[i64::MAX, 0, 2], Op::Universal), [0]);
    assert_eq!(run_op(&[i64::MAX, -1, 2], Op::Universal), [-i64::MAX]);
    assert_eq!(run_op(&[i64::MIN, 0, 2], Op::Universal), [0]);

    // 3 = Division/remainder ([a, b] -> b / a or b % a if not divisible)
    assert!(!run_op_is_ok(&[3], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[1, 3], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[0, 1, 3], Op::Universal)); // Division by zero
    assert!(!run_op_is_ok(&[-1, i64::MIN, 3], Op::Universal)); // Overflow
    assert_eq!(run_op(&[1, 2, 3, 4, 8, 3], Op::Universal), [1, 2, 3, 8 / 4]);
    assert_eq!(run_op(&[4, 8, 3], Op::Universal), [8 / 4]);
    assert_eq!(run_op(&[8, 4, 3], Op::Universal), [4 % 8]);
    assert_eq!(run_op(&[3, 8, 3], Op::Universal), [8 % 3]);
    assert_eq!(run_op(&[3, -8, 3], Op::Universal), [-8 % 3]);
    assert_eq!(run_op(&[-3, 8, 3], Op::Universal), [8 % -3]);

    // 4 = Factorial of absolute value [a] -> a!
    assert!(!run_op_is_ok(&[4], Op::Universal)); // Not enough parameters
    assert!(!run_op_is_ok(&[21, 4], Op::Universal)); // Result too big for i64
    assert!(!run_op_is_ok(&[i64::MAX, 4], Op::Universal)); // Result too big for i64
    assert!(!run_op_is_ok(&[i64::MIN, 4], Op::Universal)); // Result too big for i64
    assert_eq!(run_op(&[1, 2, 3, 6, 4], Op::Universal), [1, 2, 3, 720]);
    assert_eq!(run_op(&[0, 4], Op::Universal), [1]);
    assert_eq!(run_op(&[1, 4], Op::Universal), [1]);
    assert_eq!(run_op(&[-1, 4], Op::Universal), [1]);
    assert_eq!(run_op(&[6, 4], Op::Universal), [720]);
    assert_eq!(run_op(&[-6, 4], Op::Universal), [720]);
    assert_eq!(run_op(&[20, 4], Op::Universal), [2432902008176640000]);
    assert_eq!(run_op(&[-20, 4], Op::Universal), [2432902008176640000]);

    // 5 = sign
    assert!(!run_op_is_ok(&[5], Op::Universal)); // Not enough parameters
    assert_eq!(run_op(&[1, 2, 3, 1, 5], Op::Universal), [1, 2, 3, 1]);
    assert_eq!(run_op(&[0, 5], Op::Universal), [0]);
    assert_eq!(run_op(&[1, 5], Op::Universal), [1]);
    assert_eq!(run_op(&[-1, 5], Op::Universal), [-1]);
    assert_eq!(run_op(&[-1234, 5], Op::Universal), [-1]);
    assert_eq!(run_op(&[1234, 5], Op::Universal), [1]);
    assert_eq!(run_op(&[i64::MAX, 5], Op::Universal), [1]);
    assert_eq!(run_op(&[i64::MIN, 5], Op::Universal), [-1]);

    // Invalid arguments
    assert!(!run_op_is_ok(&[1, 2, 3, 4, 6], Op::Universal));
    assert!(!run_op_is_ok(&[1, 2, 3, 4, 7], Op::Universal));
    assert!(!run_op_is_ok(&[1, 2, 3, 4, -1], Op::Universal));
    assert!(!run_op_is_ok(&[1, 2, 3, 4, i64::MIN], Op::Universal));
    assert!(!run_op_is_ok(&[1, 2, 3, 4, i64::MAX], Op::Universal));
}

#[test]
fn test_remainder() {
    assert!(!run_op_is_ok(&[], Op::Remainder));
    assert!(!run_op_is_ok(&[1], Op::Remainder));
    assert!(!run_op_is_ok(&[0, 1], Op::Remainder)); // Division by zero
    assert!(!run_op_is_ok(&[-1, i64::MIN], Op::Remainder)); // Integer overflow

    assert_eq!(run_op(&[1, 2, 3, 3, 1], Op::Remainder), [1, 2, 3, 1]);

    assert_eq!(run_op(&[1, i64::MIN], Op::Remainder), [0]);
    assert_eq!(run_op(&[3, 1], Op::Remainder), [1]);
    assert_eq!(run_op(&[-3, 1], Op::Remainder), [1]);
    assert_eq!(run_op(&[3, -1], Op::Remainder), [-1]);
    assert_eq!(run_op(&[-3, -1], Op::Remainder), [-1]);
}

#[test]
fn test_modulo() {
    assert!(!run_op_is_ok(&[], Op::Modulo));
    assert!(!run_op_is_ok(&[1], Op::Modulo));
    assert!(!run_op_is_ok(&[0, 1], Op::Modulo)); // Division by zero
    assert!(!run_op_is_ok(&[-1, i64::MIN], Op::Modulo)); // Integer overflow

    assert_eq!(run_op(&[1, 2, 3, 3, 1], Op::Modulo), [1, 2, 3, 1]);

    assert_eq!(run_op(&[1, i64::MIN], Op::Modulo), [0]);
    assert_eq!(run_op(&[3, 1], Op::Modulo), [1]);
    assert_eq!(run_op(&[-3, 1], Op::Modulo), [1]);
    assert_eq!(run_op(&[3, -1], Op::Modulo), [2]);
    assert_eq!(run_op(&[-3, -1], Op::Modulo), [2]);
}

#[test]
fn test_tetration_num_iters() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::TetrationNumIters));
    assert!(!run_op_is_ok(&[1], Op::TetrationNumIters));

    // Negative iterations
    assert!(!run_op_is_ok(&[-1, 1], Op::TetrationNumIters));
    assert!(!run_op_is_ok(&[i64::MIN, 1], Op::TetrationNumIters));

    // Overflow
    assert!(!run_op_is_ok(&[4, 3], Op::TetrationNumIters));
    assert!(!run_op_is_ok(&[i64::MAX, i64::MAX], Op::TetrationNumIters));

    assert_eq!(run_op(&[1, 2, 3, 0, 1], Op::TetrationNumIters), [1, 2, 3, 1]);

    assert_eq!(run_op(&[0, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[0, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[1, 0], Op::TetrationNumIters), [0]);
    assert_eq!(run_op(&[2, 0], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[1000, 0], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[1, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[2, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[3, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[1000, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[2, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[2, 2], Op::TetrationNumIters), [4]);
    assert_eq!(run_op(&[2, 3], Op::TetrationNumIters), [27]);
    assert_eq!(run_op(&[2, 4], Op::TetrationNumIters), [256]);
    assert_eq!(run_op(&[2, 5], Op::TetrationNumIters), [3125]);
    assert_eq!(run_op(&[2, 6], Op::TetrationNumIters), [46656]);
    assert_eq!(run_op(&[3, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[3, 2], Op::TetrationNumIters), [16]);
    assert_eq!(run_op(&[3, 3], Op::TetrationNumIters), [7625597484987]);
    assert_eq!(run_op(&[4, 1], Op::TetrationNumIters), [1]);
    assert_eq!(run_op(&[4, 2], Op::TetrationNumIters), [65536]);
}

#[test]
fn test_tetration_iters_num() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::TetrationItersNum));
    assert!(!run_op_is_ok(&[1], Op::TetrationItersNum));

    // Negative iterations
    assert!(!run_op_is_ok(&[1, -1], Op::TetrationItersNum));
    assert!(!run_op_is_ok(&[1, i64::MIN], Op::TetrationItersNum));

    // Overflow
    assert!(!run_op_is_ok(&[3, 4], Op::TetrationItersNum));
    assert!(!run_op_is_ok(&[i64::MAX, i64::MAX], Op::TetrationItersNum));

    assert_eq!(run_op(&[1, 2, 3, 1, 0], Op::TetrationItersNum), [1, 2, 3, 1]);

    assert_eq!(run_op(&[1, 0], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 0], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[0, 1], Op::TetrationItersNum), [0]);
    assert_eq!(run_op(&[0, 2], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[0, 1000], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 1], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 2], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 3], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 1000], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[1, 2], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[2, 2], Op::TetrationItersNum), [4]);
    assert_eq!(run_op(&[3, 2], Op::TetrationItersNum), [27]);
    assert_eq!(run_op(&[4, 2], Op::TetrationItersNum), [256]);
    assert_eq!(run_op(&[5, 2], Op::TetrationItersNum), [3125]);
    assert_eq!(run_op(&[6, 2], Op::TetrationItersNum), [46656]);
    assert_eq!(run_op(&[1, 3], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[2, 3], Op::TetrationItersNum), [16]);
    assert_eq!(run_op(&[3, 3], Op::TetrationItersNum), [7625597484987]);
    assert_eq!(run_op(&[1, 4], Op::TetrationItersNum), [1]);
    assert_eq!(run_op(&[2, 4], Op::TetrationItersNum), [65536]);
}

#[test]
fn test_median() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Median));
    // Division by zero
    assert!(!run_op_is_ok(&[0], Op::Median));
    // Not enough elements
    assert!(!run_op_is_ok(&[1, 2, 3, 5], Op::Median));

    assert_eq!(run_op(&[1, 2, 3, 2, 2], Op::Median), [1, 2, 3, 2, 2, 2]);

    assert_eq!(run_op(&[1], Op::Median), [1, 1]);
    assert_eq!(run_op(&[3, 1], Op::Median), [3, 1, 1]);
    assert_eq!(run_op(&[2, 2], Op::Median), [2, 2, 2]);
    assert_eq!(run_op(&[3, 2], Op::Median), [3, 2, 2]);
    assert_eq!(run_op(&[4, 2], Op::Median), [4, 2, 3]);
    assert_eq!(run_op(&[1, 2, 3, 4, 5], Op::Median), [1, 2, 3, 4, 5, 3]);
    assert_eq!(run_op(&[4, 3, 2, 1, 5], Op::Median), [4, 3, 2, 1, 5, 3]);
    assert_eq!(run_op(&[i64::MAX - 4, i64::MAX - 5, i64::MAX, 4], Op::Median), [i64::MAX - 4, i64::MAX - 5, i64::MAX, 4, i64::MAX - 5]);
}

#[test]
fn test_digitsum() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::DigitSum));

    assert_eq!(run_op(&[0], Op::DigitSum), [0, 0]);
    assert_eq!(run_op(&[1], Op::DigitSum), [1, 1]);
    assert_eq!(run_op(&[-1], Op::DigitSum), [-1, 1]);
    assert_eq!(run_op(&[10], Op::DigitSum), [10, 1]);
    assert_eq!(run_op(&[-10], Op::DigitSum), [-10, 1]);
    assert_eq!(run_op(&[333], Op::DigitSum), [333, 9]);
    assert_eq!(run_op(&[-333], Op::DigitSum), [-333, 9]);
    assert_eq!(run_op(&[i64::MIN], Op::DigitSum), [i64::MIN, 89]);
    assert_eq!(run_op(&[i64::MAX], Op::DigitSum), [i64::MAX, 88]);
}

#[test]
fn test_lensum() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::LenSum));
    assert!(!run_op_is_ok(&[1], Op::LenSum));

    assert_eq!(run_op(&[1, 2, 3, 0, 0], Op::LenSum), [1, 2, 3, 0]);

    assert_eq!(run_op(&[0, 0], Op::LenSum), [0]);
    assert_eq!(run_op(&[0, 1], Op::LenSum), [1]);
    assert_eq!(run_op(&[9, 9], Op::LenSum), [2]);
    assert_eq!(run_op(&[10, 9], Op::LenSum), [3]);
    assert_eq!(run_op(&[10, 10], Op::LenSum), [4]);
    assert_eq!(run_op(&[i64::MAX, i64::MAX], Op::LenSum), [19 + 19]);
    assert_eq!(run_op(&[-1, -1], Op::LenSum), [2]);
    assert_eq!(run_op(&[i64::MIN, i64::MIN], Op::LenSum), [19 + 19]);
}

#[test]
fn test_bitshift() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Bitshift));
    assert!(!run_op_is_ok(&[1], Op::Bitshift));

    // Negative numbers are not allowed
    assert!(!run_op_is_ok(&[1, -1], Op::Bitshift));
    assert!(!run_op_is_ok(&[64, -1], Op::Bitshift));
    assert!(!run_op_is_ok(&[64, i64::MIN], Op::Bitshift));

    assert_eq!(run_op(&[1, 2, 3, 1, 1], Op::Bitshift), [1, 2, 3, 2]);

    assert_eq!(run_op(&[0, 0], Op::Bitshift), [0]);
    assert_eq!(run_op(&[1, 0], Op::Bitshift), [1]);
    assert_eq!(run_op(&[2, 0], Op::Bitshift), [2]);

    assert_eq!(run_op(&[0, 1], Op::Bitshift), [0]);
    assert_eq!(run_op(&[1, 1], Op::Bitshift), [2]);
    assert_eq!(run_op(&[2, 1], Op::Bitshift), [4]);
    assert_eq!(run_op(&[3, 1], Op::Bitshift), [6]);
    assert_eq!(run_op(&[i64::MAX, 1], Op::Bitshift), [-2]);
    assert_eq!(run_op(&[i64::MIN, 1], Op::Bitshift), [0]);
    assert_eq!(run_op(&[-1, 1], Op::Bitshift), [-2]);
    assert_eq!(run_op(&[0, 2], Op::Bitshift), [0]);
    assert_eq!(run_op(&[1, 2], Op::Bitshift), [4]);
    assert_eq!(run_op(&[i64::MIN, 2], Op::Bitshift), [0]);


    assert_eq!(run_op(&[0, 64], Op::Bitshift), [0]);
    assert_eq!(run_op(&[-1, 64], Op::Bitshift), [0]);
    assert_eq!(run_op(&[1, 64], Op::Bitshift), [0]);
    assert_eq!(run_op(&[i64::MIN, 64], Op::Bitshift), [0]);
    assert_eq!(run_op(&[i64::MAX, 64], Op::Bitshift), [0]);
    assert_eq!(run_op(&[1, i64::MAX], Op::Bitshift), [0]);
}

#[test]
fn test_and() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::And));
    assert!(!run_op_is_ok(&[1], Op::And));

    assert_eq!(run_op(&[1, 2, 3, 5, 3], Op::And), [1, 2, 3, 1]);

    assert_eq!(run_op(&[0, 0], Op::And), [0]);
    assert_eq!(run_op(&[0, 1], Op::And), [0]);
    assert_eq!(run_op(&[1, 1], Op::And), [1]);
    assert_eq!(run_op(&[5, 3], Op::And), [1]);
    assert_eq!(run_op(&[i64::MAX, i64::MAX], Op::And), [i64::MAX]);
    assert_eq!(run_op(&[i64::MIN, i64::MIN], Op::And), [i64::MIN]);
}

#[test]
fn test_sum() {
    assert_eq!(run_op(&[], Op::Sum), [0]);
    assert_eq!(run_op(&[0], Op::Sum), [0]);
    assert_eq!(run_op(&[1], Op::Sum), [1]);
    assert_eq!(run_op(&[1, -2], Op::Sum), [-1]);
    assert_eq!(run_op(&[1, i64::MIN], Op::Sum), [i64::MIN + 1]);
    // Intermediate results here would overflow an i64. We still support that.
    assert_eq!(run_op(&[i64::MAX, i64::MAX, i64::MIN, i64::MIN], Op::Sum), [-2]);

    // Integer overflow
    assert!(!run_op_is_ok(&[i64::MAX, 1], Op::Sum));
    assert!(!run_op_is_ok(&[i64::MIN, -1], Op::Sum));
}

#[test]
fn test_gcd2() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Gcd2));
    assert!(!run_op_is_ok(&[1], Op::Gcd2));

    // Integer overflow
    assert!(!run_op_is_ok(&[0, i64::MIN], Op::Gcd2));
    assert!(!run_op_is_ok(&[i64::MIN, i64::MIN], Op::Gcd2));

    assert_eq!(run_op(&[1, 2, 3, 3, 7], Op::Gcd2), [1, 2, 3, 1]);

    assert_eq!(run_op(&[3, 7], Op::Gcd2), [1]);
    assert_eq!(run_op(&[3, 21], Op::Gcd2), [3]);
    assert_eq!(run_op(&[18, 21], Op::Gcd2), [3]);
    assert_eq!(run_op(&[-18, 21], Op::Gcd2), [3]);
    assert_eq!(run_op(&[18, -21], Op::Gcd2), [3]);
    assert_eq!(run_op(&[-18, -21], Op::Gcd2), [3]);
    assert_eq!(run_op(&[0, 0], Op::Gcd2), [0]);
    assert_eq!(run_op(&[0, i64::MAX], Op::Gcd2), [i64::MAX]);
    assert_eq!(run_op(&[i64::MIN, 6], Op::Gcd2), [2]);
}

#[test]
fn test_gcdn() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::GcdN));
    // Zero elements is not valid
    assert!(!run_op_is_ok(&[0], Op::GcdN));
    // Not enough elements
    assert!(!run_op_is_ok(&[1], Op::GcdN));

    // Integer overflow
    assert!(!run_op_is_ok(&[0, i64::MIN, 2], Op::GcdN));
    assert!(!run_op_is_ok(&[0, 0, i64::MIN, 3], Op::GcdN));
    assert!(!run_op_is_ok(&[0, i64::MIN, 0, 3], Op::GcdN));
    assert!(!run_op_is_ok(&[i64::MIN, 1], Op::GcdN));

    assert_eq!(run_op(&[1, 2, 3, 1, 1, 2], Op::GcdN), [1, 2, 3, 1]);

    assert_eq!(run_op(&[0, 1], Op::GcdN), [0]);
    assert_eq!(run_op(&[5, 1], Op::GcdN), [5]);
    assert_eq!(run_op(&[-5, 1], Op::GcdN), [5]);
    assert_eq!(run_op(&[i64::MAX, 1], Op::GcdN), [i64::MAX]);
    assert_eq!(run_op(&[3, 7, 2], Op::GcdN), [1]);
    assert_eq!(run_op(&[3, 7, 1, 3], Op::GcdN), [1]);
    assert_eq!(run_op(&[21, 21, 21, 3], Op::GcdN), [21]);
    assert_eq!(run_op(&[21, 7, 14, 3], Op::GcdN), [7]);
    assert_eq!(run_op(&[21, 54, 6, 3], Op::GcdN), [3]);
    assert_eq!(run_op(&[i64::MIN, 6, i64::MIN, i64::MIN, 4], Op::GcdN), [2]);
}

#[test]
fn test_qeq() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Qeq));
    assert!(!run_op_is_ok(&[1], Op::Qeq));
    assert!(!run_op_is_ok(&[1, 2], Op::Qeq));

    // Integer overflow (results are -1, 2^63)
    assert!(!run_op_is_ok(&[i64::MIN, i64::MIN+1, 1], Op::Qeq));
    // Integer overflow (linear equation; result is 2^63)
    assert!(!run_op_is_ok(&[i64::MIN, 1, 0], Op::Qeq));
    // Too many results (all integers are a valid solution of 0 = 0)
    assert!(!run_op_is_ok(&[0, 0, 0], Op::Qeq));

    // (x+5)(x-8) = x^2 - 3x - 40
    assert_eq!(run_op(&[-40, -3, 1], Op::Qeq), [-5, 8]);
    // (x-3)(x-3) = x^2 - 6x + 9
    assert_eq!(run_op(&[9, -6, 1], Op::Qeq), [3]);
    // 2 non-integer solutions
    assert_eq!(run_op(&[-7, 3, 1], Op::Qeq), []);

    assert_eq!(run_op(&[0, i64::MIN + 1, 1], Op::Qeq), [0, i64::MAX]);
    assert_eq!(run_op(&[0, i64::MAX, 1], Op::Qeq), [i64::MIN + 1, 0]);

    // Linear equations:
    // 2x+4 = 0 -> x = -2
    assert_eq!(run_op(&[4, 2, 0], Op::Qeq), [-2]);
    // 2x+3 = 0 -> x is not integer
    assert_eq!(run_op(&[3, 2, 0], Op::Qeq), []);
    // constant = 0 -> x is not integer
    assert_eq!(run_op(&[4, 0, 0], Op::Qeq), []);
    // MIN x + MIN = 0 -> x = -1
    assert_eq!(run_op(&[i64::MIN, i64::MIN, 0], Op::Qeq), [-1]);

    // Internal overflow:
    // highest possible discriminant
    assert_eq!(run_op(&[i64::MAX, i64::MIN, i64::MIN], Op::Qeq), []);
    // lowest possible discriminant
    assert_eq!(run_op(&[i64::MIN, 0, i64::MIN], Op::Qeq), []);
    // discriminant overflows i128 but equation has two small integer solutions
    let multiplier = i64::MIN / -2;
    assert_eq!(run_op(&[-2 * multiplier, -1 * multiplier, 1 * multiplier], Op::Qeq), [-1, 2]);
    // discriminant overflows, one integer solution
    assert_eq!(run_op(&[i64::MIN, -1, i64::MAX], Op::Qeq), [-1]);
}

#[test]
fn test_funkcia() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Funkcia));
    assert!(!run_op_is_ok(&[1], Op::Funkcia));

    assert_eq!(run_op(&[1, 2, 3, 100, 54], Op::Funkcia), [1, 2, 3, 675]);

    assert_eq!(run_op(&[100, 54], Op::Funkcia), [675]);
    assert_eq!(run_op(&[54, 100], Op::Funkcia), [675]);

    const MOD: i64 = 1_000_000_007;

    assert_eq!(run_op(&[-1, -1], Op::Funkcia), [0]);
    assert_eq!(run_op(&[1, 0], Op::Funkcia), [0]);
    assert_eq!(run_op(&[1, 1], Op::Funkcia), [0]);
    assert_eq!(run_op(&[1, 2], Op::Funkcia), [2]);
    assert_eq!(run_op(&[2, 2], Op::Funkcia), [0]);
    assert_eq!(run_op(&[i64::MAX, 0], Op::Funkcia), [i64::MAX % MOD]);
    assert_eq!(run_op(&[0, i64::MAX], Op::Funkcia), [i64::MAX % MOD]);
    assert_eq!(run_op(&[i64::MAX, 0], Op::Funkcia), [i64::MAX % MOD]);
    assert_eq!(run_op(&[0, MOD], Op::Funkcia), [0]);
    assert_eq!(run_op(&[0, MOD - 1], Op::Funkcia), [MOD - 1]);
}

#[test]
fn test_bulkxor() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::BulkXor));
    // Not enough values
    assert!(!run_op_is_ok(&[1, 1], Op::BulkXor));
    // Not enough values
    assert!(!run_op_is_ok(&[1, 2, 3, 2], Op::BulkXor));

    assert_eq!(run_op(&[1, 2, 3, 1, 1, 1], Op::BulkXor), [1, 2, 3, 0]);

    assert_eq!(run_op(&[1, 1, 1], Op::BulkXor), [0]);
    assert_eq!(run_op(&[0, 1, 1], Op::BulkXor), [1]);
    assert_eq!(run_op(&[1, 0, 1], Op::BulkXor), [1]);
    assert_eq!(run_op(&[0, 0, 1], Op::BulkXor), [0]);
    assert_eq!(run_op(&[-1, -1, 1], Op::BulkXor), [0]);
    assert_eq!(run_op(&[-1, 0, 1], Op::BulkXor), [0]);
    assert_eq!(run_op(&[i64::MIN, 0, 1], Op::BulkXor), [0]);
    assert_eq!(run_op(&[i64::MAX, 0, 1], Op::BulkXor), [1]);
    assert_eq!(run_op(&[i64::MAX, i64::MIN, 1], Op::BulkXor), [1]);
    assert_eq!(run_op(&[0, 0, 1, 0, 2], Op::BulkXor), [0, 1]);
    assert_eq!(run_op(&[1, 0, 1, 0, 2], Op::BulkXor), [1, 1]);
    assert_eq!(run_op(&[1, 0, 0, 0, 2], Op::BulkXor), [1, 0]);
    assert_eq!(run_op(&[0, 0, 0, 0, 2], Op::BulkXor), [0, 0]);
}

#[test]
fn test_branchifzero() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::BranchIfZero));
    assert!(!run_op_is_ok(&[0], Op::BranchIfZero));

    // Index too large
    assert!(!run_is_ok(&[5, 0], &[Op::BranchIfZero, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));
    // Negative index
    assert!(!run_is_ok(&[-1, 0], &[Op::BranchIfZero, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));

    assert_eq!(run(&[4, 0], &[Op::BranchIfZero, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), [4]);
    assert_eq!(run(&[3, 0], &[Op::BranchIfZero, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), []);
    assert_eq!(run(&[1, 2, 3, 4], &[Op::BranchIfZero, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), []);
}

#[test]
fn test_call() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Call));
    // Index too large
    assert!(!run_is_ok(&[5], &[Op::Call, Op::Nop, Op::Nop, Op::Nop, Op::Nop]));
    // Negative index
    assert!(!run_is_ok(&[-1], &[Op::Call, Op::Nop, Op::Nop, Op::Nop, Op::Nop]));
    assert_eq!(run(&[1, 2, 3, 4], &[Op::Call, Op::Nop, Op::Nop, Op::Nop, Op::Nop]), [1, 2, 3, 4, 1]);
    assert_eq!(run(&[1, 2, 3], &[Op::Nop, Op::Call, Op::Nop, Op::Nop, Op::Nop]), [1, 2, 3, 2]);
    assert_eq!(run(&[1, 2, 3], &[Op::Nop, Op::Nop, Op::Nop, Op::Nop, Op::Call, Op::Nop]), [1, 2, 3, 5, 5]);
}

#[test]
fn test_goto() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Goto));
    // Index too large
    assert!(!run_is_ok(&[5], &[Op::Goto, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));
    // Negative index
    assert!(!run_is_ok(&[-1], &[Op::Goto, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));
    assert_eq!(run(&[1, 2, 3, 4], &[Op::Goto, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), [1, 2, 3]);
    assert_eq!(run(&[1, 2, 3], &[Op::Goto, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), [1]);
}

#[test]
fn test_jump() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Jump));
    // Index too large
    assert!(!run_is_ok(&[5], &[Op::Jump, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));
    assert!(!run_is_ok(&[4], &[Op::Jump, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));
    // Negative index
    assert!(!run_is_ok(&[-2], &[Op::Jump, Op::Pop, Op::Pop, Op::Pop, Op::Pop]));

    // Pop, pop, jump back to start, two more pops, then jump to the last pop.
    assert_eq!(run(&[3, 0, -3, 0, 0], &[Op::Pop, Op::Pop, Op::Jump, Op::Pop, Op::Pop, Op::Pop, Op::Pop]), []);
}

#[test]
fn test_rev() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Rev));
    assert!(!run_op_is_ok(&[1], Op::Rev));
    assert!(!run_op_is_ok(&[0, 1], Op::Rev));

    // Negative parameters are not allowed, even if it makes sense.
    assert!(!run_is_ok(&[-1, 0], &[Op::Nop, Op::Nop, Op::Rev, Op::Nop, Op::Nop]));

    // Return index out of range
    assert!(!run_op_is_ok(&[0, 0], Op::Rev));

    // Jump index out of range
    assert!(!run_op_is_ok(&[1, 0], Op::Rev));

    // Essentially a nop
    assert_eq!(run(&[1, 2, 3, 4, 0, 0], &[Op::Rev, Op::Nop]), [1, 2, 3, 4]);

    // Essentially a nop with a quadratic equation (x = -2 and x = 0)
    assert_eq!(run(&[1, 2, 3, 4, 0, 2, 1], &[Op::Rev, Op::Nop]), [1, 2, 3, 4]);

    // rev 2 forward, stack is rotated to [4, 3, 2, 1], pop twice, return to nop
    assert_eq!(run(&[1, 2, 3, 4, 2, 0], &[Op::Rev, Op::Pop, Op::Pop, Op::Nop]), [3, 4]);

    // Leaves the program in reverse by jumping over the rev.
    assert_eq!(run(&[0, 1, 2, 3, 2, 0], &[Op::Nop, Op::Rev, Op::Goto, Op::Nop, Op::Nop]), [3, 2, 1, 0]);
    // Leaves the program in reverse; jumps onto another jump directly
    assert_eq!(run(&[0, 1, 2, 3, 1, 0], &[Op::Nop, Op::Rev, Op::Goto, Op::Nop]), [3, 2, 1, 0]);

    // Two revs nested
    // -1 gets popped
    assert_eq!(run(&[-1, 0, 2, -1, 10, 11, 12, -1, -1, 5, 0], &[Op::Rev, Op::Pop, Op::Pop, Op::Pop, Op::Rev, Op::Pop, Op::Nop]), [10, 11, 12]);
    // Rev returning directly onto the outer rev
    assert_eq!(run(&[-1, 0, 2, 10, 11, 12, -1, -1, 4, 0, -1], &[Op::Pop, Op::Rev, Op::Pop, Op::Pop, Op::Rev, Op::Pop, Op::Nop]), [10, 11, 12]);
}

#[test]
fn test_sleep() {
    assert!(!run_op_is_ok(&[], Op::Sleep));
    assert!(!run_op_is_ok(&[1, 2, 3], Op::Sleep));
}

#[test]
fn test_deez() {
    // Not enough parameters
    assert!(!run_op_is_ok(&[], Op::Deez));
    // 2 instructions
    // 20: sum (creates 0 on an empty stack)
    // 9: ++ 0 -> 1
    // resulting stack: [1]
    // that is translated back into pop and added to the end of the program
    assert_eq!(run_op(&[1, 2, 3, 9, 20, 2], Op::Deez), [1, 2]);
}

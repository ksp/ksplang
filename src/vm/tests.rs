use super::*;

const PI_TEST_VALUES: [i8; 42] = [
    3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5,
    0, 2, 8, 8, 4, 1, 9, 7, 1, 6,
];

fn run(initial_stack: &[i64], ops: &[Op]) -> Vec<i64> {
    super::run(ops, VMOptions::new(initial_stack, usize::MAX, &PI_TEST_VALUES)).unwrap()
}

fn run_is_ok(initial_stack: &[i64], ops: &[Op]) -> bool {
    super::run(ops, VMOptions::new(initial_stack, usize::MAX, &PI_TEST_VALUES)).is_ok()
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
        super::run(&[Op::Praise], VMOptions::new(&initial_stack, stack_size, &PI_TEST_VALUES))
    }

    // 1 -> 11 chars
    assert_eq!(run_praise_with_stack_size(&[1], 11), Ok(i_like_ksp.repeat(1)));
    assert_eq!(run_praise_with_stack_size(&[1], 10), Err(RunError::StackOverflow));

    // 9091 -> 100001 chars
    assert_eq!(run_praise_with_stack_size(&[9091], 100001), Ok(i_like_ksp.repeat(9091)));
    assert_eq!(run_praise_with_stack_size(&[9091], 100000), Err(RunError::StackOverflow));

    // This should fail in reasonable time.
    assert_eq!(run_praise_with_stack_size(&[i64::MAX], 10), Err(RunError::StackOverflow));
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
        super::run(&[Op::FF], VMOptions::new(&initial_stack, stack_size, &PI_TEST_VALUES)).unwrap()
    }

    assert!(!run_op_is_ok(&[], Op::FF));
    assert!(!run_op_is_ok(&[1], Op::FF));

    assert_eq!(run_ff(&[1, 2, 3, 4, 5], 1000), [1, 2, 3, 4, 5]);
    assert_eq!(run_ff(&[4, 2], 8), &[i64::MIN; 8]);
    assert_eq!(run_ff(&[1, 2, 3, 4, 2], 8), &[i64::MIN; 8]);
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

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
    assert_eq!(run_op(vec![], Op::LSwap), []);
    assert_eq!(run_op(vec![1], Op::LSwap), [1]);
    assert_eq!(run_op(vec![1, 2, 3, 4], Op::LSwap), [4, 2, 3, 1]);
}

#[test]
fn test_lroll() {
    // Not enough parameters
    assert!(!run_op_is_ok(vec![], Op::Roll));
    assert!(!run_op_is_ok(vec![0], Op::Roll));
    // Not enough elements
    assert!(!run_op_is_ok(vec![1, 1], Op::Roll));
    assert!(!run_op_is_ok(vec![1, 2, 3, 1, 4], Op::Roll));

    assert_eq!(run_op(vec![0, 0], Op::Roll), []);
    assert_eq!(run_op(vec![1, 0], Op::Roll), []);
    assert_eq!(run_op(vec![1, 2, 3, 4, 1, 4], Op::Roll), [4, 1, 2, 3]);
    assert_eq!(run_op(vec![1, 2, 3, 4, -1, 4], Op::Roll), [2, 3, 4, 1]);
    assert_eq!(run_op(vec![0, 1, 2, 3, 4, 2, 4], Op::Roll), [0, 3, 4, 1, 2]);

    assert_eq!(run_op(vec![1, 2, 3, 4, i64::MAX, 4], Op::Roll), [2, 3, 4, 1]);
    assert_eq!(run_op(vec![1, 2, 3, 4, i64::MIN, 4], Op::Roll), [1, 2, 3, 4]);
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

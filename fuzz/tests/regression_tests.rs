use ksplang::{compiler::test_utils::verify_repro, ops::Op::{self, *}};

fn run_fuzz_case(ops: Vec<Op>, input: Vec<i64>) {
    verify_repro(ops, input);
}

#[test]
fn regression_branch_if_zero_empty_stack() {
    let ops = vec![ BranchIfZero ];
    let input = vec![0];
    run_fuzz_case(ops, input);
}

#[test]
fn fuzz_artifact_large_stack() {
    let ops = vec![ Praise ];
    verify_repro(ops.clone(), vec![4022862081]);
    verify_repro(ops.clone(), vec![100]);
    verify_repro(ops.clone(), vec![50]);
    verify_repro(ops.clone(), vec![20]);
}

#[test]
fn fuzz_artifact_nevim_peek_stack_modification() {
    let ops = vec![ Praise ];
    verify_repro(ops, vec![-11918861, 0]);
}

#[test]
fn fuzz_artifact_run_length() {
    let ops = vec![ And ];
    verify_repro(ops, vec![-1224979098644774912, 0]);
}

#[test]
fn fuzz_cfg_interpreter_also_deopts() {
    let ops = vec![ Increment, Swap, ];
    verify_repro(ops, vec![0, 0, -2]);
}

#[test]
fn fuzz_pop_error2() {
    let ops = vec![ Qeq, ];
    verify_repro(ops, vec![2893044002181676845, 0]);
}

#[test]
fn fuzz_gcd_range_tracking_bug() {
    let ops = vec![
        DigitSum,
        Gcd2,
        Gcd2,
        DigitSum,
    ];
    verify_repro(ops, vec![-1, 528983428994, 71776119063904255, 0]);
}

#[test]
fn fuzz_bulkxor_ordering() {
    let ops = vec![
        DigitSum, DigitSum, Increment, LenSum, DigitSum, LenSum,
        DigitSum,
        BulkXor,
    ];
    verify_repro(ops, vec![-8659344755311771648, -8647043227960016249, 0]);
}

#[test]
fn fuzz_tetration_which_always_fails() {
    let ops = vec![
        DigitSum,
        Increment,
        DigitSum,
        LenSum,
        Increment,
        DigitSum,
        Increment,
        TetrationNumIters,
    ];
    verify_repro(ops, vec![9163700435218548299, 5424162628174564166, 0]);
}

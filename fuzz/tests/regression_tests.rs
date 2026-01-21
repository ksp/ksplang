use ksplang::{compiler::test_utils::{ReproData, verify_repro, verify_repro_const}, ops::Op::{self, *}};

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
    let ops = vec![ DigitSum, Increment, DigitSum, LenSum, Increment, DigitSum, Increment, TetrationNumIters, ];
    verify_repro(ops, vec![9163700435218548299, 5424162628174564166, 0]);
}


#[test]
fn fuzz_funkcia_simplification_bug() {
    let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Funkcia, And, Funkcia ];
    verify_repro(ops, vec![2, 1, 0]);
}

#[test]
fn fuzz_select_ranges_arity() {
    let ops = vec![ DigitSum, DigitSum, Gcd2, DigitSum, DigitSum, DigitSum, Modulo, And, Funkcia, ];
    verify_repro(ops, vec![-280485640011906, -1099327092737, 0]);
}

#[test]
fn fuzz_select_ranges_arity2() {
    let ops = vec![ DigitSum, DigitSum, Gcd2, DigitSum, DigitSum, DigitSum, Modulo, And, Funkcia, Max, And, ];
    verify_repro(ops, vec![1843385120036290559, 68100994365206283, 4294967295]);
}

#[test]
fn fuzz_median4() {
    let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Funkcia, Increment, Increment, Increment, Increment, Median, ];
    verify_repro(ops, vec![6462577159401615359, 3411951361811483263, 0]);
}

#[test]
fn fuzz_deopt_bad_ctr_increment() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Jump, ];
    verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_gpc_multiple_constants() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Increment, Praise, GcdN, ];
    verify_repro(ops, vec![-1, -1, 0]);
}

#[test]
fn fuzz_median2_rounding() {
    let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Funkcia, And, Increment, Increment, Median, ];
    verify_repro(ops, vec![42, -1, 0]);
}

#[test]
fn fuzz_roll_zero() {
    let ops = vec![ DigitSum, Increment, DigitSum, LenSum, Increment, DigitSum, TetrationItersNum, DigitSum, Roll, ];
    verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_select_simplificaiton_large() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, Remainder, DigitSum, DigitSum, DigitSum, Max, DigitSum, Modulo, Remainder, Increment, BulkXor, Remainder, Remainder, Increment, And, ];
   verify_repro(ops, vec![-14694063110410753, -50722894626733825, -3032071681, 8857255856174097162, 562945977220957]);
}

#[test]
fn fuzz_select_simplification() {
    let ops = vec![ DigitSum, DigitSum, Remainder, DigitSum, DigitSum, Remainder, Increment, BulkXor, ];
    verify_repro(ops, vec![42, 43, 67]);
}

#[test]
fn fuzz_jump_increment_at_program_end() {
    let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, Increment, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment ];
    verify_repro(ops, vec![123, 1234, 89999999]);
}

#[test]
fn fuzz_stack_size_overflow() { // TODO: how do we want to handle this? for now it's ignored in fuzzer
    let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, Praise, Max, Qeq, Praise ];
    verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_stack_size_overflow2() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, Increment, Praise, Increment, DigitSum, Praise, Praise ];
   verify_repro(ops, vec![1, 1, 255]);
}

#[test]
fn fuzz_funkcia_negative_input_range() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, Funkcia, ];
   verify_repro(ops, vec![1, 1, 7]);
}

#[test]
fn fuzz_bitshift_deopt() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, Bitshift ];
   verify_repro(ops, vec![1, 1, 1]);
}

#[test]
fn fuzz_swap0_divisivility_alias_analysis() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, Praise, DigitSum, LSwap, Modulo, Remainder, Swap, LSwap, ];
   verify_repro(ops, vec![0, 1, 10]);
}

#[test]
fn fuzz_bad_zero_divisibility_assume() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Remainder, DigitSum, DigitSum, Swap, DigitSum, LSwap, Qeq, ];
   verify_repro(ops, vec![855484965027766032, 812630658534838159, 0]);
}

#[test]
fn fuzz_another_divisibility_simplification_bug() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Remainder, DigitSum, Remainder, ];
   verify_repro(ops, vec![1, 1, 1]);
}

#[test]
fn fuzz_spill_and_deopt() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Increment, Praise, DigitSum, Praise, Gcd2, Remainder, Qeq, BulkXor, ];
   verify_repro(ops, vec![3602879701889992651, -3454260914193170432, 0]);
}

#[test]
fn fuzz_gcd_min_deopt() {
   let ops = vec![ Gcd2, ];
   verify_repro(ops, vec![0, 0, 0, 0, i64::MIN]);
}

#[test]
fn fuzz_gcd_min_deopt2() {
   let ops = vec![ DigitSum, LSwap, DigitSum, Bitshift, Gcd2, ];
   verify_repro(ops, vec![9999999, 0, 0]);
}

#[test]
fn fuzz_bitshift_negative_range_1() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, Remainder, DigitSum, Increment, Bitshift, Remainder, Increment, DigitSum, Increment, Remainder, ];
   verify_repro(ops, vec![1, 1, 79]);
}

#[test]
fn fuzz_bitshift_negative_range_2() {
    // only fails with range-checking interpreter
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, Remainder, DigitSum, Increment, Bitshift ];
   verify_repro(ops, vec![1, 1, 79]);
}

#[test]
fn fuzz_hoisting_no_space_1() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, Remainder, DigitSum, DigitSum, Modulo, Qeq, Increment, Increment, Increment, Increment, Increment, Pop, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Increment, Increment, Increment, DigitSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, Modulo, DigitSum, DigitSum, Increment, Increment, And, Remainder, DigitSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Increment, Increment, Increment, LenSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, Modulo, DigitSum, DigitSum, Increment, Increment, Increment, Pop, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, And, Remainder, DigitSum, Increment, Bitshift, DigitSum, Pop2, Increment, Increment, Increment, LenSum, Increment, Increment, ];
   verify_repro(ops, vec![4851502695418381121, -53126547782941885, 33554431]);
}

#[test]
fn fuzz_hoisting_no_space_2() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, Remainder, DigitSum, DigitSum, Modulo, Qeq, Increment, Increment, Increment, Pop, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Increment, Increment, Increment, DigitSum, Increment, Bitshift, DigitSum, Modulo, DigitSum, DigitSum, Increment, Increment, And, Remainder, DigitSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Increment, Increment, And, Remainder, DigitSum, Increment, Remainder, Remainder, Remainder, Remainder, Increment, Increment, ];
   verify_repro(ops, vec![-60413, -3187671041, 0]);
}

#[test]
fn fuzz_hoisting_no_space_3() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, Remainder, DigitSum, DigitSum, Modulo, Qeq, Increment, Increment, Pop, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, Increment, DigitSum, Increment, DigitSum, Increment, Bitshift, DigitSum, Modulo, DigitSum, DigitSum, Increment, Increment, And, Remainder, DigitSum, Increment, Bitshift, DigitSum, Pop2, DigitSum, DigitSum, Increment, Increment, Increment, And, Remainder, DigitSum, Increment, Remainder, Remainder, Remainder, Increment, Remainder, ];
   verify_repro(ops, vec![-15466496, 288230372964040703, 1]);
}

#[test]
fn fuzz_probably_cyclic_phi_swaps() {
   let ops = vec![ LSwap, LSwap, Pop, DigitSum, DigitSum, Remainder, Increment, DigitSum, DigitSum, DigitSum, Remainder, Qeq, DigitSum, DigitSum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Increment, DigitSum, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, Increment, Pop, DigitSum, DigitSum, DigitSum, Remainder, Remainder, Increment, Increment, DigitSum, DigitSum, Remainder, Qeq, Remainder, Remainder, ];
   verify_repro(ops, vec![-5781140590214271057, 4868117448974905171, -5781140590221376701, 175]);
}

#[test]
fn fuzz_i_forgot_whats_this() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, Increment, DigitSum, DigitSum, Modulo, Qeq, ];
   verify_repro(ops, vec![-253, -739441781291, 0]);
}

#[test]
fn fuzz_jump_overflow1() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Jump, Qeq, Jump ];
   verify_repro(ops, vec![1, 1, 1]);
}

#[test]
fn fuzz_jump_overflow2() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, Jump, ];
   verify_repro(ops, vec![9150749290107117950, -72007441148674178, 0]);
}

#[test]
fn fuzz_ctr_increment_need_to_hold_registers_in_allocator() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, Remainder, Jump, Increment, Max, TetrationNumIters, ];
   verify_repro(ops, vec![0, 0, 111]);
}

#[test]
fn fuzz_invalid_mul_add_normalization() {
   let ops = vec![ DigitSum, Increment, DigitSum, Increment, DigitSum, DigitSum, LenSum, Universal, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_variadic_op_ran_out_of_temp_registers() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, Gcd2, Max, Max, Max, DigitSum, DigitSum, DigitSum, Increment, DigitSum, LenSum, Goto, Max, Praise, Roll, ];
   verify_repro(ops, vec![4431242408380362622, 648518346341351423, 7144743315925499684, 2337]);
}

#[test]
fn fuzz_invalid_mul_to_shift_optimization() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Remainder, DigitSum, DigitSum, Increment, Max, Increment, Max, DigitSum, Universal, DigitSum, GcdN, Roll, ];
   verify_repro(ops, vec![8033895653830950782, -244091581890705, -7813745819768708738]);
}

#[test]
fn fuzz_gcd_preserve_error_in_variadics() {
   let ops = vec![ DigitSum, Bitshift, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Gcd2, Gcd2, Gcd2, ];
   verify_repro(ops, vec![281894152633852286, 36825871673603, 16794249597]);
}

#[test]
fn fuzz_obc_ksplangopsincrement_deopt_bug1() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, Modulo, DigitSum, DigitSum, DigitSum, LenSum, Jump, Increment, Increment, Max, TetrationNumIters, ];
   verify_repro(ops, vec![1, 1, 179]);
}

#[test]
fn fuzz_obc_ksplangopsincrement_deopt_bug2() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, DigitSum, BulkXor, Qeq, DigitSum, Increment, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Bitshift, Increment, TetrationNumIters, DigitSum, ];
   verify_repro(ops, vec![9114925018868809795, -71982827398290050, 163255447823154725]);
}

#[test]
fn fuzz_index_out_of_range_in_dataflow() {
   let ops = vec![ DigitSum, Bitshift, DigitSum, DigitSum, Remainder, DigitSum, Increment, DigitSum, DigitSum, Remainder, Increment, DigitSum, LSwap, BranchIfZero, Modulo, Max, LSwap, BranchIfZero, Modulo, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_obc_ctr_increment_another_deopt_bug() {
   let ops = vec![ Funkcia, Max, DigitSum, DigitSum, DigitSum, DigitSum, LenSum, Jump, Increment, Increment, DigitSum, BulkXor, BranchIfZero, Bitshift, Median, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0]);
}

#[test]
fn fuzz_obc_ctr_increment_another_deopt_bug2() {
   let ops = vec![ DigitSum, Pop, Remainder, DigitSum, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, DigitSum, Increment, DigitSum, LenSum, DigitSum, BulkXor, Pop, Jump, Increment, Goto, ];
   verify_repro(ops, vec![0, -3927539563580481243, -7822895346882761217, -7812620392308268763, 2738140736658829182, 126]);
}

#[test]
fn fuzz_single_median_item() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, LenSum, Increment, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Remainder, TetrationItersNum, Increment, Increment, Median, ];
   verify_repro(ops, vec![-40533015121625089, -40533483273060346, 0]);
}

#[test]
fn aby_fuzzer_nebrečel() {
   let ops = vec![ ];
   verify_repro(ops, vec![]);
}


#[test]
fn fuzz_qeq_invalid_div_operation() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, LenSum, DigitSum, DigitSum, DigitSum, Increment, Increment, Increment, DigitSum, DigitSum, Remainder, Qeq, Qeq, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_stackswap_optimization_unexpected_deopt() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Swap, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, Swap, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Swap, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_abssub_sub_invalid_optimization() {
   let ops = vec![ DigitSum, Increment, DigitSum, LenSum, DigitSum, DigitSum, Funkcia, Qeq, Increment, DigitSum, DigitSum, LenSum, DigitSum, Remainder, Increment, DigitSum, Universal, ];
   verify_repro(ops, vec![0, 0, 12345]);
}

#[test]
fn fuzz_missing_tetration_optimization_assert() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Modulo, DigitSum, DigitSum, Swap, TetrationItersNum, ];
   verify_repro(ops, vec![-1, 0, 126]);
}

#[test]
fn fuzz_something_with_swaps() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, Increment, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, DigitSum, LSwap, BranchIfZero, TetrationNumIters, Modulo, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Goto, ];
   let (_g, obc) = verify_repro(ops, vec![666, 777777, 3]);
    assert!(obc.program.len() < 30, "Too long program, did some optimization fail?");
}

#[test]
fn fuzz_tetration_missing_iteration_check() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Increment, DigitSum, Remainder, Increment, BulkXor, Jump, Increment, TetrationNumIters, ];
   verify_repro(ops, vec![-70368758522500311, -56034555, 0]);
}

#[test]
fn fuzz_swap_interfering_deopt1() {
   let ops = vec![ DigitSum, DigitSum, Swap, LSwap, DigitSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, Goto, ];
   verify_repro(ops, vec![1, 0, 0]);
}
#[test]
fn fuzz_swap_interfering_deopt2() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, Swap, Funkcia, LSwap, DigitSum, Increment, BranchIfZero, Pop, DigitSum, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, DigitSum, Max, DigitSum, LenSum, Goto, ];
   verify_repro(ops, vec![1, 0, 1]);
}

#[test]
fn fuzz_swap_invalid_removal1() {
   let ops = vec![ DigitSum, LSwap, DigitSum, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Goto, ];
   verify_repro(ops, vec![1, 0, 0]);
}

#[test]
fn fuzz_swap_invalid_removal2() {
   let ops = vec![ LSwap, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Modulo, Goto, ];
   verify_repro(ops, vec![6148914691236517502, 2377910638922800284, 0]);
}

#[test]
fn fuzz_nop_assert_simplification() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, Increment, Increment, Increment, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, TetrationNumIters, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_somehow_magically_value_had_empty_range() {
   let ops = vec![ DigitSum, DigitSum, TetrationNumIters, DigitSum, LSwap, Modulo, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, Increment, DigitSum, LSwap, BranchIfZero, TetrationNumIters, And, And, And, And, And, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_broken_div_mul_add_mod_pattern() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, Median, DigitSum, Increment, Increment, DigitSum, DigitSum, LenSum, Universal ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_invalid_lensum_mod_2_optimization() {
   let ops = vec![ DigitSum, Increment, LenSum, DigitSum, DigitSum, LenSum, DigitSum, DigitSum, Remainder, Qeq, Increment ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_ctr_increment_empty_input_array() {
   let ops = vec![ DigitSum, DigitSum, Modulo, DigitSum, DigitSum, Increment, Gcd2, BulkXor, DigitSum, DigitSum, Remainder, BulkXor, Jump, Increment, ];
   verify_repro(ops, vec![0, 0, 0]);
}

#[test]
fn fuzz_select_of_select_condition_simplification() {
   let ops = vec![ DigitSum, Swap, DigitSum, TetrationItersNum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, BulkXor, Increment, Swap, DigitSum, TetrationItersNum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, BulkXor, Increment, DigitSum, Swap, DigitSum, TetrationItersNum ];
   verify_repro(ops, vec![-1, 0, 0, 1, 0]);
}

#[test]
fn fuzz_deopt_on_terminated_block_crash() {
   let ops = vec![ Bitshift, Swap, DigitSum, DigitSum, DigitSum, DigitSum, Remainder, DigitSum, Increment, Increment, Max, Praise, Remainder, LSwap, Modulo, BranchIfZero, Remainder, Remainder, Swap, Increment, DigitSum, Max, Max, Max, Max, DigitSum, DigitSum, DigitSum, Funkcia, Swap, Increment, DigitSum, DigitSum, DigitSum, DigitSum, Funkcia, Qeq, ];
   verify_repro(ops, vec![0; 20]);
}

#[test]
fn fuzz_deopt_on_deferred_stack_swap_is_invalid() {
   let ops = vec![ DigitSum, DigitSum, Increment, LenSum, DigitSum, LenSum, Swap, LenSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, Call, ];
   verify_repro(ops, vec![0, 0, 0, 0]);
}

#[test]
fn fuzz_invalid_range_condition_push_though_modulo() {
   let ops = vec![ LenSum, DigitSum, Increment, LenSum, DigitSum, LenSum, Praise, DigitSum, DigitSum, DigitSum, Swap, Remainder, Modulo, TetrationNumIters, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]);
}


#[test]
fn fuzz_missing_value_materialization_in_ctr_increment_deopt() {
   let ops = vec![ DigitSum, DigitSum, Increment, LenSum, Jump, Increment, Increment, Increment, Increment, Increment, BulkXor, Jump, Increment, Pop, LenSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Praise, Roll, Increment, BulkXor, ];

   verify_repro(ops, vec![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn fuzz_value_materialization_in_ctr_increment_deopt_bug() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, BulkXor, Jump, Increment, Remainder, ];
   verify_repro(ops, vec![-290271069732865, 2964283004886712319, -347875573761, -6413125852061499357, -6796097142415970305, 7595878676688797947, 7566047376929042281, 251]);
}

#[test]
fn fuzz_overflow_in_divisibility_check() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Funkcia, And, Qeq, ];
   verify_repro(ops, vec![-7061644220011816657, 476710435850919325, -7089369500922937345, -9223372036854775808, -1, 0]);
}

#[test]
fn fuzz_overflow_in_curseddiv_div_check() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Increment, Gcd2, Gcd2, Gcd2, Gcd2, Increment, Increment, Universal, ];
   verify_repro(ops, vec![-8102099357864558841, -8102099357864587377, -16327203, -1, -9223372036854775808, -1, -66991989383495681, -16327203, -1, -9223372036854775808, 0]);
}

#[test]
fn fuzz_funkcia_broken_range_inferrence_for_zero_arg() {
   let ops = vec![ Pop, Pop2, Funkcia, LSwap, LenSum, DigitSum, DigitSum, DigitSum, Increment, Gcd2, DigitSum, LSwap, BranchIfZero, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, -35465847065564229, 0, 0, 0, 0]);
}

#[test]
fn fuzz_artifact_obc_deopts_earlier_than_necessary() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, LenSum, Jump, Increment, Increment, Increment, GcdN, ];
   verify_repro(ops, vec![434586871141, -9223372036854775808, 0]);
}

#[test]
fn fuzz_artifact_obc_deopts_earlier_than_necessary2() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, LenSum, Jump, Increment, Increment, Increment, GcdN, ];
   verify_repro(ops, vec![72056713559500133, -9223372036854775808, 0]);
}

#[test]
fn fuzz_single_value_gcd_is_abs() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Modulo, DigitSum, Increment, DigitSum, Qeq, DigitSum, Increment, LenSum, GcdN, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, 1]);
}

#[test]
fn fuzz_crash_on_divides_by_i64min() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, Praise, Funkcia, DigitSum, DigitSum, DigitSum, DigitSum, DigitSum, Increment, Increment, Funkcia, Max, Bitshift, DigitSum, LSwap, Remainder, BranchIfZero, Max, Median, Remainder, ];
   verify_repro(ops, vec![0;20]);
}

#[test]
fn fuzz_mod_range_ops_overflow() {
   let ops = vec![ LenSum, DigitSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Call, Increment, Increment, Increment, Max, Increment, Increment, Bitshift, Remainder, ];
   verify_repro(ops, vec![-1013027338595650367, 216173890215346175, 4611685126606946303, -5787213827046136020, 4557430889879941039, 4991471925827288895, 6462665444868593045, 3801512248693702575, 0]);
}

#[test]
fn fuzz_bitshift_negative_range() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, Increment, Increment, Increment, Increment, DigitSum, DigitSum, Remainder, Qeq, Bitshift, ];
   verify_repro(ops, vec![4455748147947192641, -69242844287401985, -57983845218765633, 5570194071739171000, 3026269155315731789, 8604979239799224071, 9212068884851457911, 1978051483820414, 506381572169269247, 8608480567731124075, 565191891875397495, -2882304347923322105, 20480]);
}

#[test]
fn fuzz_bad_div_eq_condition_simplification() {
   let ops = vec![ DigitSum, DigitSum, LenSum, Jump, Increment, Increment, Increment, Increment, Increment, DigitSum, DigitSum, Funkcia, LSwap, LSwap, Qeq, Swap, LSwap, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 1, 0]);
}

#[test]
fn fuzz_variadic_op_deopt_input_reg_overwrite() {
   let ops = vec![ LenSum, Increment, DigitSum, Increment, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 49733868826177713, 8608393193207168768, 65405]);
}

#[test]
fn fuzz_mod_range_ops_overflow2() {
   let ops = vec![ DigitSum, DigitSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Call, Increment, Increment, Increment, Max, Increment, Increment, Increment, Increment, Bitshift, Modulo, ];
   verify_repro(ops, vec![-1, -5787224822168083515, 4557525817606123439, 4557430888798830399, -5787213827046133841, -6842197495944951377, -5342947728991, -1281, -5787308985970982913, -7668198946217414737, 0]);
}

#[test]
fn fuzz_crash_on_late_deopt_unreachable() {
   let ops = vec![ DigitSum, Increment, DigitSum, LenSum, DigitSum, DigitSum, Increment, Increment, DigitSum, DigitSum, Remainder, Qeq, DigitSum, Remainder, Gcd2, Increment, Increment, Increment, ];
   verify_repro(ops, vec![72339069014638591, -22606306925871105, -1347440641, -1, -5773051772335554561, -81, -1, -344944811521, -1, 0]);
}

#[test]
fn fuzz_invalid_div_eq_0_pushdown() {
   let ops = vec![ Increment, DigitSum, DigitSum, Remainder, DigitSum, Increment, DigitSum, DigitSum, Remainder, Qeq, DigitSum, Increment, DigitSum, LenSum, DigitSum, DigitSum, Remainder, Qeq, DigitSum, Remainder, ];
   verify_repro(ops, vec![-5188146770730811465, -1, -1, -5188146770730811393, -5208412970261938177, -73, -5188147079968456705, 0]);
}

#[test]
fn fuzz_hoisting_changes_effect_and_makes_it_invalid1() {
   let ops = vec![ LSwap, DigitSum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Modulo, Qeq, LSwap, DigitSum, DigitSum, DigitSum, DigitSum, Modulo, Qeq, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn fuzz_hoisting_changes_effect_and_makes_it_invalid2() {
   let ops = vec![ LSwap, DigitSum, DigitSum, Pop2, Increment, DigitSum, DigitSum, DigitSum, Modulo, Qeq, LSwap, DigitSum, DigitSum, Gcd2, DigitSum, DigitSum, DigitSum, Modulo, Qeq, LSwap, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn fuzz_bad_shiftl_effect_inferrence() {
   let ops = vec![ DigitSum, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, DigitSum, Increment, DigitSum, DigitSum, Bitshift, DigitSum, BranchIfZero, DigitSum, Max, BranchIfZero, Bitshift, DigitSum, Increment, DigitSum, Gcd2, DigitSum, DigitSum, Remainder, Qeq, Bitshift, DigitSum, Increment, Max, Sum, DigitSum, Gcd2, DigitSum, DigitSum, Remainder, Qeq, DigitSum, DigitSum, Increment, LenSum, ];
   verify_repro(ops, vec![-61453979541569717, -2344273723743273180, 8608480567731124087, 7081852463225730852, -61453979541569717, -2344273723743273180, 8608480567731124087, 8608480567737939748, -2315130579621707519, 7081852463225449695, -61453979545305269, -2314885530818492853, -3799266470416135354, -2594229207528946105, -1, -1, -1, -59672695062659073, -1, -1, -1, -1, -1, -14942209, -1, -280513443004417, -1, -237077911960321, -1, -22734945524908227, -1, -1, -1, -1099511627775, -1, -1268899090616287233, 9161166084165075764, -8757377, 5422135737521669119]);
}

#[test]
fn fuzz_unreachable_block_causes_crashes() {
   let ops = vec![ DigitSum, DigitSum, DigitSum, Increment, LSwap, DigitSum, DigitSum, LSwap, DigitSum, LSwap, DigitSum, DigitSum, Remainder, Qeq, Remainder, LSwap, DigitSum, LenSum, Praise, Universal, ];
   verify_repro(ops, vec![-1012762419733073423, -1012762423789014735, 0]);
}

#[test]
fn fuzz_block_parameter_value_removal() {
   let ops = vec![ Gcd2, Increment, LSwap, DigitSum, LenSum, DigitSum, LSwap, DigitSum, LenSum, DigitSum, LSwap, DigitSum, DigitSum, Remainder, Qeq, DigitSum, LSwap, DigitSum, LenSum, Praise, LSwap, DigitSum, DigitSum, Remainder, Qeq, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, Max, ];
   verify_repro(ops, vec![0; 4]);
}

#[test]
fn fuzz_value_only_used_in_deopt_got_smashed_by_regalloc() {
   let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, Increment, DigitSum, DigitSum, LenSum, Pop2, DigitSum, DigitSum, Funkcia, Qeq, Pop2,
                   DigitSum, DigitSum, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Funkcia, Qeq,
                   Pop2, DigitSum, Increment, DigitSum, DigitSum, DigitSum, Funkcia, Qeq ];
   verify_repro(ops, vec![0, 120, 0]);
}

#[test]
fn fuzz_block_terminated_by_simplifier_optimization() {
   let ops = vec![ DigitSum, Increment, Increment, Increment, DigitSum, DigitSum, Increment, DigitSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, TetrationNumIters, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, Bitshift, Max, DigitSum, Increment, DigitSum, Gcd2, Universal, ];
   verify_repro(ops, vec![-185, 5424383215664581631, 0]);
}

#[test]
fn fuzz_crash_in_range_ops_mod_noneuclidean() {
   let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, DigitSum, LenSum, Praise, Pop, Funkcia, DigitSum, LSwap, Modulo, Max, LenSum, DigitSum, DigitSum, Remainder, Qeq, Remainder, Remainder, Increment, Swap, ];
   verify_repro(ops, vec![-5908722711413264915, -1012762419733090899, 0]);
}

#[test]
fn fuzz_yet_another_way_the_iterated_binary_gcd_does_not_work() {
   let ops = vec![ Modulo, DigitSum, Bitshift, DigitSum, Increment, DigitSum, And, DigitSum, DigitSum, DigitSum, Increment, Gcd2, Universal, DigitSum, Increment, Gcd2, Gcd2, ];
   verify_repro(ops, vec![1085102592571150095, 1085102592571198463, -1034834473201, 1099511566095]);
}

#[test]
fn fuzz_cyclical_phis_stack_smashing() {
   let ops = vec![ Modulo, And, Max, LSwap, LenSum, DigitSum, DigitSum, DigitSum, Increment, Gcd2, DigitSum, LSwap, BranchIfZero, ];
   verify_repro(ops, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0]);
}

#[test]
fn sanity_check_const_input() {
    let ops = vec![ Roll, Universal, DigitSum, Increment, And ];
    let r = ReproData::new(ops, [1000, 1001, 1002, 1003, 1004])
            .with_constin([0, 123, 124, 2, 5]);
    r.verify();
    let r = ReproData::new([], [])
            .with_constin([0]);
    r.verify();
    let r = ReproData::new([], [])
            .with_constin([]);
    r.verify();
    let r = ReproData::new([], [0])
            .with_constin([]);
    r.verify();
}

#[test]
fn fuzz_obc_arrayop_incorred_deopt_and_const_load() {
   let ops = vec![ DigitSum, DigitSum, LenSum, DigitSum, Funkcia, DigitSum, Increment, Increment, Increment, Median, Median ];
   verify_repro(ops, vec![-1052266987521, -68961369294110966, 0]);
}

#[test]
fn fuzz_median_cursed_simplification_to_deopt() {
   let ops = vec![ DigitSum, LenSum, DigitSum, DigitSum, DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, BulkXor, BranchIfZero, Roll, Median ];
   verify_repro(ops, vec![506382253224885243, -1, 0]);
}

#[test]
fn fuzz_variadic_mul_const_propagation() {
    let ops = vec![ DigitSum, DigitSum, Increment, DigitSum, DigitSum, LenSum, Universal, Increment, Increment, DigitSum, DigitSum, Increment, Increment, Increment, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, Increment, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal ];
    verify_repro(ops, vec![2531906053038088995, 3684827553939530531, 0]);
}

#[test]
fn fuzz_one_more_jump_cyclical_phi_bug() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, LenSum, DigitSum, Funkcia, Pop2, Increment, DigitSum, DigitSum, Bitshift, Increment, DigitSum, LSwap, LSwap, Increment, Roll, BranchIfZero, Max, Modulo, Swap, Increment, Max, LSwap, Max, Modulo, Swap, Swap, Increment, Increment, Praise, LenSum, Max, Increment, Increment, Max ];
    verify_repro(ops, vec![4557430892032626447, 1080933451445567232, -178120883765489, 1085102528955105087, 0]);
}

#[test]
fn fuzz_hoisting_common_instruction_fix() {
    let ops = vec![ DigitSum, Increment, DigitSum, DigitSum, Increment, DigitSum, DigitSum, Remainder, Qeq, Increment, DigitSum, Increment, DigitSum, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, DigitSum, Gcd2, DigitSum, DigitSum, Remainder, Qeq, Increment, DigitSum, Increment, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment ];
    verify_repro(ops, vec![-3906369333256179659, -1, 0]);
}

#[test]
fn fuzz_empty_range_in_osmibyte_compiler() {
    let ops = vec![ Modulo, Funkcia, DigitSum, DigitSum, Increment, DigitSum, Increment, DigitSum, Gcd2, Gcd2, Gcd2, DigitSum, LenSum, DigitSum, BranchIfZero, DigitSum, LenSum, DigitSum, Max, Praise, Max, Max, Max, Modulo, Funkcia, Max, DigitSum, Bitshift, DigitSum, Bitshift, DigitSum, LSwap, Modulo, DigitSum, LSwap, BranchIfZero, Increment, Remainder, LSwap, BranchIfZero, LSwap, BranchIfZero, Increment, Jump, Max, Gcd2, Gcd2, Increment, BulkXor, BulkXor, BulkXor, BulkXor, BulkXor, Increment, And, And ];
    verify_repro(ops, vec![2531906049341864879, 9, 4051332257732442615, -144681187489743559, 0]);
}

#[test]
fn fuzz_multiset_add_removal() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, LenSum, DigitSum, DigitSum, DigitSum, Modulo, Universal, Increment, DigitSum, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, LenSum, DigitSum, DigitSum, DigitSum, Modulo, Universal, Increment, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, Pop2, DigitSum, LenSum, Universal, Gcd2 ];
    verify_repro(ops, vec![-3761654902719526028, -3798844061601365756, 0]);
}

#[test]
fn fuzz_stackswap_realises_range_is_empty() {
    let ops = vec![ Pop, Max, DigitSum, DigitSum, Gcd2, Increment, Gcd2, Gcd2, DigitSum, LenSum, DigitSum, BranchIfZero, DigitSum, LenSum, DigitSum, Max, Praise, Max, Max, Max, Modulo, Funkcia, Max, DigitSum, Bitshift, DigitSum, Bitshift, DigitSum, LSwap, Modulo, DigitSum, LSwap, Remainder, BranchIfZero, LSwap, BranchIfZero, Swap, Call, Call, Max, DigitSum, Increment, Increment ];
    verify_repro(ops, vec![-1, -881390843, 432345564227567615, -13449, 8577956512327008255, 0]);
}

#[test]
fn fuzz_swap_read_removal_removes_deopt() {
    let ops = vec![ DigitSum, LenSum, Increment, DigitSum, Increment, Increment, DigitSum, LenSum, DigitSum, LenSum, Increment, Increment, Increment, Increment, Increment, DigitSum, Swap, LenSum, DigitSum, DigitSum, LenSum, BulkXor, Jump, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Swap, Call ];
    verify_repro(ops, vec![-50753800347340881, 648799821239136175, -5764607523034234881, -198257032560821, -198257032606801, 5453771187815402415, -5787125524196249601, -5787125524196249601, 0]);
}

#[test]
fn fuzz_invalid_deopt_for_arrayop() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, Median, Median ];
    verify_repro_const(ops, vec![0], vec![9, -1, -1, -1, -9]);
}
#[test]
fn fuzz_median_4_with_many_constants_did_run_into_some_should_not_happen_assert() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, LSwap, Gcd2, Funkcia, DigitSum, LSwap, Median ];
    verify_repro_const(ops, vec![0], vec![6101267679832641267, 6896745891131031553]);
}

#[test]
fn fuzz_qeq_int_min_neg_one_division_edge_case() {
    let ops = vec![ Qeq ];
    verify_repro_const(ops, vec![-9223372036854775808], vec![-1, 0]);
}

#[test]
fn fuzz_unchecked_rem_in_qeq() {
    let ops = vec![ Qeq ];
    verify_repro_const(ops, vec![0], vec![i64::MIN, -1, 0]);
}

#[test]
fn fuzz_rem_wrapping() {
    let ops = vec![ DigitSum, DigitSum, LSwap, Modulo, Bitshift, Modulo ];
    verify_repro_const(ops, vec![255], vec![-1, 9220557287087669247]);
}

#[test]
fn fuzz_block_get_terminated_in_push_swap() {
    let ops = vec![ DigitSum, DigitSum, LSwap, Remainder, DigitSum, Increment, LSwap, Remainder, DigitSum, DigitSum, Remainder, DigitSum, Call ];
    verify_repro_const(ops, vec![0], vec![-576741896551463425]);
}

#[test]
fn fuzz_invalid_add_sub_optimization() {
    let ops = vec![ Universal, Increment ];
    verify_repro_const(ops, vec![0], vec![9223372036854775807, 1]);
}

#[test]
fn fuzz_invalid_median_to_div_optimization() {
    let ops = vec![ DigitSum, DigitSum, Median, LenSum, Gcd2, DigitSum, DigitSum, Increment, LenSum, Call, Max, Gcd2, Gcd2, Gcd2, Gcd2, Gcd2, Gcd2, Max ];
    verify_repro_const(ops, vec![0], vec![-280654637957121, -1, -8193, -1, -1, 2559 ]);
}

#[test]
fn fuzz_median_simplification_to_div_with_non2_value() {
    let ops = vec![ LSwap, Modulo, DigitSum, LSwap, DigitSum, LenSum, Median ];
    verify_repro_const(ops, vec![53713], vec![-1219009850024132609, -66088542984596172, 3, 91]);
}

#[test]
fn fuzz_median_spilled_output_handling() {
    let ops = vec![ Praise, Roll, Max, Remainder, Increment, LSwap, DigitSum, LSwap, Median, LSwap, LSwap, Max, Max, LenSum, Max, BulkXor ];
    verify_repro_const(ops, vec![0], vec![0, 8]);
}

#[test]
fn fuzz_some_swap_problem_TODO() {
    let ops = vec![ Max, DigitSum, Increment, LenSum, DigitSum, DigitSum, LenSum, Median, LSwap, DigitSum, LSwap, Remainder, BranchIfZero, Pop, Call ];
    verify_repro_const(ops, vec![-5714873315750497025, 0], vec![272339441856688]);
}

#[test]
fn fuzz_obc_multiplication_with_overflow() {
    let ops = vec![ DigitSum, DigitSum, DigitSum, DigitSum, Swap, Modulo, Increment, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal ];
    verify_repro_const(ops, vec![-1027579379729, 255], vec![-6781891201990876]);
}

#[test]
fn fuzz_bug_mul_overflow_in_cfg_interpreter() {
    let ops = vec![ LSwap, DigitSum, LenSum, Increment, Increment, DigitSum, DigitSum, LenSum, Universal, DigitSum, DigitSum, And, DigitSum, Increment, DigitSum, LenSum, Universal, Increment, DigitSum, DigitSum, LenSum, DigitSum, LenSum, Universal ];
    verify_repro_const(ops, vec![10009], vec![16325548649466666, 87, 15]);
}

#[test]
fn fuzz_euclidean_modulo_range_ops_mul_overflow() {
    let ops = vec![ Swap, Modulo, Swap ];
    verify_repro_const(ops, vec![0], vec![9223372036854775807, -4671077238513065943, 2325686995071728639]);
}

#[test]
fn fuzz_obc_temp_register_allocation_pollution() {
    let ops = vec![ DigitSum, DigitSum, Praise, Max, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Increment, Roll, DigitSum, DigitSum, DigitSum, Swap, BranchIfZero, Max, Max, Max, Max, Max, Max, Pop, Max, Max, Max, BulkXor, LSwap, Modulo, Jump, Praise, Funkcia, Median, Max, Roll, Max, Sum, Modulo, BulkXor, Funkcia ];
    verify_repro_const(ops, vec![-1089724887719042, -577867611791490817, 0], vec![4107282509986059614]);
}

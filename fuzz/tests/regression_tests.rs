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
    assert!(obc.program.len() < 25, "Too long program, did some opt fail?");
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


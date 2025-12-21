use std::cmp;

use crate::compiler::{
    cfg::GraphBuilder, cfg_interpreter, osmibytecode::OsmibytecodeBlock, osmibytecode_vm::{self, ExitPointId, RegFile}, precompiler::{NoTrace, Precompiler}
};
use crate::vm::{self, VMOptions, RunError};
use crate::ops::Op;

const PI_TEST_VALUES: [i8; 42] = [
    3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5,
    0, 2, 8, 8, 4, 1, 9, 7, 1, 6,
];

pub fn verify_repro(ops: Vec<Op>, input: Vec<i64>) {
    let g = GraphBuilder::new(0);
    let mut precompiler = Precompiler::new(&ops, input.len(), false, 0, 2_000, true, None, g, NoTrace());
    precompiler.bb_limit = 32;
    precompiler.instr_limit = 500;
    precompiler.interpret();
    let g = precompiler.g;
    // if is_trivial(&g) { return; }
    println!("{g}");

    let obc_block = OsmibytecodeBlock::from_cfg(&g);
    println!("{obc_block}");

    let mut obc_stack = input.clone();
    let mut regs = RegFile::new();
    let obc_res = osmibytecode_vm::interpret_block::<true>(&obc_block, &mut obc_stack, &mut regs);

    let executed_ops = match &obc_res {
        // Ok(res) if res.ksplang_interpreted == 0 => return,
        Ok(res) => res.ksplang_interpreted,
        Err(_) => 0,
    };

    let mut cfg_stack = input.clone();
    let cfg_res = cfg_interpreter::interpret_cfg(&g, &mut cfg_stack, true);

    let vm_ops_limit = if obc_res.is_ok() { executed_ops } else { 500_000 };
    let max_stack = cmp::max(1000, obc_stack.len() + 100);

    // use stop_after to get success, not error result
    let vm_options = VMOptions::new(&input, max_stack, &PI_TEST_VALUES, u64::MAX, vm_ops_limit);
    let vm_res = vm::run(&ops, vm_options);

    if cfg!(debug_assertions) {
        println!("    * CFG result: {cfg_res:?} stack: {} {cfg_stack:?}", cfg_stack.len());
        println!("    * OBC result: {obc_res:?} stack: {} {obc_stack:?}", obc_stack.len());
        println!("    * Interpreter result: {:?}", vm_res);
    }

    match (obc_res, cfg_res, vm_res) {
        (Ok(obc_run), Ok(cfg_run), Ok(vm_run)) => {
            assert_eq!(cfg_run.executed_ksplang, obc_run.ksplang_interpreted, "CFG vs Osmibyte op count mismatch");

            assert_eq!(cfg_stack, vm_run.stack, "CFG vs VM stack mismatch. Program: {:?}, Input: {:?}", ops, input);
            assert_eq!(obc_stack, vm_run.stack, "Osmibyte vs VM stack mismatch. Program: {:?}, Input: {:?}", ops, input);
        },
        (Err(obc_err), Err(cfg_err), Err(vm_err)) => {
            if let RunError::InstructionFailed { error: vm_op_err, .. } = vm_err {
                assert_eq!(cfg_err, vm_op_err, "CFG vs VM error mismatch");
                assert_eq!(obc_err, vm_op_err, "Osmibyte vs VM error mismatch");
            }
        },
        (Ok(obc_run), Err(e), _) => {
             if obc_run.exit_point == ExitPointId::Start || (obc_run.ksplang_interpreted == 0 && obc_stack == input) {
                return;
             }
             panic!("Osmibyte OK, CFG Err: {:?}", e)
        },
        (Err(e), Ok(_), _) => panic!("Osmibyte Err: {:?}, CFG OK", e),
        (Ok(obc_run), _, Err(e)) => {
             if obc_run.exit_point == ExitPointId::Start || (obc_run.ksplang_interpreted == 0 && obc_stack == input) {
                return;
             }
             panic!("Osmibyte OK, VM Err: {:?}", e)
        },
        (Err(e), _, Ok(_)) => panic!("Osmibyte Err: {:?}, VM OK", e),
    }
}

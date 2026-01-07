use std::{cmp, fmt};

use crate::compiler::{
    cfg::GraphBuilder, cfg_interpreter, osmibytecode::OsmibytecodeBlock, osmibytecode_vm::{self, ExitPointId, RegFile}, precompiler::{NoTrace, Precompiler}
};
use crate::vm::{self, VMOptions, RunError};
use crate::ops::Op;

const PI_TEST_VALUES: [i8; 42] = [
    3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5,
    0, 2, 8, 8, 4, 1, 9, 7, 1, 6,
];

#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct ReproData {
    ops: Vec<Op>,
    input: Vec<i64>,
    // trace_input: Vec<i64>,
    const_input: Vec<i64>,
    soften_limits: bool,
    max_interpret: Option<usize>,
}

impl ReproData {
    pub fn new(ops: impl Into<Vec<Op>>, input: impl Into<Vec<i64>>) -> Self {
        Self {
            ops: ops.into(),
            input: input.into(),
            ..Default::default()
        }
    }

    pub fn with_constin(mut self, const_input: impl Into<Vec<i64>>) -> Self {
        self.const_input = const_input.into();
        self
    }

    pub fn with_soften_limits(mut self, soften_limits: bool) -> Self {
        self.soften_limits = soften_limits;
        self
    }

    pub fn with_max_interpret(mut self, max_interpret: usize) -> Self {
        self.max_interpret = Some(max_interpret);
        self
    }

    pub fn verify(self) -> (GraphBuilder, OsmibytecodeBlock) {
        verify_repro_core(self)
    }
}

impl fmt::Display for ReproData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let def = Self::default();
        writeln!(f, "#[test]")?;
        writeln!(f, "fn fuzz_repro() {{")?;
        write!(f,   "    let ops = vec![ ")?;
        for (i, op) in self.ops.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{:?}", op)?;
        }
        writeln!(f, " ];")?;
        if self.soften_limits == def.soften_limits && self.max_interpret.is_none() {
            if self.const_input.is_empty() {
                writeln!(f, "    verify_repro(ops, vec!{:?});", self.input)?;
            } else {
                writeln!(f, "    verify_repro_const(ops, vec!{:?}, vec!{:?});", self.input, self.const_input)?;
            }
        } else {
            writeln!(f, "    let r = ReproData::new(ops, {:?})", self.input)?;

            if !self.const_input.is_empty() {
                writeln!(f, "        .with_constin({:?})", self.const_input)?;
            }
            write!(f, "        ")?;
            if self.soften_limits != def.soften_limits {
                write!(f, ".with_soften_limits({:?})", self.soften_limits)?;
            }
            if self.max_interpret != def.max_interpret {
                write!(f, ".with_max_interpret({:?})", self.max_interpret)?;
            }
            writeln!(f, ";")?;
            writeln!(f, "    r.verify();")?;
        }
        writeln!(f, "}}")
    }
}

// pub fn verify_repro(ops: Vec<Op>, input: Vec<i64>) -> (GraphBuilder, OsmibytecodeBlock) {
// }
pub fn verify_repro(ops: Vec<Op>, input: Vec<i64>) -> (GraphBuilder, OsmibytecodeBlock) {
    let r = ReproData::new(ops, input);
    r.verify()
}
pub fn verify_repro_const(ops: Vec<Op>, input: Vec<i64>, constin: Vec<i64>) -> (GraphBuilder, OsmibytecodeBlock) {
    let r = ReproData::new(ops, input).with_constin(constin);
    r.verify()
}
fn verify_repro_core(r: ReproData) -> (GraphBuilder, OsmibytecodeBlock) {
    let full_input = r.input.iter().copied().chain(r.const_input.iter().copied()).collect::<Vec<i64>>();

    let mut g = GraphBuilder::new(0);
    for c in &r.const_input {
        let c = g.store_constant(*c);
        g.stack.push(c);
    }
    if r.const_input.len() > 0 {
        g.push_checkpoint();
    }
    let max_interpret = r.max_interpret.unwrap_or(r.ops.len() + 2000);
    let mut precompiler = Precompiler::new(&r.ops, full_input.len(), false, 0, max_interpret, true, None, g, NoTrace());
    precompiler.bb_limit = 32;
    precompiler.instr_limit = 500;
    precompiler.soften_limits = r.soften_limits;
    precompiler.interpret();
    let g = precompiler.g;
    // if is_trivial(&g) { return; }
    println!("{g}");

    let obc_block = OsmibytecodeBlock::from_cfg(&g);
    println!("{obc_block}");

    let mut obc_stack = r.input.clone();
    let mut regs = RegFile::new();
    let obc_res = osmibytecode_vm::interpret_block::<true>(&obc_block, &mut obc_stack, &mut regs);
    if obc_res.as_ref().is_ok_and(|r| r.exit_point == ExitPointId::Start) {
        obc_stack.extend_from_slice(&r.const_input);
    }

    let executed_ops = match &obc_res {
        // Ok(res) if res.ksplang_interpreted == 0 => return,
        Ok(res) => res.ksplang_interpreted,
        Err(_) => 0,
    };

    let mut cfg_stack = r.input.clone();
    let cfg_res = cfg_interpreter::interpret_cfg(&g, &mut cfg_stack, true);

    let vm_ops_limit = if obc_res.is_ok() { executed_ops } else { 500_000 };
    let max_stack = cmp::max(1000, obc_stack.len() + 100);

    // use stop_after to get success, not error result
    let vm_options = VMOptions::new(&full_input, max_stack, &PI_TEST_VALUES, u64::MAX, vm_ops_limit);
    let vm_res = vm::run(&r.ops, vm_options);

    if cfg!(debug_assertions) && g.conf.should_log(1) {
        println!("{r}");
        println!("    * CFG result: {cfg_res:?} stack: {} {cfg_stack:?}", cfg_stack.len());
        println!("    * OBC result: {obc_res:?} stack: {} {obc_stack:?}", obc_stack.len());
        println!("    * Interpreter result: {:?}", vm_res);
    }

    match (obc_res, cfg_res, vm_res) {
        (Ok(obc_run), Ok(cfg_run), Ok(vm_run)) => {
            // if obc_run.exit_point == ExitPointId::Start || (obc_run.ksplang_interpreted == 0 && obc_stack == input) {
            //    return (g, obc_block)
            // }

            assert_eq!(cfg_stack, vm_run.stack, "CFG vs VM stack mismatch");
            assert_eq!(cfg_run.executed_ksplang, obc_run.ksplang_interpreted, "CFG vs Osmibyte op count mismatch");
            assert_eq!(obc_stack, vm_run.stack, "Osmibyte vs VM stack mismatch.");
        },
        (Err(obc_err), Err(cfg_err), Err(vm_err)) => {
            if let RunError::InstructionFailed { error: vm_op_err, .. } = vm_err {
                assert_eq!(cfg_err, vm_op_err, "CFG vs VM error mismatch");
                assert_eq!(obc_err, vm_op_err, "Osmibyte vs VM error mismatch");
            }
        },
        (Ok(obc_run), Err(e), _) => {
             if obc_run.exit_point == ExitPointId::Start || (obc_run.ksplang_interpreted == 0 && obc_stack == r.input) {
                return (g, obc_block)
             }
             panic!("Osmibyte OK, CFG Err: {:?}", e)
        },
        (Err(e), Ok(_), _) => panic!("Osmibyte Err: {:?}, CFG OK", e),
        (Ok(obc_run), _, Err(e)) => {
             if obc_run.exit_point == ExitPointId::Start || (obc_run.ksplang_interpreted == 0 && obc_stack == r.input) {
                return (g, obc_block)
             }
             panic!("Osmibyte OK, VM Err: {:?}", e)
        },
        (Err(e), _, Ok(_)) => panic!("Osmibyte Err: {:?}, VM OK", e),
    }

    return (g, obc_block)
}

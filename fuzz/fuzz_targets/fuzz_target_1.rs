#![no_main]

use std::fmt;

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;
use ksplang::{compiler::test_utils::verify_repro, ops::Op};

const ALLOWED_OPS: &[Op] = &[
    Op::Praise,
    Op::Pop,
    Op::Pop2,
    Op::Max,
    Op::LSwap,
    Op::Roll,
    Op::Swap,
    Op::Increment,
    Op::Universal,
    Op::Remainder,
    Op::Modulo,
    Op::TetrationNumIters,
    Op::TetrationItersNum,
    Op::Median,
    Op::DigitSum,
    Op::LenSum,
    Op::Bitshift,
    Op::And,
    Op::Sum,
    Op::Gcd2,
    Op::GcdN,
    Op::Qeq,
    Op::Funkcia,
    Op::BulkXor,
    Op::BranchIfZero,
    Op::Call,
    Op::Goto,
    Op::Jump,
    // Op::FF,
    // Op::KPi,
    // Op::Rev,
    // Op::Sleep,
    // Op::Deez,
];

struct ArbitraryOp(Op);

impl<'a> Arbitrary<'a> for ArbitraryOp {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let idx = u.choose_index(ALLOWED_OPS.len())?;
        Ok(ArbitraryOp(ALLOWED_OPS[idx]))
    }
}

impl fmt::Debug for ArbitraryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Debug::fmt(&self.0, f) }
}

#[derive(Arbitrary)]
struct FuzzInput {
    program: Vec<ArbitraryOp>,
    input: Vec<i64>,
}

impl std::fmt::Debug for FuzzInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "FuzzInput {{")?;
        writeln!(f, "    program: {:?},", self.program)?;
        writeln!(f, "    input: {:?},", self.input)?;
        write!(f, "}}")?;
        writeln!(f, "Reproduce with:")?;
        writeln!(f, "#[test]")?;
        writeln!(f, "fn fuzz_repro() {{")?;
        writeln!(f, "    let ops = vec![")?;
        for op in &self.program {
            writeln!(f, "        {:?},", op.0)?;
        }
        writeln!(f, "    ];")?;
        writeln!(f, "    verify_repro(ops, vec!{:?});", self.input)?;
        writeln!(f, "}}")?;
        Ok(())
    }
}

fuzz_target!(|data: FuzzInput| {
    let FuzzInput { program, input } = data;
    let ops: Vec<Op> = program.iter().map(|op| op.0).collect();

    if ops.is_empty() || input.is_empty() { return } // uninteresting edge case

    verify_repro(ops, input);
});


#![no_main]

use std::fmt;

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;
use ksplang::{compiler::test_utils::ReproData, ops::Op};

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

#[derive(Arbitrary)]
struct FuzzInput {
    program: Vec<ArbitraryOp>,
    input: Vec<i64>,
}

impl std::fmt::Debug for FuzzInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(&to_repro(&self), f)
    }
}

fn to_repro(i: &FuzzInput) -> ReproData {
    ReproData::new(i.program.iter().map(|op| op.0).collect::<Vec<_>>(), i.input.clone())
}

fuzz_target!(|data: FuzzInput| {
    let r = to_repro(&data);

    r.verify();
});


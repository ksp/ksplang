#![no_main]

use std::fmt;

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;
use ksplang::{compiler::test_utils::ReproData};
use ksplang_fuzz::{self, ArbitraryOp};


#[derive(Arbitrary)]
struct FuzzInput {
    program: Vec<ArbitraryOp>,
    const_input: Vec<i64>,
    input: Vec<i64>,
}

impl std::fmt::Debug for FuzzInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(&to_repro(&self), f)
    }
}

fn to_repro(i: &FuzzInput) -> ReproData {
    ReproData::new(i.program.iter().map(|op| op.0).collect::<Vec<_>>(), i.input.clone())
        .with_constin(i.const_input.clone())
}

fuzz_target!(|data: FuzzInput| {
    if data.program.is_empty() || data.input.is_empty() { return }

    let r = to_repro(&data);

    r.verify();
});


use thiserror::Error;

use crate::ops::Op;

#[derive(Debug, Error)]
pub enum ParserError {
    #[error("Unknown operation: `{0}`.")]
    UnknownOperation(String),
}

pub fn parse_word(word: &str) -> Result<Op, ParserError> {
    assert!(!word.contains(|c: char| c.is_whitespace()));
    let op = match word.to_lowercase().as_ref() {
        // Note that while Op::Nop exists, it is not a part of the language.
        "praise" => Op::Praise,
        "pop" => Op::Pop,
        "¬" => Op::Pop2,
        "pop2" => Op::Pop2,
        "max" => Op::Max,
        "l-swap" => Op::LSwap,
        "lroll" => Op::Roll,
        "-ff" => Op::FF,
        "swap" => Op::Swap,
        "kpi" => Op::KPi,
        "++" => Op::Increment,
        "u" => Op::Universal,
        "rem" => Op::Remainder,
        "%" => Op::Modulo,
        "tetr" => Op::TetrationNumIters,
        "^^" => Op::TetrationItersNum,
        "m" => Op::Median,
        "cs" => Op::DigitSum,
        "lensum" => Op::LenSum,
        "bitshift" => Op::Bitshift,
        // "Σ".to_lowercase() == "σ".
        "σ" => Op::Sum,
        "sum" => Op::Sum,
        "d" => Op::GcdN,
        "gcd" => Op::Gcd2,
        "qeq" => Op::Qeq,
        "funkcia" => Op::Funkcia,
        "bulkxor" => Op::BulkXor,
        "brz" => Op::BranchIfZero,
        "call" => Op::Call,
        "goto" => Op::Goto,
        "j" => Op::Jump,
        "rev" => Op::Rev,
        "spanek" => Op::Sleep,
        "deez" => Op::Deez,
        _ => return Err(ParserError::UnknownOperation(word.to_string())),
    };

    return Ok(op);
}

pub fn parse_program(str: &str) -> Result<Vec<Op>, ParserError> {
    let mut ops = Vec::new();
    for word in str.split_whitespace() {
        ops.push(parse_word(word)?);
    }
    Ok(ops)
}
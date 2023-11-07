use thiserror::Error;

use crate::ops::Op;

#[derive(Debug, Error)]
pub enum ParserError {
    #[error("Unknown operation: `{0}`.")]
    UnknownOperation(String),
}

pub fn parse(str: &str) -> Result<Vec<Op>, ParserError> {
    let mut ops = Vec::new();
    for word in str.split_whitespace() {
        match word.to_lowercase().as_ref() {
            "praise" => ops.push(Op::Praise),
            "pop" => ops.push(Op::Pop),
            "¬" => ops.push(Op::Pop2),
            "pop2" => ops.push(Op::Pop2),
            "max" => ops.push(Op::Max),
            "l-swap" => ops.push(Op::LSwap),
            "lroll" => ops.push(Op::LRoll),
            "-ff" => ops.push(Op::FF),
            "swap" => ops.push(Op::Swap),
            "kpi" => ops.push(Op::KPi),
            "++" => ops.push(Op::Increment),
            "u" => ops.push(Op::Universal),
            "rem" => ops.push(Op::Remainder),
            "^^" => ops.push(Op::Tetration),
            "m" => ops.push(Op::Median),
            "cs" => ops.push(Op::DigitSum),
            "lensum" => ops.push(Op::LenSum),
            "bitshift" => ops.push(Op::Bitshift),
            "Σ" => ops.push(Op::Sum),
            "sum" => ops.push(Op::Sum),
            "d" => ops.push(Op::GcdN),
            "gcd" => ops.push(Op::Gcd2),
            // TODO: Name these instructions:
            //"?" => ops.push(Op::QuadraticEquationSolver),
            //"?" => ops.push(Op::PrimesThingy),
            //"?" => ops.push(Op::BulkPairwiseOfSomethingBinary),
            "brz" => ops.push(Op::BranchIfZero),
            // TODO: Does this take values from the stack?
            //"call" => ops.push(Op::Call),
            "goto" => ops.push(Op::Goto),
            "j" => ops.push(Op::Jump),
            "rev" => ops.push(Op::Rev),
            "spanek" => ops.push(Op::Sleep),
            "deez" => ops.push(Op::Deez),
            _ => return Err(ParserError::UnknownOperation(word.to_string())),
        }
    }
    Ok(ops)
}
use thiserror::Error;

use crate::ops::Op;

#[derive(Debug, Error)]
pub enum ParserError {
    #[error("Unknown operation: `{0}`.")]
    UnknownOperation(char),
}

pub fn parse(str: &str) -> Result<Vec<Op>, ParserError> {
    let mut ops = Vec::new();
    for char in str.chars() {
        match char {
            c if c.is_whitespace() => (),
            '0' => ops.push(Op::Const0),
            '1' => ops.push(Op::Const1),
            '2' => ops.push(Op::Const2),
            '3' => ops.push(Op::Const3),
            '4' => ops.push(Op::Const4),
            '5' => ops.push(Op::Const5),
            '6' => ops.push(Op::Const6),
            '7' => ops.push(Op::Const7),
            '8' => ops.push(Op::Const8),
            '9' => ops.push(Op::Const9),
            'a' => ops.push(Op::Add),
            'c' => ops.push(Op::Copy),
            'd' => ops.push(Op::Dup),
            'e' => ops.push(Op::Equal),
            'g' => ops.push(Op::Greater),
            'k' => ops.push(Op::Count),
            'l' => ops.push(Op::Less),
            'm' => ops.push(Op::Mul),
            'o' => ops.push(Op::Overwrite),
            'p' => ops.push(Op::Pop),
            'q' => ops.push(Op::Quotient),
            'r' => ops.push(Op::Remainder),
            's' => ops.push(Op::Subtract),
            'x' => ops.push(Op::Exchange),
            _ => return Err(ParserError::UnknownOperation(char)),
        }
    }
    Ok(ops)
}
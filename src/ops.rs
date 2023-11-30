use std::fmt::{Display, Formatter};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op {
    Nop,
    Praise,
    Pop,
    Pop2,
    Max,
    LSwap,
    Roll,
    FF,
    Swap,
    KPi,
    Increment,
    Universal,
    Remainder,
    Modulo,
    TetrationNumIters,
    TetrationItersNum,
    Median,
    DigitSum,
    LenSum,
    Bitshift,
    Sum,
    Gcd2,
    GcdN,
    Qeq,
    Funkcia,
    BulkXor,
    BranchIfZero,
    Call,
    Goto,
    Jump,
    Rev,
    Sleep,
    Deez,
    // TODO: not/shift/or/and/eval/ding
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Op::Nop => "nop",
            Op::Praise => "praise",
            Op::Pop => "pop",
            Op::Pop2 => "pop2",
            Op::Max => "max",
            Op::LSwap => "L-swap",
            Op::Roll => "lroll",
            Op::FF => "-ff",
            Op::Swap => "swap",
            Op::KPi => "kPi",
            Op::Increment => "++",
            Op::Universal => "u",
            Op::Remainder => "REM",
            Op::Modulo => "%",
            Op::TetrationNumIters => "tetr",
            Op::TetrationItersNum => "^^",
            Op::Median => "m",
            Op::DigitSum => "CS",
            Op::LenSum => "lensum",
            Op::Bitshift => "bitshift",
            Op::Sum => "Σ",
            Op::Gcd2 => "gcd",
            Op::GcdN => "d",
            Op::Qeq => "qeq",
            Op::Funkcia => "funkcia",
            Op::BulkXor => "bulkxor",
            Op::BranchIfZero => "BRZ",
            Op::Call => "call",
            Op::Goto => "GOTO",
            Op::Jump => "j",
            Op::Rev => "rev",
            Op::Sleep => "SPANEK",
            Op::Deez => "deez"
        };
        write!(f, "{}", name)
    }
}
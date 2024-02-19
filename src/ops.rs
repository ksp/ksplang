//! ksplang instructions.
use std::fmt::{Display, Formatter};

/// A ksplang instruction.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op {
    /// Not a real ksplang instruction, only used internally for tests.
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
    And,
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
}

impl Op {
    /// Returns the instruction with the given id, or `None` if the id is invalid.
    ///
    /// # Example
    /// ```
    /// use ksplang::ops::Op;
    /// assert_eq!(Op::by_id(0), Some(Op::Praise));
    /// assert_eq!(Op::by_id(33), None);
    /// ```
    pub const fn by_id(id: usize) -> Option<Op> {
        match id {
            0 => Some(Op::Praise),
            1 => Some(Op::Pop),
            2 => Some(Op::Pop2),
            3 => Some(Op::Max),
            4 => Some(Op::LSwap),
            5 => Some(Op::Roll),
            6 => Some(Op::FF),
            7 => Some(Op::Swap),
            8 => Some(Op::KPi),
            9 => Some(Op::Increment),
            10 => Some(Op::Universal),
            11 => Some(Op::Remainder),
            12 => Some(Op::Modulo),
            13 => Some(Op::TetrationNumIters),
            14 => Some(Op::TetrationItersNum),
            15 => Some(Op::Median),
            16 => Some(Op::DigitSum),
            17 => Some(Op::LenSum),
            18 => Some(Op::Bitshift),
            19 => Some(Op::And),
            20 => Some(Op::Sum),
            21 => Some(Op::Gcd2),
            22 => Some(Op::GcdN),
            23 => Some(Op::Qeq),
            24 => Some(Op::Funkcia),
            25 => Some(Op::BulkXor),
            26 => Some(Op::BranchIfZero),
            27 => Some(Op::Call),
            28 => Some(Op::Goto),
            29 => Some(Op::Jump),
            30 => Some(Op::Rev),
            31 => Some(Op::Sleep),
            32 => Some(Op::Deez),
            _ => None,
        }
    }
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
            Op::And => "And",
            Op::Sum => "sum",
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
            Op::Deez => "deez",
        };
        write!(f, "{}", name)
    }
}

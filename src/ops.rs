#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op {
    Const0,
    Const1,
    Const2,
    Const3,
    Const4,
    Const5,
    Const6,
    Const7,
    Const8,
    Const9,
    Add,
    Copy,
    Dup,
    Equal,
    Greater,
    Count,
    Less,
    Mul,
    Overwrite,
    Pop,
    Quotient,
    Remainder,
    Subtract,
    Exchange,
    Nop,
}

impl Op {
    /// (vals required before; resulting stack diff)
    const fn stack_len_diff(&self) -> (usize, isize) {
        match self {
            Op::Const0 => (0, 1),
            Op::Const1 => (0, 1),
            Op::Const2 => (0, 1),
            Op::Const3 => (0, 1),
            Op::Const4 => (0, 1),
            Op::Const5 => (0, 1),
            Op::Const6 => (0, 1),
            Op::Const7 => (0, 1),
            Op::Const8 => (0, 1),
            Op::Const9 => (0, 1),
            Op::Add => (2, -1),
            Op::Copy => (1, 0),
            Op::Dup => (1, 1),
            Op::Equal => (2, -1),
            Op::Greater => (2, -1),
            Op::Count => (0, 1),
            Op::Less => (2, -1),
            Op::Mul => (2, -1),
            Op::Overwrite => (2, -2), // May require any amount of vals before, needs checking runtime
            Op::Pop => (1, -1),
            Op::Quotient => (2, -1),
            Op::Remainder => (2, -1),
            Op::Subtract => (2, -1),
            Op::Exchange => (2, 0),
            Op::Nop => (0, 0),
        }
    }
}

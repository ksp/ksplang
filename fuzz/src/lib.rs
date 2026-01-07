use arbitrary::Arbitrary;
use ksplang::ops::Op;

pub const ALLOWED_OPS: &[Op] = &[
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
];

pub struct ArbitraryOp(pub Op);

impl<'a> Arbitrary<'a> for ArbitraryOp {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let idx = u.choose_index(ALLOWED_OPS.len())?;
        Ok(ArbitraryOp(ALLOWED_OPS[idx]))
    }
}

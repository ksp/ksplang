#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Op {
    Praise,
    Pop,
    Pop2,
    Max,
    LSwap,
    LRoll,
    FF,
    Swap,
    KPi,
    Increment,
    Universal,
    Remainder,
    // TODO: Modulo?
    Tetration,
    // TODO: Second tetration?
    Median,
    DigitSum,
    LenSum,
    Bitshift,
    Sum,
    Gcd2,
    GcdN,
    QuadraticEquationSolver,
    PrimesThingy,
    BulkPairwiseOfSomethingBinary,
    BranchIfZero,
    Call, // TODO: Does it have a source code argument?
    Goto,
    Jump,
    Rev,
    Sleep,
    Deez,
    // TODO: not/shift/or/and/eval/ding
}
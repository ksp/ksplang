use std::iter::Product;

use crate::{compiler::{cfg::{GraphBuilder, OptInstr}, precompiler::Precompiler}, parser};

fn precompile_ops(ops: &[crate::ops::Op], terminate_at: Option<usize>) -> Precompiler<'_> {
    let g = GraphBuilder::new();
    let mut precompiler = Precompiler::new(ops, 1000, false, 0, 100_000, terminate_at, g);
    precompiler.interpret();
    precompiler
}

fn precompile(ksplang: &str, terminate_at: Option<usize>) -> GraphBuilder {
    let parsed = parser::parse_program(ksplang).unwrap();
    let g = GraphBuilder::new();
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, terminate_at, g);
    precompiler.interpret();
    precompiler.g
}

#[test]
fn test_constant_zero() {
    // let g = precompile("CS CS lensum CS funkcia", None);
    // let g = precompile("CS CS lensum CS funkcia ++ praise CS d pop funkcia ++ REM", None);
    // let g = precompile("CS CS lensum ++ CS lensum CS ++ funkcia CS ++ funkcia", None);
    // TODO:
    //  * fusing: const + (const + a)
    //  * median(a, 2) = a / 2 + 1
    //  * a << 1 = a * 2
    //  * a * 2 / 2 = a
    //  * a / 2 * 2 = a & ~1
    let g = precompile("CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum ++ CS lensum CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u", None);

    for bb in &g.blocks {
        println!("{}", bb);
    }
    println!("Stack: {:?}", g.stack.stack);
    assert_eq!(g.stack.stack_depth, 1);
    assert_eq!(g.stack.stack_position, -1);
    assert_eq!(g.get_constant(g.stack.peek().unwrap()), Some(0));
    assert_eq!(g.current_block_ref().instructions.len(), 2);
}

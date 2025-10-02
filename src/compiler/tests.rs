use std::ops::RangeInclusive;

use crate::{compiler::{cfg::GraphBuilder, precompiler::{NoTrace, Precompiler}, utils::FULL_RANGE}, parser};

fn precompile(ksplang: &str, terminate_at: Option<usize>) -> GraphBuilder {
    let parsed = parser::parse_program(ksplang).unwrap();
    let g = GraphBuilder::new();
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, terminate_at, g, NoTrace());
    precompiler.interpret();
    precompiler.g
}

fn test_constant(prog: &str, c: i64) {
    let g = precompile(prog, None);

    for bb in &g.blocks {
        println!("{}", bb);
    }
    println!("Stack: {}", g.fmt_stack());
    assert_eq!(g.stack.stack_depth, 1);
    assert_eq!(g.stack.stack_position, -1);
    assert_eq!(g.get_constant(g.stack.peek().unwrap()), Some(c));
    assert_eq!(g.current_block_ref().instructions.len(), 2);
}

#[test]
fn test_constant_0() {
    test_constant("CS CS lensum CS funkcia", 0);
}
#[test]
fn test_constant_n4611686018427387904() {
    test_constant("CS CS lensum ++ CS lensum ++ CS bitshift CS ++ bitshift CS ++ CS funkcia bitshift", -4611686018427387904);
}
#[test]
fn test_constant_n1() {
    test_constant("CS CS lensum ++ CS CS CS % qeq", -1);
}
#[test]
fn test_constant_n929() {
    test_constant("CS CS lensum ++ CS lensum CS ++ tetr ++ ++ CS CS lensum ++ ++ bitshift ++ CS CS lensum CS funkcia ++ CS CS % qeq", -929);
}
#[test]
fn test_constant_2() {
    test_constant("CS CS lensum ++ CS lensum", 2);
}
#[test]
fn test_constant_35() {
    test_constant("CS CS lensum ++ CS lensum CS ++ tetr ++ CS funkcia", 35);
}
#[test]
fn test_constant_36() {
    test_constant("CS CS lensum CS funkcia ++ praise qeq qeq pop funkcia REM REM", 36);
}
#[test]
fn test_constant_40() {
    test_constant("CS CS lensum CS funkcia ++ praise CS d pop funkcia ++ REM", 40);
}
#[test]
fn test_constant_65() {
    test_constant("CS CS lensum CS funkcia ++ praise qeq qeq qeq And", 65);
}
#[test]
fn test_constant_102() {
    test_constant("CS CS lensum CS funkcia ++ praise qeq qeq gcd ++ funkcia REM pop2", 102);
}
#[test]
fn test_constant_7625597484987() {
    test_constant("CS CS ++ lensum CS lensum ++ CS tetr", 7625597484987);
}

fn test_dup(ksplang: &str, input_range: RangeInclusive<i64>) {
    let parsed = parser::parse_program(ksplang).unwrap();
    let mut g = GraphBuilder::new();
    let val = {
        let info = g.new_value();
        info.range = input_range.clone();
        info.id
    };
    g.stack.push(val);
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, None, g, NoTrace());
    precompiler.interpret();
    let g = precompiler.g;

    if *input_range.start() == *input_range.end() {
        let c = g.constant_lookup.get(input_range.start()).unwrap();
        assert_eq!(g.stack.stack, vec![*c, *c]);
    } else {
        assert_eq!(g.stack.stack, vec![val, val]);
    }
    assert_eq!(1, g.current_block_ref().instructions.len());
}

// Duplikace ze vzoráku KSP
const VZORAKOVA_DUP: &str = "CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum ++ CS lensum CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u";
const SEJSELOVA_DUP: &str = "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2";
#[test]
fn test_dup1() {
    test_dup(VZORAKOVA_DUP, FULL_RANGE);
}

#[test]
fn test_dup2() {
    test_dup(SEJSELOVA_DUP, FULL_RANGE);
}

#[test]
fn test_dup1_limited_ranges() {
    test_dup(VZORAKOVA_DUP, 0..=1000000);
    test_dup(VZORAKOVA_DUP, -1..=1);
    test_dup(VZORAKOVA_DUP, 1345432..=1345432);
    test_dup(VZORAKOVA_DUP, i64::MIN..=i64::MIN+1);
}

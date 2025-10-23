use std::{ops::RangeInclusive};

use rand::{Rng, SeedableRng};

use crate::{compiler::{cfg::GraphBuilder, ops::{OptOp, ValueId}, precompiler::{NoTrace, Precompiler}, utils::FULL_RANGE}, parser, vm::{NoStats, RunError, RunResult, VMOptions}};

fn precompile(ksplang: &str, terminate_at: Option<usize>, initial_values: &[RangeInclusive<i64>]) -> (GraphBuilder, Vec<ValueId>) {
    let parsed = parser::parse_program(ksplang).unwrap();
    let mut g = GraphBuilder::new(0);
    for r in initial_values {
        let val = {
            let info = g.new_value();
            info.range = r.clone();
            info.id
        };
        g.stack.push(val);
    }
    let vals = g.stack.stack.clone();
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, terminate_at, g, NoTrace());
    precompiler.interpret();
    (precompiler.g, vals)
}

fn test_constant(prog: &str, c: i64) {
    let g = precompile(prog, None, &[]).0;

    for bb in &g.blocks {
        println!("{}", bb);
    }
    println!("Stack: {}", g.fmt_stack());
    assert_eq!(g.stack.stack_depth, 1);
    assert_eq!(g.stack.stack_position(), 1);
    assert_eq!(g.get_constant(g.stack.peek().unwrap()), Some(c));
    assert_eq!(g.current_block_ref().instructions.len(), 2);
}

#[test]
fn test_constant_0() {
    test_constant("CS CS lensum CS funkcia", 0);
}
#[test]
fn test_constant_0b() {
    test_constant("CS CS lensum ++ CS %", 0);
}
#[test]
fn test_constant_0c() {
    test_constant("CS CS CS CS funkcia pop2 pop2", 0);
}
#[test]
fn test_constant_0d() {
    test_constant("CS CS CS ++ CS CS % pop2 pop2 pop2", 0);
}
// #[test]
// fn test_constant_0e() {
//     test_constant("CS CS ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ ++ bitshift", 0);
// }
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
    let mut g = GraphBuilder::new(0);
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

fn test_neg(prog: &str) {
    let (g, vals) = precompile(prog, None, &[(FULL_RANGE)]);
    assert_eq!(1, g.stack.stack.len());
    let result_val = g.stack.stack[0];
    let result_info = &g.values[&result_val];
    assert_eq!((-i64::MAX)..=i64::MAX, result_info.range);
    let defined_at = g.get_instruction_(result_info.assigned_at.unwrap());
    assert_eq!(OptOp::Sub, defined_at.op);
    assert_eq!([ValueId::C_ZERO, vals[0]], defined_at.inputs[..]);
    assert_eq!(2, g.current_block_ref().instructions.len());
}

#[test]
fn test_neg_a() { test_neg("CS CS lensum CS funkcia ++ CS CS % qeq"); }

#[test]
fn test_neg_b() {
    test_neg("
        CS CS lensum CS funkcia ++
        CS CS lensum CS funkcia ++ praise qeq qeq pop bitshift ++ REM REM
        bitshift
        CS CS lensum ++ CS lensum ++ ++ ++
        u
        CS CS lensum ++ CS lensum
        u
    ");
}

// Duplikace ze vzoráku KSP
const VZORAKOVA_DUP: &str = "CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum ++ CS lensum CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u";
const SEJSELOVA_DUP: &str = "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2";
#[test]
fn test_dup1() {
    test_dup(VZORAKOVA_DUP, FULL_RANGE);
}
#[test]
fn test_dup1_trochu_jina() {
    test_dup("CS CS lensum CS funkcia ++ ++ m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum CS funkcia ++ ++ m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia ++ ++ CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u", FULL_RANGE);
}

#[test]
fn test_dup2() {
    test_dup(SEJSELOVA_DUP, i64::MIN..=0);
    test_dup(SEJSELOVA_DUP, 3..=i64::MAX);
    // test_dup(SEJSELOVA_DUP, FULL_RANGE); // TODO: support this
}

#[test]
fn test_dup2_twice() {
    test_dup(&format!("{SEJSELOVA_DUP} ++ {SEJSELOVA_DUP}"), FULL_RANGE);
    // test_dup(SEJSELOVA_DUP, FULL_RANGE); // TODO: support this
}

#[test]
fn test_dup_32bit_vzorak() {
    const VZORAK_32BIT_DUP: &str = "
        CS CS lensum ++ CS lensum CS bitshift CS ++ ++ bitshift CS bitshift
        CS CS lensum CS funkcia
        u

        CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia bitshift pop2 pop2 pop2
        CS CS lensum ++ CS lensum ++
        m
        pop2 pop2

        CS CS lensum ++ CS CS CS % qeq CS ++ ++ bitshift CS ++ ++ bitshift CS bitshift
        CS CS lensum CS funkcia
        u

        CS CS lensum CS funkcia ++
        CS CS lensum ++ CS lensum
        lroll

        CS CS lensum ++ CS CS CS % qeq CS ++ ++ bitshift CS ++ ++ bitshift CS bitshift
        CS CS lensum CS funkcia
        u
    ";
    test_dup(VZORAK_32BIT_DUP, -2147483648..=2147483648);
    // test_dup(VZORAK_32BIT_DUP, FULL_RANGE);
}

#[test]
fn test_dup1_limited_ranges() {
    test_dup(VZORAKOVA_DUP, 0..=1000000);
    test_dup(VZORAKOVA_DUP, -1..=1);
    test_dup(VZORAKOVA_DUP, 1345432..=1345432);
    test_dup(VZORAKOVA_DUP, i64::MIN..=i64::MIN + 1);
}

const PI_TEST_VALUES: [i8; 42] = [
    3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2, 6, 4, 3, 3, 8, 3, 2, 7, 9, 5,
    0, 2, 8, 8, 4, 1, 9, 7, 1, 6,
];

fn run_with_opt(initial_stack: &[i64], program: &str) -> Result<RunResult<NoStats>, RunError> {
    let ops = parser::parse_program(program).unwrap();
    let mut vm = crate::vm::OptimizingVM::new(ops, true);
    let options = VMOptions::new(initial_stack, usize::MAX, &PI_TEST_VALUES, u64::MAX, u64::MAX);
    vm.run(initial_stack.to_vec(), options)
}

const VZORAK_SEKVENCE: &str = include_str!("tests/sekvence.ksplang");

#[test]
fn test_sekvence_1() {
    let res = run_with_opt(&[42, 43, 100], VZORAK_SEKVENCE).unwrap();
    let expected: Vec<i64> = [42, 43].into_iter().chain((0..=100).rev()).collect();
    assert_eq!(res.stack, expected);
}

const VZORAK_SORT: &str = include_str!("tests/sort.ksplang");

#[test]
fn test_sort_1() {
    let res = run_with_opt(&[3, 4, -4, 1, 1, 5], VZORAK_SORT).unwrap();
    assert_eq!(res.stack, [-4, 1, 1, 3, 4]);
}

#[test]
fn test_sort_2() {
    let rng = rand::rngs::SmallRng::seed_from_u64(1);
    let mut input: Vec<i64> = rng.random_iter().take(30).collect();
    input.push(input.len() as i64);
    let res = run_with_opt(&input, VZORAK_SORT).unwrap();
    input.pop();
    input.sort();
    assert_eq!(res.stack, input);
}


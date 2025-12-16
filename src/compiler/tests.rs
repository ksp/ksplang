#![allow(dead_code)]
use std::ops::RangeInclusive;

use rand::{Rng, SeedableRng};

use crate::{compiler::{cfg::GraphBuilder, ops::{BlockId, OptOp, ValueId}, osmibytecode::{Condition, OsmibyteOp, OsmibytecodeBlock, RegId}, pattern::OptOptPattern, precompiler::{NoTrace, Precompiler}, utils::FULL_RANGE}, parser, vm::{ActualTracer, NoStats, RunError, RunResult, VMOptions, run_with_stats}};

const PUSH_0: &str = "CS CS lensum CS funkcia";
const PUSH_1: &str = "CS CS lensum CS funkcia ++";
const PUSH_2: &str = "CS CS lensum ++ CS lensum";
const PUSH_3: &str = "CS CS lensum ++ CS lensum ++";
const PUSH_4: &str = "CS CS lensum ++ CS lensum ++ ++";
const PUSH_5: &str = "CS CS lensum ++ CS lensum ++ ++ ++";
const PUSH_6: &str = "CS CS lensum ++ CS lensum CS ++ funkcia";
const PUSH_7: &str = "CS CS lensum ++ CS lensum CS ++ funkcia ++";
const PUSH_8: &str = "CS CS lensum ++ CS lensum CS bitshift";
const PUSH_NEG_1: &str = "CS CS lensum ++ CS CS CS % qeq";

fn precompile<const N: usize>(ksplang: &str, terminate_at: Option<usize>, initial_values: [RangeInclusive<i64>; N]) -> (GraphBuilder, [ValueId; N]) {
    let parsed = parser::parse_program(ksplang).unwrap();
    let mut g = GraphBuilder::new(0);
    for r in initial_values {
        let val = {
            let info = g.new_value();
            info.range = r.clone();
            info.id
        };
        g.stack.push(val);
        g.block_mut_(BlockId(0)).parameters.push(val);
    }
    let vals = g.stack.stack.clone();
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, true, terminate_at, g, NoTrace());
    precompiler.interpret();
    (precompiler.g, vals.try_into().unwrap())
}

fn test_constant(prog: &str, c: i64) {
    let g = precompile(prog, None, []).0;

    for bb in &g.blocks {
        println!("{}", bb);
    }
    println!("Stack: {}", g.fmt_stack());
    assert_eq!(g.stack.stack_depth, 1);
    assert_eq!(g.stack.stack_position(), 1);
    assert_eq!(g.get_constant(g.stack.peek().unwrap()), Some(c));
    assert_eq!(g.current_block_ref().instructions.len(), 3); // Pop + Checkpoint + DeoptAssert(false)
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
    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, true, None, g, NoTrace());
    precompiler.interpret();
    let g = precompiler.g;
    println!("DUP CFG: {g}");
    let ob = OsmibytecodeBlock::from_cfg(&g);
    println!("DUP OB:\n{}", ob);

    if *input_range.start() == *input_range.end() {
        let c = g.constant_lookup.get(input_range.start()).unwrap();
        assert_eq!(g.stack.stack, vec![*c, *c]);
    } else {
        assert_eq!(g.stack.stack, vec![val, val]);
    }
    assert_eq!(2, g.block_(BlockId(0)).instructions.len()); // Checkpoint + DeoptAssert
}

fn test_neg(prog: &str) {
    let (g, vals) = precompile(prog, None, [(FULL_RANGE)]);
    assert_eq!(1, g.stack.stack.len());
    let result_val = g.stack.stack[0];
    let result_info = &g.values[&result_val];
    assert_eq!((-i64::MAX)..=i64::MAX, result_info.range);
    let defined_at = g.get_instruction_(result_info.assigned_at.unwrap());
    assert_eq!(OptOp::Sub, defined_at.op);
    assert_eq!([ValueId::C_ZERO, vals[0]], defined_at.inputs[..]);
    assert_eq!(3, g.current_block_ref().instructions.len()); // Pop + Checkpoint + DeoptAssert


    let ob = OsmibytecodeBlock::from_cfg(&g);
    println!("{}", ob);
    let reg = RegId(0);
    assert_eq!(&ob.program[..], [
        OsmibyteOp::SubConst(reg, 0, reg),
        OsmibyteOp::Push(reg),
        OsmibyteOp::Done(g.blocks[0].ksplang_instr_count, g.blocks[0].ksplang_instr_count as i16)
    ]);
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

#[test]
fn sgn_sgn() {
    let sgn_sgn = format!("
        {PUSH_5} u
        {PUSH_5} u
    ");
    let (g, [val1]) = precompile(&sgn_sgn, None, [(FULL_RANGE)]);
    assert_eq!(1, g.stack.stack.len());
    let result_val = g.val_info(g.stack.stack[0]).unwrap();
    let defined_at = g.get_instruction_(result_val.assigned_at.unwrap());
    assert_eq!((&OptOp::Sgn, [val1].as_slice()), (&defined_at.op, &defined_at.inputs[..]));
    assert_eq!(3, g.current_block_ref().instructions.len()); // Sgn + Checkpoint + DeoptAssert
}


// Duplikace ze vzoráku KSP
const VZORAKOVA_DUP: &str = "CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum ++ CS lensum m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum ++ CS lensum CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u";
const ERIKOVA_DUP: &str = "CS CS lensum CS funkcia cs ++ ++ ++ m cs cs ++ gcd ++ max cs cs rem qeq cs cs cs ++ ++ qeq pop2 cs cs ++ gcd cs cs cs cs bitshift bitshift cs bitshift cs cs pop2 u bitshift cs cs gcd cs ++ lroll cs u cs cs ++ gcd ++ ++ m pop2 pop2";
const SEJSELOVA_DUP: &str =  "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2";
const SEJSELOVA2_DUP: &str = "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS CS ^^ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2";
// #[test]
// fn test_dup1a() {
//     test_dup(VZORAKOVA_DUP, FULL_RANGE);
// }
// #[test]
// fn test_dup1_trochu_jina() {
//     test_dup("CS CS lensum CS funkcia ++ ++ m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift CS CS lensum CS funkcia ++ ++ m CS CS lensum CS funkcia CS ++ CS qeq u CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia ++ ++ CS ++ ++ lroll m CS CS lensum CS funkcia ++ CS CS funkcia qeq CS CS lensum CS funkcia ++ bitshift pop2 CS CS lensum CS funkcia u ++ ++ ++ CS CS CS CS lensum CS funkcia CS ++ CS qeq u CS ++ CS lensum CS ++ ++ lroll CS funkcia u CS CS lensum CS funkcia ++ CS ++ ++ lroll CS CS lensum CS funkcia CS ++ CS qeq u CS CS funkcia u", FULL_RANGE);
// }

#[test]
fn test_dup2_s1() {
    test_dup(SEJSELOVA_DUP, i64::MIN..=0);
    test_dup(SEJSELOVA_DUP, 3..=i64::MAX);
    // test_dup(SEJSELOVA_DUP, FULL_RANGE); // TODO: support this
    // todo!()
}

#[test]
fn test_dup2_e() {
    test_dup(ERIKOVA_DUP, i64::MIN..=0);
    test_dup(ERIKOVA_DUP, 3..=i64::MAX);
    test_dup(ERIKOVA_DUP, FULL_RANGE);
}

#[test]
fn test_dup2_s2() {
    test_dup(SEJSELOVA2_DUP, i64::MIN..=0);
    test_dup(SEJSELOVA2_DUP, 3..=i64::MAX);
    test_dup(SEJSELOVA2_DUP, FULL_RANGE);
}

// #[test]
// fn test_dup2_twice() {
//     test_dup(&format!("{SEJSELOVA_DUP} ++ {SEJSELOVA_DUP}"), FULL_RANGE);
// }

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
    // test_dup(VZORAKOVA_DUP, -1..=1);
    test_dup(VZORAKOVA_DUP, 1345432..=1345432);
    test_dup(VZORAKOVA_DUP, -1345432..=-2);
    // test_dup(VZORAKOVA_DUP, i64::MIN..=i64::MIN + 1);
}

fn assert_pattern(g: &GraphBuilder, v: ValueId, p: OptOptPattern) {
    if p.try_match(g, &[v]).is_ok() {
        return
    }

    panic!("assert_pattern({v}, {p}) failed:\n{g}")
}

fn assert_size(g: &GraphBuilder, bb_count_range: RangeInclusive<usize>, i_count_range: RangeInclusive<usize>) {
    let bb_count = g.reachable_blocks().count();
    let i_count = g.reachable_blocks().map(|b| b.instructions.len()).sum();
    if bb_count_range.contains(&bb_count) && i_count_range.contains(&i_count) {
        return
    }

    panic!("assert_size failed:
        i_count: {i_count} should be in {i_count_range:?}
        bb_count: {bb_count} should be in {bb_count_range:?}
        CFG: {g}")
}

#[test]
fn test_j_increment() {
    let (g, _vals) = precompile("j ++ ++ ++ ++ ++", None, [0..=5]);

    assert_size(&g, 1..=1, 1..=5);
    assert!(g.blocks[0].instructions.values().any(|instr| matches!(&instr.op, OptOp::KsplangOpsIncrement(_))), "inc missing: {g}");

    assert_eq!(&[ValueId::C_FIVE], g.stack.stack.as_slice());
}

#[test]
fn test_dec_positive() {
    const DEC_POSITIVE: &str = "CS CS lensum CS funkcia ++ CS u";
    let (g, [x]) = precompile(DEC_POSITIVE, None, [1..=i64::MAX]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op(OptOp::Add, [ (-1).into(), x.into() ]));
    assert_size(&g, 1..=1, 3..=3);
    assert_eq!(1, g.stack.stack.len());
}

#[test]
fn test_dec() {
    let p = "CS CS lensum CS funkcia CS ++ CS qeq u";
    let (g, [x]) = precompile(p, None, [1..=i64::MAX]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op(OptOp::Add, [ (-1).into(), x.into() ]));
    assert_size(&g, 1..=1, 3..=3);
    assert_eq!(1, g.stack.stack.len());
}

#[test]
fn test_zero_not_positive() {
    let p = "CS CS lensum CS funkcia ++ CS bulkxor";
    let (g, [x]) = precompile(p, None, [FULL_RANGE]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op(OptOp::Select(Condition::Geq(0.into(), x.into())), [ 1.into(), 0.into() ]));
    assert_size(&g, 1..=1, 3..=3);
    assert_eq!(1, g.stack.stack.len());
}

#[test]
fn test_zero_not() {
    let p = "CS CS lensum ++ CS lensum ++ ++ ++ u CS CS lensum CS funkcia CS ++ u CS j ++ CS bulkxor";
    let (g, [x]) = precompile(p, None, [FULL_RANGE]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op(OptOp::Select(Condition::Eq(0i64.into(), x.into())), [ 1.into(), 0.into() ]));
    assert_size(&g, 1..=1, 4..=4);
    assert_eq!(1, g.stack.stack.len());
}

#[test]
fn test_yoink_destructive() {
    let p = "CS CS CS lensum CS funkcia ++ CS ++ lroll swap";
    let (g, [x]) = precompile(p, None, [FULL_RANGE]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op(OptOp::StackSwap, [
        x.into(),
        OptOptPattern::any()
    ]));
    assert_size(&g, 1..=1, 3..=6);
    assert_eq!(1, g.stack.stack.len());
}

// #[test]
// fn test_bitnot() {
//     let p = "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2 CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2 CS CS lensum ++ CS lensum ++ ++ ++ u CS CS lensum CS funkcia ++ u CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia ++ bitshift pop2 pop2 pop2 ++ CS CS lensum CS funkcia ++ CS CS % qeq CS CS lensum CS funkcia ++ u CS CS lensum CS funkcia ++ praise qeq qeq funkcia and pop2 pop2 CS funkcia CS CS lensum CS funkcia ++ CS ++ lroll brz pop2 CS CS lensum CS funkcia ++ praise qeq qeq rem bitshift rem pop2 CS pop j pop2 pop CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia ++ bitshift pop2 pop2 pop2 ++ CS CS lensum CS funkcia ++ CS CS % qeq pop2 CS CS lensum ++ CS lensum CS ++ ++ bitshift CS ++ ++ ++ pop j pop pop CS CS lensum ++ CS CS CS % qeq CS CS ++ lroll CS CS lensum CS funkcia ++ CS CS % qeq CS CS lensum CS funkcia u CS pop";
//     let (g, [x]) = precompile(p, None, [FULL_RANGE]);
//     for v in g.values.values() {
//         println!("{:?}", v);
//     }
//     assert_pattern(&g, g.stack.stack[0], OptOptPattern::op1(OptOp::BinNot, x));
//     assert_size(&g, 1..=1, 3..=3);
//     assert_eq!(1, g.stack.stack.len());
// }

#[test]
fn test_permute_abcd_dacb() {
    let p = "CS CS lensum CS funkcia ++ CS ++ ++ ++ lroll CS CS lensum CS funkcia ++ CS ++ lroll";
    let (g, [a, b, c, d]) = precompile(p, None, [FULL_RANGE, FULL_RANGE, 1..=100, -102..=1002]);
    assert_size(&g, 1..=1, 2..=2);
    assert_eq!(g.stack.stack, [d, a, c, b]);
}

#[test]
fn test_pop4() {
    let p = "CS CS lensum ++ CS CS CS % qeq CS ++ ++ ++ lroll pop";
    let (g, [_a, b, c, d]) = precompile(p, None, [FULL_RANGE, FULL_RANGE, 1..=100, -102..=1002]);
    assert_size(&g, 1..=1, 2..=2);
    assert_eq!(g.stack.stack, [b, c, d]);
}

#[test]
fn test_sub() {
    let p = "CS CS lensum CS funkcia ++ CS CS % qeq CS CS lensum CS funkcia u";
    let (g, [a, b]) = precompile(p, None, [FULL_RANGE, i64::MIN + 1..=i64::MAX]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op2(OptOp::Sub, a, b));
    assert_size(&g, 1..=1, 3..=3);
    assert_eq!(g.stack.stack.len(), 1);
}

#[test]
fn test_sub_range_check() {
    let p = "CS CS lensum CS funkcia ++ CS CS % qeq CS CS lensum CS funkcia u";
    let (g, [a, b]) = precompile(p, None, [FULL_RANGE, FULL_RANGE]);
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op2(OptOp::Sub, a, b));
    assert_size(&g, 1..=1, 4..=4);
    assert_eq!(g.stack.stack.len(), 1);
}

#[test]
fn test_min2() {
    let p = "CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia ++ bitshift pop2 pop2 pop2 CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia ++ bitshift pop2 pop2 pop2 CS CS lensum ++ CS lensum ++ ++ ++ m CS CS lensum ++ CS lensum ++ ++ max % CS CS CS ++ gcd ++ ++ ++ u j j ++ ++ pop2 pop2 pop2 m pop2 CS ++ CS pop2 CS pop2 CS % ++ ++ ++ ++ ++ ++ ++ j pop ++ m pop2 pop2 pop2 CS pop pop2 pop2";

    // Collect trace
    let parsed = parser::parse_program(p).unwrap();
    let initial_stack = vec![1000, 2000];
    let options = VMOptions::new(&initial_stack, 1000, &[], 10000, 10000);
    let run_result = run_with_stats::<ActualTracer>(&parsed, options, ActualTracer::new(&initial_stack, 10000)).unwrap();
    let trace = run_result.tracer;

    println!("trace: {:?}", trace);

    // Precompile with trace
    let mut g = GraphBuilder::new(0);
    let a = g.new_value().id;
    g.values.get_mut(&a).unwrap().range = FULL_RANGE;
    let b = g.new_value().id;
    g.values.get_mut(&b).unwrap().range = FULL_RANGE;

    g.stack.push(a);
    g.stack.push(b);
    g.block_mut_(BlockId(0)).parameters.push(a);
    g.block_mut_(BlockId(0)).parameters.push(b);

    let mut precompiler = Precompiler::new(&parsed, 1000, false, 0, 100_000, true, None, g, trace);
    precompiler.interpret();
    let g = precompiler.g;


    // TODO: actually assert it's just Min
    assert_pattern(&g, g.stack.stack[0], OptOptPattern::op3(OptOp::Median, 3, a, b));
    // assert_pattern(&g, g.stack.stack[0], OptOptPattern::op2(OptOp::Min, a, b));
    // assert_size(&g, 1..=1, 4..=4);
    // assert_eq!(g.stack.stack.len(), 1);
}

// #[test]
// fn test_ismin() {
//     let p = "CS CS lensum CS funkcia CS ++ ++ ++ m CS CS ++ gcd ++ max CS CS % qeq CS CS CS ++ ++ qeq pop2 CS j ++ CS praise qeq qeq pop2 funkcia funkcia ++ % bitshift CS CS gcd CS ++ lroll CS u CS CS pop2 CS lensum m pop2 pop2 CS CS lensum ++ CS lensum ++ ++ ++ u CS CS lensum CS funkcia ++ u CS CS lensum CS funkcia ++ praise qeq pop2 pop2 funkcia ++ bitshift pop2 pop2 pop2 ++ CS CS lensum CS funkcia ++ CS CS % qeq CS CS lensum CS funkcia ++ u CS CS lensum CS funkcia ++ CS bulkxor";
//
//     let (g, [a]) = precompile(p, None, [FULL_RANGE]);
//     assert_pattern(&g, g.stack.stack[0], OptOptPattern::op2(OptOp::Select(Condition::Eq(a.into(), i64::MIN.into())), 0, 1));
//     assert_size(&g, 1..=1, 4..=4);
//     assert_eq!(g.stack.stack.len(), 1);
// }

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
const SORT100: &str = include_str!("tests/sort100.ksplang");

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
    // todo!()
}

#[test]
fn test_sort100() {
    let input = vec![100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 100];
    let res = run_with_opt(&input, SORT100).unwrap();
    assert_eq!(res.stack, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]);
}

fn parse_in_num(str: &str) -> Vec<i64> {
    let mut stack = vec![];
    for line in str.lines() {
        for word in line.split_whitespace() {
            stack.push(word.parse().unwrap());
        }
    }
    stack
}
fn parse_in_txt(str: &str) -> Vec<i64> {
    str.chars().map(|c| c as i64).collect()
}

#[test]
fn test_aoc24_1_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-1-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-1-short.in");

    let input = parse_in_num(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [379802]);
}

#[test]
fn test_aoc24_1_2() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-1-2.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-1-short.in");

    let input = parse_in_num(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [297525]);
}

#[test]
fn test_aoc24_2_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-2-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-2-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [0]);
}

#[test]
fn test_aoc24_3_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-3-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-3-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [31748124]);
}

#[test]
fn test_aoc24_3_2() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-3-2.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-3-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [19281440]);
}

#[test]
fn test_aoc24_4_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-4-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-4-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [77]);
}

#[test]
fn test_aoc24_4_2() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-4-2.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-4-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [67]);
}

#[test]
fn test_aoc24_5_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-5-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-5-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [158]);
}

#[test]
fn test_aoc24_5_2() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-5-2.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-5-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [76]);
}

#[test]
fn test_aoc24_6_2() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-5-2.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-5-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [76]);
}

#[test]
fn test_aoc24_7_1() {
    const PROG: &str = include_str!("../../benches/programs/aoc24-7-1.ksplang");
    const IN: &str = include_str!("../../benches/programs/aoc24-7-short.in");

    let input = parse_in_txt(IN);
    let res = run_with_opt(&input, PROG).unwrap();
    assert_eq!(res.stack, [314001004]);
}


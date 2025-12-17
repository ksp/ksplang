use crate::compiler::{
    cfg::GraphBuilder,
    ops::{OptOp, ValueId},
    osmibytecode::Condition,
    simplifier::simplify_cond,
};
use std::ops::RangeInclusive;

fn create_graph<const N: usize>(ranges: [RangeInclusive<i64>; N]) -> (GraphBuilder, [ValueId; N]) {
    let mut g = GraphBuilder::new(0);
    let values = ranges.map(|range| {
        let info = g.new_value();
        info.range = range;
        info.id
    });
    (g, values)
}

#[test]
fn test_mod_simplification() {
    let (mut g, [a, b]) = create_graph([1..=100, 1..=100]);

    // m = a % b
    let m = g.push_instr(OptOp::Mod, &[a, b], false, Some(0..=100), None).0;

    let at = g.next_instr_id();
    let simplified = simplify_cond(&mut g, Condition::Eq(m, a), at);

    assert_eq!(simplified, Condition::Lt(a, b));
}

#[test]
fn test_add_const_simplification() {
    let (mut g, [a]) = create_graph([0..=100]);
    let c10 = g.store_constant(10);

    // b = a + 10
    let b = g.push_instr(OptOp::Add, &[c10, a], false, Some(10..=110), None).0;

    // condition: b > 20
    let at = g.next_instr_id();
    let c20 = g.store_constant(20);
    let simplified = simplify_cond(&mut g, Condition::Gt(b, c20), at);

    // expected: a + 10 > 20  =>  a > 10, normalized to 10 < a
    let c10_2 = g.store_constant(10);
    assert_eq!(simplified, Condition::Lt(c10_2, a));
}

#[test]
fn test_digitsum_zero() {
    let (mut g, [a]) = create_graph([0..=100]);

    // d = digitsum(a)
    let d = g.push_instr(OptOp::DigitSum, &[a], false, Some(0..=100), None).0;

    // condition: d == 0
    let at = g.next_instr_id();
    let c0 = g.store_constant(0);
    let simplified = simplify_cond(&mut g, Condition::Eq(d, c0), at);

    // expected: a == 0, normalize to 0 == a
    assert_eq!(simplified, Condition::Eq(c0, a));
}

#[test]
fn test_divides_simplification_bug_10_2() {
    let (mut g, [v2]) = create_graph([2..=2]);
    // 10 % 2 == 0
    let at = g.next_instr_id();
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v2), at);
    assert_eq!(simplified, Condition::True, "10 % 2 should be True");
}

#[test]
fn test_divides_simplification_bug_12_4() {
    let (mut g, [v4]) = create_graph([4..=4]);
    // 12 % 4 == 0
    let at = g.next_instr_id();
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v4), at);
    assert_eq!(simplified, Condition::True, "12 % 4 should be True");
}

#[test]
fn test_divides_simplification_bug_10_neg2() {
    let (mut g, [v_neg2]) = create_graph([-2..=-2]);
    // 10 % -2 == 0
    let at = g.next_instr_id();
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v_neg2), at);
    assert_eq!(simplified, Condition::True, "10 % -2 should be True");
}

#[test]
fn test_divides_simplification_10_4() {
    let (mut g, [v4]) = create_graph([4..=4]);
    // 10 % 4 != 0
    let at = g.next_instr_id();
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v4), at);
    assert_eq!(simplified, Condition::False, "10 % 4 should be False");
}

#[test]
fn test_divides_simplification_11_0to9() {
    let (mut g, [v1]) = create_graph([0..=9]);
    // 11 % v1 == 0
    let at = g.next_instr_id();
    let c11 = g.store_constant(11);
    let simplified = simplify_cond(&mut g, Condition::Divides(c11, v1), at);
    // 11 is prime, so divisors are 1, 11.
    // v1 is in 0..=9. Only 1 is in range.
    // So v1 == 1.
    let c1 = g.store_constant(1);
    // Condition::Eq might normalize order, check both or rely on specific behavior
    // Based on previous output "1 == v1", it seems to normalize constant to left?
    // Or maybe my code produced Eq(v1, 1) and Display prints it as 1 == v1?
    // Let's assume Eq(v1, 1) based on code.
    // Actually, let's check if it equals either.
    let is_eq = simplified == Condition::Eq(v1, c1) || simplified == Condition::Eq(c1, v1);
    assert!(is_eq, "Expected v1 == 1, got {:?}", simplified);
}

#[test]
fn test_divides_simplification_12_0to5() {
    let (mut g, [v1]) = create_graph([0..=5]);
    // 12 % v1 == 0
    let at = g.next_instr_id();
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v1), at);
    // Divisors of 12 in 0..=5 are 1, 2, 3, 4.
    // 5 is not divisor.
    // Cannot simplify to single Eq.
    assert_eq!(simplified, Condition::Divides(c12, v1));
}

#[test]
fn test_divides_simplification_12_7to11() {
    let (mut g, [v1]) = create_graph([7..=11]);
    // 12 % v1 == 0
    let at = g.next_instr_id();
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v1), at);
    // Range is strictly between 12/2 and 12.
    // No divisors possible.
    assert_eq!(simplified, Condition::False);
}

#[test]
fn test_divides_simplification_2to4_3() { // used in duplication
    let (mut g, [v1]) = create_graph([2..=4]);
    // 3 % v1 == 0
    let at = g.next_instr_id();
    let simplified = simplify_cond(&mut g, Condition::Divides(ValueId::C_THREE, v1), at);
    assert_eq!(simplified, Condition::Eq(ValueId::C_THREE, v1), "3 % v1[2..4]");
}

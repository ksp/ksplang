use crate::compiler::{
    cfg::GraphBuilder, ops::{BlockId, InstrId, OpEffect, OptInstr, OptOp, ValueId}, osmibytecode::Condition, pattern::OptOptPattern, simplifier::{simplify_cond, simplify_instr}, utils::FULL_RANGE
};
use std::ops::RangeInclusive;
const END_INSTR: InstrId = InstrId(BlockId(0), u32::MAX);

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

    let simplified = simplify_cond(&mut g, Condition::Eq(m, a), END_INSTR);

    assert_eq!(simplified, Condition::Lt(a, b));
}

#[test]
fn test_add_const_simplification() {
    let (mut g, [a]) = create_graph([0..=100]);
    let c10 = g.store_constant(10);

    // b = a + 10
    let b = g.push_instr(OptOp::Add, &[c10, a], false, Some(10..=110), None).0;

    // condition: b > 20
    let c20 = g.store_constant(20);
    let simplified = simplify_cond(&mut g, Condition::Gt(b, c20), END_INSTR);

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
    let c0 = g.store_constant(0);
    let simplified = simplify_cond(&mut g, Condition::Eq(d, c0), END_INSTR);

    // expected: a == 0, normalize to 0 == a
    assert_eq!(simplified, Condition::Eq(c0, a));
}

#[test]
fn test_mod_simplification_gt_const_imin() {
    let (mut g, [x]) = create_graph([0..=10]);
    let m = g.push_instr(OptOp::Mod, &[x, ValueId::C_TWO], false, Some(0..=1), None).0;

    // i64::MIN > (x % 2) is impossible
    assert_eq!(simplify_cond(&mut g, Condition::Gt(ValueId::C_IMIN, m), END_INSTR), Condition::False);
}

#[test]
fn test_mod_simplification_lt_const_imax() {
    let (mut g, [x]) = create_graph([0..=10]);
    let m = g.push_instr(OptOp::Mod, &[x, ValueId::C_TWO], false, Some(0..=1), None).0;

    // i64::MAX < (x % 2) is impossible
    assert_eq!(simplify_cond(&mut g, Condition::Lt(ValueId::C_IMAX, m), END_INSTR), Condition::False);
}

#[test]
fn test_mul_simplification_gt_negative_multiplier() {
    let (mut g, [x]) = create_graph([-99..=99]);
    let mul = g.push_instr(OptOp::Mul, &[ValueId::C_NEG_TWO, x], false, None, None).0;

    // 2 > (-2 * x)  =>  -1 < x
    assert_eq!(simplify_cond(&mut g, Condition::Gt(ValueId::C_TWO, mul), END_INSTR), Condition::Lt(ValueId::C_NEG_ONE, x));

    // 2 < (-2 * x)  =>  x < -1  =>  -1 > x
    assert_eq!(simplify_cond(&mut g, Condition::Lt(ValueId::C_TWO, mul), END_INSTR), Condition::Gt(ValueId::C_NEG_ONE, x));
}

#[test]
fn test_divides_simplification_bug_10_2() {
    let (mut g, [v2]) = create_graph([2..=2]);
    // 10 % 2 == 0
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v2), END_INSTR);
    assert_eq!(simplified, Condition::True, "10 % 2 should be True");
}

#[test]
fn test_divides_simplification_bug_12_4() {
    let (mut g, [v4]) = create_graph([4..=4]);
    // 12 % 4 == 0
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v4), END_INSTR);
    assert_eq!(simplified, Condition::True, "12 % 4 should be True");
}

#[test]
fn test_divides_simplification_bug_10_neg2() {
    let (mut g, [v_neg2]) = create_graph([-2..=-2]);
    // 10 % -2 == 0
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v_neg2), END_INSTR);
    assert_eq!(simplified, Condition::True, "10 % -2 should be True");
}

#[test]
fn test_divides_simplification_10_4() {
    let (mut g, [v4]) = create_graph([4..=4]);
    // 10 % 4 != 0
    let c10 = g.store_constant(10);
    let simplified = simplify_cond(&mut g, Condition::Divides(c10, v4), END_INSTR);
    assert_eq!(simplified, Condition::False, "10 % 4 should be False");
}

#[test]
fn test_divides_simplification_11_0to9() {
    let (mut g, [v1]) = create_graph([0..=9]);
    // 11 % v1 == 0
    let c11 = g.store_constant(11);
    let simplified = simplify_cond(&mut g, Condition::Divides(c11, v1), END_INSTR);
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
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v1), END_INSTR);
    // Divisors of 12 in 0..=5 are 1, 2, 3, 4.
    // 5 is not divisor.
    // Cannot simplify to single Eq.
    assert_eq!(simplified, Condition::Divides(c12, v1));
}

#[test]
fn test_divides_simplification_12_7to11() {
    let (mut g, [v1]) = create_graph([7..=11]);
    // 12 % v1 == 0
    let c12 = g.store_constant(12);
    let simplified = simplify_cond(&mut g, Condition::Divides(c12, v1), END_INSTR);
    // Range is strictly between 12/2 and 12.
    // No divisors possible.
    assert_eq!(simplified, Condition::False);
}

#[test]
fn test_divides_simplification_2to4_3() { // used in duplication
    let (mut g, [v1]) = create_graph([2..=4]);
    // 3 % v1 == 0
    let simplified = simplify_cond(&mut g, Condition::Divides(ValueId::C_THREE, v1), END_INSTR);
    assert_eq!(simplified, Condition::Eq(ValueId::C_THREE, v1), "3 % v1[2..4]");
}

#[test]
fn test_absfactorial_eq_neq_non_factorial_0to6() {
    let (mut g, [a]) = create_graph([FULL_RANGE]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    // 7 is not |n|!
    let simplified_eq = simplify_cond(&mut g, Condition::Eq(ValueId::C_SEVEN, fact), END_INSTR);
    assert_eq!(simplified_eq, Condition::False);

    let simplified_neq = simplify_cond(&mut g, Condition::Neq(ValueId::C_SEVEN, fact), END_INSTR);
    assert_eq!(simplified_neq, Condition::True);
}

#[test]
fn test_absfactorial_zero_lt_always_true() {
    let (mut g, [a]) = create_graph([-3..=3]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    // 0 < |a|! and 0 <= |a|! is always true
    assert_eq!(simplify_cond(&mut g, Condition::Leq(ValueId::C_ZERO, fact), END_INSTR), Condition::True);
    assert_eq!(simplify_cond(&mut g, Condition::Lt(ValueId::C_ZERO, fact), END_INSTR), Condition::True);
}

#[test]
fn test_abssub_sgn_symmetric_range() {
    let (mut g, [a]) = create_graph([-3..=3]);
    let sgn = g.push_instr(OptOp::Sgn, &[a], false, None, None).0;
    let abs = g.push_instr(OptOp::AbsSub, &[a, sgn], false, None, None).0;

    // 3 <= |a - sgn(a)| is false
    let simplified = simplify_cond(&mut g, Condition::Lt(ValueId::C_THREE, abs), END_INSTR);
    assert_eq!(simplified, Condition::False);
    let simplified = simplify_cond(&mut g, Condition::Leq(ValueId::C_THREE, abs), END_INSTR);
    assert_eq!(simplified, Condition::False);

    // 2 <= |a - sgn(a)|  —— cannot be simplified
    let simplified = simplify_cond(&mut g, Condition::Leq(ValueId::C_TWO, abs), END_INSTR);
    assert_eq!(simplified, Condition::Eq(ValueId::C_TWO, abs));
}

#[test]
fn test_abssub_sgn_border_check_asymmetric_range() {
    let (mut g, [a]) = create_graph([-3..=4]);
    let sgn = g.push_instr(OptOp::Sgn, &[a], false, None, None).0;
    let abs = g.push_instr(OptOp::AbsSub, &[a, sgn], false, None, None).0;

    // 3 <= |a - sgn(a)| is false
    let simplified = simplify_cond(&mut g, Condition::Leq(ValueId::C_THREE, abs), END_INSTR);
    assert_eq!(simplified, Condition::Eq(ValueId::C_FOUR, a));
}

#[test]
fn test_absfactorial_3to6_range() {
    let (mut g, [a]) = create_graph([3..=6]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    // 2 is not |n|! if n >= 3
    let simplified_eq2 = simplify_cond(&mut g, Condition::Eq(ValueId::C_TWO, fact), END_INSTR);
    assert_eq!(simplified_eq2, Condition::False);

    // 6 = 3! so should simplify to a == 3
    let simplified_eq6 = simplify_cond(&mut g, Condition::Eq(ValueId::C_SIX, fact), END_INSTR);
    assert_eq!(simplified_eq6, Condition::Eq(ValueId::C_THREE, a));
}

#[test]
fn test_absfactorial_eq_factorial_constant_6_abs() {
    let (mut g, [a]) = create_graph([-6..=6]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    // cannot be simplified because absolute value
    let simplified = simplify_cond(&mut g, Condition::Eq(ValueId::C_SIX, fact), END_INSTR);

    assert_eq!(simplified, Condition::Eq(ValueId::C_SIX, fact));
}

#[test]
fn test_absfactorial_eq_factorial_constant_6_neg_only() {
    let (mut g, [a]) = create_graph([-6..=-3]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    let c6 = ValueId::C_SIX;
    let cneg3 = g.store_constant(-3);

    let simplified = simplify_cond(&mut g, Condition::Eq(c6, fact), END_INSTR);

    // With only negative inputs, equality should map to the negative argument producing 6 => a == -3
    assert_eq!(simplified, Condition::Eq(cneg3, a));
}

#[test]
fn test_absfactorial_eq_factorial_constant_6_mixed_sign_keeps() {
    let (mut g, [a]) = create_graph([-6..=6]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    let c6 = ValueId::C_SIX;

    let simplified = simplify_cond(&mut g, Condition::Eq(c6, fact), END_INSTR);

    // When both signs are possible, simplifier should leave the condition unchanged
    assert_eq!(simplified, Condition::Eq(c6, fact));
}

#[test]
fn test_absfactorial_eq_one_mixed_range_panics() {
    let (mut g, [a]) = create_graph([-5..=5]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;

    // Simplifying 1 == |a|! across a mixed-sign range currently panics via unreachable!
    let _ = simplify_cond(&mut g, Condition::Eq(ValueId::C_ONE, fact), END_INSTR);
}

#[test]
fn test_absfactorial_gt_lt_positive_range() {
    let (mut g, [a]) = create_graph([-3..=10]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;
    let at = g.next_instr_id();
    let c100 = g.store_constant(100); // between 5! (120) and 4! (24)
    let c120 = g.store_constant(120); // between 5! (120) and 4! (24)

    // 100 > |a|!  =>  4 >= a (since we need |a|! <= 100, so |a| <= 4)
    assert_eq!(simplify_cond(&mut g, Condition::Gt(c100, fact), at), Condition::Geq(ValueId::C_FOUR, a));
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c100, fact), at), Condition::Geq(ValueId::C_FOUR, a));

    // 100 < |a|!  =>  5 <= a (since we need |a|! > 100, so |a| >= 5)
    assert_eq!(simplify_cond(&mut g, Condition::Lt(c100, fact), at), Condition::Leq(ValueId::C_FIVE, a));
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c100, fact), at), Condition::Leq(ValueId::C_FIVE, a));

    // 120 > |a|!  =>  5 > a
    assert_eq!(simplify_cond(&mut g, Condition::Gt(c120, fact), at), Condition::Gt(ValueId::C_FIVE, a));
    // 120 >= |a|!  =>  5 >= a
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c120, fact), at), Condition::Geq(ValueId::C_FIVE, a));

    // 120 < |a|!  =>  5 < a
    assert_eq!(simplify_cond(&mut g, Condition::Lt(c120, fact), at), Condition::Lt(ValueId::C_FIVE, a));
    // 120 <= |a|!  =>  5 <= a
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c120, fact), at), Condition::Leq(ValueId::C_FIVE, a));

    assert_eq!(simplify_cond(&mut g, Condition::Eq(c120, fact), at), Condition::Eq(ValueId::C_FIVE, a));
    assert_eq!(simplify_cond(&mut g, Condition::Neq(c120, fact), at), Condition::Neq(ValueId::C_FIVE, a));

}

#[test]
fn test_absfactorial_gt_lt_negative_range() {
    let (mut g, [a]) = create_graph([-10..=3]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;
    let at = g.next_instr_id();
    let c100 = g.store_constant(100);
    let c120 = g.store_constant(120);
    let cneg4 = g.store_constant(-4);
    let cneg5 = g.store_constant(-5);

    // 100 > |a|!  =>  -4 <= a
    assert_eq!(simplify_cond(&mut g, Condition::Gt(c100, fact), at), Condition::Leq(cneg4, a));
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c100, fact), at), Condition::Leq(cneg4, a));

    // 100 < |a|!  =>  -5 >= a
    assert_eq!(simplify_cond(&mut g, Condition::Lt(c100, fact), at), Condition::Geq(cneg5, a));
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c100, fact), at), Condition::Geq(cneg5, a));

    // 120 > |a|!  =>  -5 < a
    assert_eq!(simplify_cond(&mut g, Condition::Gt(c120, fact), at), Condition::Lt(cneg5, a));
    // 120 >= |a|!  =>  -5 <= a
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c120, fact), at), Condition::Leq(cneg5, a));

    // 120 < |a|!  =>  -5 > a
    assert_eq!(simplify_cond(&mut g, Condition::Lt(c120, fact), at), Condition::Gt(cneg5, a));
    // 120 <= |a|!  =>  -5 >= a
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c120, fact), at), Condition::Geq(cneg5, a));

    assert_eq!(simplify_cond(&mut g, Condition::Eq(c120, fact), at), Condition::Eq(cneg5, a));
    assert_eq!(simplify_cond(&mut g, Condition::Neq(c120, fact), at), Condition::Neq(cneg5, a));
}

#[test]
fn test_absfactorial_gt_lt_mixed_range() {
    let (mut g, [a]) = create_graph([-10..=10]);
    let fact = g.push_instr(OptOp::AbsFactorial, &[a], false, None, None).0;
    let at = g.next_instr_id();
    let c100 = g.store_constant(100);
    let c120 = g.store_constant(120);

    assert_eq!(simplify_cond(&mut g, Condition::Gt(c100, fact), at), Condition::Gt(c100, fact));
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c100, fact), at), Condition::Geq(c100, fact));

    assert_eq!(simplify_cond(&mut g, Condition::Lt(c100, fact), at), Condition::Lt(c100, fact));
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c100, fact), at), Condition::Leq(c100, fact));

    assert_eq!(simplify_cond(&mut g, Condition::Gt(c120, fact), at), Condition::Gt(c120, fact));
    assert_eq!(simplify_cond(&mut g, Condition::Geq(c120, fact), at), Condition::Geq(c120, fact));

    assert_eq!(simplify_cond(&mut g, Condition::Lt(c120, fact), at), Condition::Lt(c120, fact));
    assert_eq!(simplify_cond(&mut g, Condition::Leq(c120, fact), at), Condition::Leq(c120, fact));
}

#[test]
fn test_mul_div_simplification_keeps_divide_by_zero_effect() {
    let (mut g, [a, x]) = create_graph([FULL_RANGE, -1..=1]);
    let (mul, mul_instr) = g.push_instr(OptOp::Mul, &[a, x], true, None, None);
    assert_eq!(OpEffect::MayFail, mul_instr.unwrap().effect);

    let div = g.value_numbering(OptOp::Div, &[mul, x], None, None);
    assert_eq!(div, a);
    let last_instr = g.current_block_ref().instructions.values().last().unwrap();
    assert_eq!(last_instr.op, OptOp::Assert(Condition::Neq(ValueId::C_ZERO, x), crate::vm::OperationError::DivisionByZero));
}

#[test]
fn test_add_merging_simplification() {
    let (mut g, [a, b, c, d]) = create_graph([-100..=100, 0..=100, 0..=100, 0..=111]);
    let add1 = g.value_numbering(OptOp::Add, &[a, b], None, None);
    let sub = g.value_numbering(OptOp::Sub, &[c, b], None, None);
    let add2 = g.value_numbering(OptOp::Add, &[add1, sub], None, None);
    let add3 = g.value_numbering(OptOp::Add, &[add2, d], None, None);
    println!("{g}");

    g.stack.poped_values.extend([add1, sub, add2, add3]);
    g.stack.push(add3);
    g.clean_poped_values();

    let last_instr = g.current_block_ref().instructions.values().last().unwrap();
    assert_eq!(last_instr.op, OptOp::Add);
    assert_eq!(last_instr.effect, OpEffect::None);
    assert_eq!(last_instr.inputs.as_slice(), [a, c, d]);

    assert_eq!(1, g.current_block_ref().instructions.len());
}

#[test]
fn test_add_mul_equivalence() {
    let (mut g, [a, b]) = create_graph([-100..=100, 0..=100]);
    let add1 = g.value_numbering(OptOp::Add, &[a, ValueId::C_ONE], None, None);
    let add2 = g.value_numbering(OptOp::Add, &[b, ValueId::C_ONE], None, None);
    let mul = g.value_numbering(OptOp::Mul, &[add1, add2], None, None);

    g.stack.poped_values.extend([add1, mul, add2]);
    g.stack.push(mul);
    g.clean_poped_values();
    println!("{g}");

    let pattern = OptOptPattern::op4(OptOp::Add, 1, a, b, OptOptPattern::op2(OptOp::Mul, a, b));
    assert!(pattern.try_match(&g, &[mul]).is_ok());
    assert_eq!(2, g.current_block_ref().instructions.len());
}

#[test]
fn test_median_cursed_conversion1() {
    let (mut g, [a, b]) = create_graph([FULL_RANGE, FULL_RANGE]);
    let n = g.store_constant(2);

    let instr = OptInstr::new(g.next_instr_id(), OptOp::MedianCursed, &[n, a, b], ValueId::from(i32::MAX));
    let (simplified, _) = simplify_instr(&mut g, instr);

    assert_eq!(simplified.op, OptOp::Median);
    assert_eq!(simplified.inputs.len(), 2);
    assert_eq!([n, a], simplified.inputs.as_slice());
}

#[test]
fn test_median_cursed_conversion2() {
    let (mut g, [n, a, b]) = create_graph([2..=3, FULL_RANGE, FULL_RANGE]);

    g.push_assert(Condition::Neq(n, ValueId::C_THREE), crate::vm::OperationError::DivisionByZero, None);

    let n_range = g.val_range_at(n, g.next_instr_id());
    assert_eq!(n_range, 2..=2);

    let instr = OptInstr::new(g.next_instr_id(), OptOp::MedianCursed, &[n, a, b, ValueId::C_ZERO], ValueId::from(i32::MAX));
    let (simplified, _) = simplify_instr(&mut g, instr);

    assert_eq!(simplified.op, OptOp::Median, "{simplified}\n{g}");
    assert_eq!(simplified.inputs.len(), 2);
    assert_eq!([ValueId::C_TWO, a], simplified.inputs.as_slice());
}

// #[test]
// fn test_median_two_args_odd_constant() { // will not happen in practice
//     let (mut g, [a]) = create_graph([0..=10]);

//     let instr = OptInstr::new(g.next_instr_id(), OptOp::Median, &[ValueId::C_THREE, a], ValueId::from(i32::MAX));
//     let _ = simplify_instr(&mut g, instr);
// }

#[test]
fn test_mul_constant_chain_overflow_panics() {
    let (mut g, [a]) = create_graph([0..=10]);
    let (double, _) = g.push_instr(OptOp::Mul, &[ValueId::C_TWO, a], false, None, None);

    let instr = OptInstr::new(g.next_instr_id(), OptOp::Mul, &[ValueId::C_IMIN, double], ValueId::from(i32::MAX));
    let _ = simplify_instr(&mut g, instr);
}

#[test]
fn test_gcd1_is_1() {
    let (mut g, [a, b]) = create_graph([FULL_RANGE, FULL_RANGE]);

    let res = g.value_numbering(OptOp::Gcd, &[a, b, ValueId::C_ONE], None, None);

    assert_eq!(ValueId::C_ONE, res);
}


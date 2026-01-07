use std::{cmp, collections::BTreeSet, ops::RangeInclusive, sync::LazyLock};

use arrayvec::ArrayVec;
use num_integer::Integer;
use smallvec::{SmallVec, ToSmallVec, smallvec};

use crate::{compiler::{analyzer::cond_implies, cfg::GraphBuilder, ops::{InstrId, OpEffect, OptInstr, OptOp, ValueId}, osmibytecode::Condition, pattern::OptOptPattern, range_ops::{IRange, mod_split_ranges, range_signum}, utils::{FULL_RANGE, abs_range, intersect_range, range_is_signless, union_range}}, digit_sum::digit_sum_u64, vm::{self, OperationError}};

use super::pattern::{OptOptPattern as P};

fn overlap(a: &RangeInclusive<i64>, b: &RangeInclusive<i64>) -> Option<RangeInclusive<i64>> {
    let start = *a.start().max(b.start());
    let end = *a.end().min(b.end());
    if start <= end {
        Some(start..=end)
    } else {
        None
    }
}

fn cond_flip(cond: &Condition<ValueId>, when: bool) -> Condition<ValueId> {
    if when {
        match cond {
            Condition::Eq(_, _) | Condition::Neq(_, _) | Condition::True | Condition::False => cond.clone(),
            &Condition::Lt(a, b) => Condition::Gt(a, b),
            &Condition::Leq(a, b) => Condition::Geq(a, b),
            &Condition::Gt(a, b) => Condition::Lt(a, b),
            &Condition::Geq(a, b) => Condition::Leq(a, b),
            _ => unreachable!("{cond}")
        }
    } else {
        cond.clone()
    }
}

pub fn simplify_cond(cfg: &mut GraphBuilder, condition: Condition<ValueId>, at: InstrId) -> Condition<ValueId> {
    let mut cond_mut = condition.clone();
    let mut changelog: SmallVec<[Condition<ValueId>; 4]> = smallvec![cond_mut.clone()];
    loop {
        let new_cond = simplify_cond_core(cfg, &cond_mut, at);
        let done = new_cond == cond_mut;
        cond_mut = new_cond;
        if done {
            break;
        } else {
            changelog.push(cond_mut.clone())
        }
    }

    for val in cond_mut.regs().into_iter().filter(|x| x.is_computed()) {
        for (assumption, _, _, instr_id) in cfg.iter_val_assumptions(val, at) {
            if let Some(implied) = cond_implies(cfg, &assumption, &cond_mut, at) && implied != cond_mut {
                if cfg.conf.should_log(10) {
                    println!("simplify_cond: condition '{cond_mut}' + assumption '{assumption}' (from {instr_id}) imply '{implied}'")
                }
                cond_mut = implied;
                changelog.push(cond_mut.clone());
                if cond_mut == Condition::True || cond_mut == Condition::False {
                    break;
                }
            }
        }
    }
    if cfg!(debug_assertions) && cond_mut != condition && cfg.conf.should_log(5) {
        println!("simplify_cond({condition}, {at}) ... {:?} -> {cond_mut}", changelog);
    }
    cond_mut
}


fn condition_to_range(condition: &Condition<ValueId>, ac: i64) -> Option<(IRange, bool)> {
    debug_assert!(condition.regs()[0].is_constant());
    match condition {
        Condition::Eq(_, _) => Some((ac..=ac, false)),
        Condition::Neq(_, _) => Some((ac..=ac, true)),
        Condition::Lt(_, _) => Some((ac.strict_add(1)..=i64::MAX, false)),
        Condition::Leq(_, _) => Some((ac..=i64::MAX, false)),
        Condition::Gt(_, _) => Some((i64::MIN..=ac.strict_sub(1), false)),
        Condition::Geq(_, _) => Some((i64::MIN..=ac, false)),
        _ => None
    }
}

fn condition_overlaps_range(condition: &Condition<ValueId>, ac: i64, r: &IRange) -> bool {
    match condition {
        Condition::Eq(_, _) => r.contains(&ac),
        Condition::Neq(_, _) => r != &(ac..=ac),
        Condition::Lt(_, _) => ac < *r.end(), // ac < x
        Condition::Leq(_, _) => ac <= *r.end(),
        Condition::Gt(_, _) => ac > *r.start(),
        Condition::Geq(_, _) => ac >= *r.start(),
        _ => true
    }
}

fn create_range_constraint_condition(cfg: &mut GraphBuilder, v: ValueId, range0: &IRange, range: &IRange) -> ArrayVec<Condition<ValueId>, 2> {
    let mut res = ArrayVec::new();
    if range.start() == range.end() {
        let c = cfg.store_constant(*range.start());
        res.push(Condition::Eq(c, v));
        return res
    }
    if range0.end() != range.end() {
        let end = cfg.store_constant(*range.end());
        res.push(Condition::Geq(end, v));
    }
    if range0.start() != range.start() {
        let start = cfg.store_constant(*range.start());
        res.push(Condition::Leq(start, v));
    }
    return res;
}

fn simplify_cond_core(cfg: &mut GraphBuilder, condition: &Condition<ValueId>, at: InstrId) -> Condition<ValueId> {
    match condition.clone() {
        Condition::EqConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Eq(c, a)
        }
        Condition::NeqConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Neq(c, a)
        }
        Condition::LtConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Gt(c, a)
        }
        Condition::LeqConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Geq(c, a)
        }
        Condition::GtConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Lt(c, a)
        }
        Condition::GeqConst(a, b) => {
            let c = cfg.store_constant(b as i64);
            Condition::Leq(c, a)
        }
        Condition::DividesConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Divides(a, b)
        }
        Condition::NotDividesConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::NotDivides(a, b)
        }
        Condition::False => Condition::False,
        Condition::True => Condition::True,
        Condition::Eq(a, b) | Condition::Leq(a, b) | Condition::Geq(a, b) | Condition::Divides(a, b)
            if a == b => Condition::True,
        Condition::Neq(a, b) | Condition::Lt(a, b) | Condition::Gt(a, b) | Condition::NotDivides(a, b)
            if a == b => Condition::False,
        Condition::Eq(a, b) if a > b => Condition::Eq(b, a),
        Condition::Neq(a, b) if a > b => Condition::Neq(b, a),
        Condition::Lt(a, b) if a > b => Condition::Gt(b, a),
        Condition::Gt(a, b) if a > b => Condition::Lt(b, a),
        Condition::Leq(a, b) if a > b => Condition::Geq(b, a),
        Condition::Geq(a, b) if a > b => Condition::Leq(b, a),
        Condition::Eq(a, b) | Condition::Neq(a, b) | Condition::Lt(a, b) | Condition::Gt(a, b) | Condition::Leq(a, b) | Condition::Geq(a, b) => {
            assert!(a.is_constant() || !b.is_constant()); // we depend on the ordering
            let (a_normalized, ar) = cfg.analyze_val_at(a, at);
            let (b_normalized, br) = cfg.analyze_val_at(b, at);
            if a_normalized != a || b_normalized != b {
                return condition.replace_arr([a_normalized, b_normalized])
            }

            if ar.start() == ar.end() && !a.is_constant() { // normalize constant
                return condition.replace_arr([cfg.store_constant(*ar.start()), b])
            }
            if br.start() == br.end() && !b.is_constant() {
                return condition.replace_arr([a, cfg.store_constant(*br.start())])
            }

            match condition {
                Condition::Eq(_, _) if overlap(&ar, &br).is_none() => return Condition::False,
                Condition::Neq(_, _) if overlap(&ar, &br).is_none() => return Condition::True,
                // Condition::Neq(_, _) if *ar.start() == *ar.end() && *br.start().wrapping_add(1) == *br.end() =>
                Condition::Lt(_, _) if ar.end() < br.start() => return Condition::True,
                Condition::Lt(_, _) if ar.start() >= br.end() => return Condition::False,
                // Condition::Lt(_, _) if ar.end() == br.start()
                Condition::Gt(_, _) if ar.start() > br.end() => return Condition::True,
                Condition::Gt(_, _) if ar.end() <= br.start() => return Condition::False,
                Condition::Leq(_, _) if ar.end() <= br.start() => return Condition::True,
                Condition::Leq(_, _) if ar.start() > br.end() => return Condition::False,
                Condition::Geq(_, _) if ar.start() >= br.end() => return Condition::True,
                Condition::Geq(_, _) if ar.end() < br.start() => return Condition::False,
                _ => {}
            }
            let condition = match condition.clone() {
                Condition::Geq(a, b) if ar.end() == br.start() =>
                    Condition::Eq(a, b),
                Condition::Gt(a, b) if ar.start() == br.end() => // a > b => a != b IF a is always >= b
                    Condition::Neq(a, b),
                Condition::Leq(a, b) if ar.start() == br.end() =>
                    Condition::Eq(a, b),
                Condition::Lt(a, b) if ar.end() == br.start() =>
                    Condition::Neq(a, b),
                x => x
            };
            if a.is_constant() {
                let ac = *ar.start();
                if let Some(def) = cfg.get_defined_at(b) {
                    // Min/Max comparison simplification
                    //  min(k, x) == k  -> x <= k
                    if matches!(def.op, OptOp::Min | OptOp::Max) && def.inputs.len() == 2 && def.inputs[0].is_constant() {
                        let k = cfg.get_constant_(def.inputs[0]);
                        let x = def.inputs[1];
                        if matches!(def.op, OptOp::Min) {
                            assert!(k >= ac); // should be eliminated by previous checks
                        } else {
                            assert!(k <= ac);
                        }
                        return match (&condition, &def.op) {
                            // min(10, x) == 10 -> x >= 10
                            (Condition::Eq(_, _) | Condition::Leq(_, _), OptOp::Min) if ac == k => Condition::Leq(a, x),
                            // max(5, x) == 5 -> x <= 5
                            (Condition::Eq(_, _) | Condition::Geq(_, _), OptOp::Max) if ac == k => Condition::Geq(a, x),
                            // min(10, x) == 5 -> x == 5
                            (Condition::Eq(_, _), _) if ac != k => Condition::Eq(a, x),
                            // same for Neq
                            (Condition::Neq(_, _) | Condition::Gt(_, _), OptOp::Min) if ac == k => Condition::Gt(a, x),
                            (Condition::Neq(_, _) | Condition::Lt(_, _), OptOp::Max) if ac == k => Condition::Lt(a, x),
                            (Condition::Neq(_, _), _) if ac != k => Condition::Neq(a, x),
                            // rest should be handled
                            (Condition::Leq(_, _), _) if ac != k => Condition::Leq(a, x),
                            (Condition::Geq(_, _), _) if ac != k => Condition::Geq(a, x),
                            (Condition::Lt(_, _), _) if ac != k => Condition::Lt(a, x),
                            (Condition::Gt(_, _), _) if ac != k => Condition::Gt(a, x),

                            _ => unreachable!("{:?} {:?} {} {}", condition, def, k, ac),
                        }
                    }

                    if ac == 0 && matches!(def.op, OptOp::DigitSum) {
                        let b2 = def.inputs[0];
                        // DigitSum preserves zero, some programs use this when branching
                        return match condition {
                            Condition::Eq(_, _) => Condition::Eq(a, b2),
                            Condition::Neq(_, _) => Condition::Neq(a, b2),
                            Condition::Lt(_, _) => Condition::Neq(a, b2), // 0 < CS(b) => 0 != b
                            Condition::Leq(_, _) => Condition::True, // 0 <= CS(b)
                            Condition::Gt(_, _) => Condition::False, // 0 > CS(b)
                            Condition::Geq(_, _) => Condition::Eq(a, b2), // 0 >= CS(b)
                            x => return x
                        }
                    }

                    if matches!(def.op, OptOp::Sgn) {
                        let b2 = def.inputs[0];
                        return match (ac, condition) {
                            (0, Condition::Eq(_, _)) => Condition::Eq(a, b2),
                            (1, Condition::Eq(_, _)) => Condition::Lt(ValueId::C_ZERO, b2), // 0 < b
                            (-1, Condition::Eq(_, _)) => Condition::Gt(ValueId::C_ZERO, b2), // 0 > b
                            (0, Condition::Neq(_, _)) => Condition::Neq(a, b2),
                            (1, Condition::Neq(_, _)) => Condition::Geq(ValueId::C_ZERO, b2), // 0 >= b
                            (-1, Condition::Neq(_, _)) => Condition::Leq(ValueId::C_ZERO, b2), // 0 <= b
                            (_, x) => return x
                        }
                    }

                    if matches!(def.op, OptOp::Add) && def.inputs.len() == 2 && def.inputs[0].is_constant() {
                        // A > (b + C) => (A - C) > b
                        let shift = cfg.get_constant_(def.inputs[0]);
                        let b2 = def.inputs[1];
                        let a2 = cfg.store_constant(ac.strict_sub(shift));

                        return condition.replace_arr([a2, b2])
                    }

                    if matches!(def.op, OptOp::Sub) && def.inputs.len() == 2 && def.inputs[0].is_constant() {
                        // A > (C - b) => b > -(C + A)
                        // i.e. 100 > (30 - b) => b > -70
                        // i.e. 12 == (0 - b) => b == -12
                        let c = cfg.get_constant_(def.inputs[0]);
                        let b2 = def.inputs[1];
                        let a2 = cfg.store_constant(c.strict_sub(ac));

                        return condition.replace_arr([b2, a2])
                    }

                    if matches!(def.op, OptOp::Sub) && ac == 0 && def.inputs.len() == 2 {
                        // 0 == (a - b) => a == b
                        // 0 >= (a - b) => b >= a
                        return condition.replace_arr([def.inputs[1], def.inputs[0]])
                    }
                    if matches!(def.op, OptOp::AbsSub) && ac == 0 && def.inputs.len() == 2 {
                        // same for AbsSub
                        match condition {
                            Condition::Eq(_, _) => return Condition::Eq(def.inputs[0], def.inputs[1]),
                            Condition::Neq(_, _) => return Condition::Neq(def.inputs[0], def.inputs[1]),
                            _ => { } // should not happen, it should be normalized to == / !=
                        }
                    }

                    if matches!(def.op, OptOp::AbsSub) && def.inputs.iter().all(|v| v.is_computed()) && ac > 0 {
                        // abssub(a, sgn(a)) is used for i64::MIN checks (this is generalized for any boundary check just in case)
                        let &[sub_a, sub_b] = def.inputs.as_slice() else { unreachable!() };
                        if let Some(sub_b_info) = cfg.val_info(sub_b) &&
                           let Some(def2) = sub_b_info.assigned_at.and_then(|iid| cfg.get_instruction(iid))
                        {
                            let sub_a_range = cfg.val_range_at(sub_a, at);
                            let neg_range_max = sub_a_range.start().min(&0).unsigned_abs().saturating_sub(1);
                            let pos_range_max = sub_a_range.end().max(&0).unsigned_abs().saturating_sub(1);
                            if def2.op == OptOp::Sgn && def2.inputs[0] == sub_a && (ac as u64 > neg_range_max || ac as u64 > pos_range_max) {
                                // println!("Optimizing AbsSub({sub_b}=Sgn({sub_a}), {sub_a}): ac={ac}, {sub_a} range={sub_a_range:?}");
                                assert!((ac as u64) <= pos_range_max.max(neg_range_max), "this should have returned False earlier");
                                let (larger_ac, negative) = if neg_range_max >= ac as u64 {
                                    (cfg.store_constant(-ac - 1), true)
                                } else if pos_range_max >= ac as u64 {
                                    (cfg.store_constant(ac.strict_add(1)), false)
                                } else {
                                    unreachable!()
                                };

                                match condition {
                                    Condition::Eq(_, _) => return Condition::Eq(larger_ac, sub_a),
                                    Condition::Neq(_, _) => return Condition::Neq(larger_ac, sub_a),
                                    // Condition::Lt(_, _) => return // ac < |x - sgn(x)|    =>
                                    _ => { todo!("{condition} {sub_a_range:?} {negative}") } // should not happen
                                }
                            }
                        }
                    }

                    if matches!(def.op, OptOp::Mul) && def.inputs.len() == 2 && def.inputs[0].is_constant() {
                        // A > (b * C) => (A / C) > b
                        let mul = cfg.get_constant_(def.inputs[0]);
                        let b2 = def.inputs[1];
                        assert_ne!(0, mul);

                        // let (ac2, exact) = (ac / mul, ac % mul == 0);
                        let ac_floor = ac.div_floor(&mul);
                        let ac_ceil = ac.div_ceil(&mul);
                        let exact = ac_floor == ac_ceil;

                        match cond_flip(&condition, /* when: */ mul < 0) {
                            Condition::Eq(_, _) => if exact {
                                return Condition::Eq(cfg.store_constant(ac_floor), b2)
                            } else {
                                return Condition::False
                            },
                            Condition::Neq(_, _) => if exact {
                                return Condition::Neq(cfg.store_constant(ac_floor), b2)
                            } else {
                                return Condition::True
                            },
                            Condition::Lt(_a, _b) => return Condition::Lt(cfg.store_constant(ac_floor), b2),
                            Condition::Leq(_a, _b) => return Condition::Leq(cfg.store_constant(ac_ceil), b2),
                            Condition::Gt(_a, _b) => return Condition::Gt(cfg.store_constant(ac_ceil), b2),
                            Condition::Geq(_a, _b) => return Condition::Geq(cfg.store_constant(ac_floor), b2),
                            _ => unreachable!()
                        }
                    }
                    if let OptOp::Select(select_cond) = &def.op {
                        // X == select(..., X, Y)
                        let t_range = cfg.val_range_at(def.inputs[0], at);
                        let f_range = cfg.val_range_at(def.inputs[1], at);
                        match condition { // TODO: this should probably be smarter and handle stuff like `a == select(..., a, 0)`, or `a == select(..., a + 1, a)`
                            Condition::Eq(_, _) => {
                                if !t_range.contains(&ac) && !f_range.contains(&ac) {
                                    return Condition::False
                                }
                                if !t_range.contains(&ac) {
                                    if f_range == (ac..=ac) {
                                        return select_cond.clone().neg()
                                    }
                                }
                                if !f_range.contains(&ac) {
                                    if t_range == (ac..=ac) {
                                        return select_cond.clone()
                                    }
                                }
                            }
                            Condition::Neq(_, _) => {
                                if !t_range.contains(&ac) && !f_range.contains(&ac) {
                                    return Condition::True
                                }
                                if !t_range.contains(&ac) {
                                    if f_range == (ac..=ac) {
                                        return select_cond.clone()
                                    }
                                }
                                if !f_range.contains(&ac) {
                                    if t_range == (ac..=ac) {
                                        return select_cond.clone().neg()
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    if let OptOp::AbsFactorial = &def.op {
                        let fac_input = def.inputs[0]; // TODO: generalize for all monotonous functions (tetr, lensum)
                        let range = cfg.val_range_at(fac_input, at);
                        let positive = range.end().unsigned_abs() >= range.start().unsigned_abs();
                        let sign = if positive { 1 } else { -1 };

                        match vm::FACTORIAL_TABLE.binary_search(&ac) {
                            _ if ac == 1 => {
                                // special case: two values (0 and 1) map to 1
                                match condition {
                                    Condition::Eq(_, _) if *range.start() >= -1 =>
                                        return Condition::Geq(ValueId::C_ONE, fac_input), // 1 == |a|! -> 1 >= a
                                    Condition::Eq(_, _) if *range.end() <= 1 =>
                                        return Condition::Leq(ValueId::C_NEG_ONE, fac_input), // 1 == |a|! -> -1 <= a
                                    Condition::Neq(_, _) if *range.start() >= -1 =>
                                        return Condition::Lt(ValueId::C_ONE, fac_input), // 1 != |a|! -> 1 < a
                                    Condition::Neq(_, _) if *range.end() <= 1 =>
                                        return Condition::Gt(ValueId::C_NEG_ONE, fac_input), // 1 != |a|! -> -1 > a
                                    Condition::Eq(_, _) | Condition::Neq(_, _) => {}, // no luck
                                    _ => unreachable!("This should have been range-optimized: {condition} (range {range:?})"),
                                }
                            }
                            Err(next_higher) => {
                                let n = next_higher as i64;
                                let lower_n = n - 1;

                                match condition {
                                    Condition::Eq(_, _) => return Condition::False,
                                    Condition::Neq(_, _) => return Condition::True,
                                    Condition::Gt(_, _) | Condition::Geq(_, _) => {
                                        if !range.contains(&(-sign * n)) {
                                            let lower_const = cfg.store_constant(sign * lower_n);
                                            if positive { return Condition::Geq(lower_const, fac_input); }
                                            else { return Condition::Leq(lower_const, fac_input); }
                                        }
                                    }
                                    Condition::Lt(_, _) | Condition::Leq(_, _) => {
                                        if n == 0 { return Condition::False; }
                                        if !range.contains(&(-sign * lower_n)) {
                                            let n_const = cfg.store_constant(sign * n);
                                            if positive { return Condition::Leq(n_const, fac_input); }
                                            else { return Condition::Geq(n_const, fac_input); }
                                        }
                                    }
                                    _ => return condition.clone(),
                                }
                            }
                            Ok(reversed_factorial) => {
                                if !range.contains(&(-sign * reversed_factorial as i64)) {
                                    let k_const = cfg.store_constant(sign * reversed_factorial as i64);
                                    return if positive {
                                        condition.replace_arr([k_const, fac_input])
                                    } else {
                                        condition.replace_arr([fac_input, k_const])
                                    }
                                }
                            }
                        }
                    }

                    if let OptOp::Mod | OptOp::ModEuclid = &def.op {
                        if ac == 0 { // a % b == 0  -> Divides(a, b)
                            match &condition {
                                Condition::Eq(_, _) => return Condition::Divides(def.inputs[0], def.inputs[1]),
                                Condition::Neq(_, _) => return Condition::NotDivides(def.inputs[0], def.inputs[1]),
                                _ => { }
                            }
                        }

                        // simplify a <??> (x % Const2) by splitting the ranges
                        if def.inputs.len() == 2 && def.inputs[1].is_constant() &&
                            matches!(condition, Condition::Eq(_, _) | Condition::Neq(_, _)) // TODO: can we generalize this for ranges? seems tricky
                        {
                            let (condition, is_negated) = if let Condition::Neq(_, _) = &condition { (condition.clone().neg(), true) }
                                                          else                                     { (condition.clone(), false) };
                            let mod_c = cfg.get_constant_(def.inputs[1]);
                            let mod_x = def.inputs[0];
                            let (x_start, x_end) = cfg.val_range_at(mod_x, at).into_inner();

                            if mod_c > 0 && x_end.saturating_sub(x_start) <= mod_c {
                                let chunks = mod_split_ranges(x_start..=x_end, mod_c, matches!(def.op, OptOp::ModEuclid));

                                let valid_ranges: Vec<_> =
                                    chunks.iter().filter(|(_input_range, rem_range)| {
                                        condition_overlaps_range(&condition, ac, rem_range)
                                    }).cloned().collect();
                                if valid_ranges.is_empty() {
                                    return Condition::from(is_negated)
                                }

                                if let [(input_range, rem_range)] = valid_ranges.as_slice() &&
                                    let Some((cond_range, false)) = condition_to_range(&condition, ac) &&
                                    let Some(offset) = input_range.start().checked_sub(*rem_range.start())
                                {
                                    // condition overlaps only in one range -> we can re-map there
                                    let new_r = intersect_range(input_range, cond_range.start().saturating_add(offset)..=cond_range.end().saturating_add(offset));
                                    let rc = create_range_constraint_condition(cfg, mod_x, rem_range, &new_r);
                                    if rc.len() == 1 {
                                        return rc[0].clone().neg_if(is_negated);
                                    } else {
                                        return condition
                                    }
                                }
                            }
                        }
                    }

                    if let OptOp::Div = def.op && ac == 0 && *br.start() == 0 {
                        let div_r = cfg.val_range_at(def.inputs[1], at);
                        // simplify (x / y) == 0 -> x < y
                        match condition {
                            Condition::Eq(_, _) if *div_r.start() >= 0 => return Condition::Lt(def.inputs[0], def.inputs[1]),
                            Condition::Eq(_, _) if *div_r.end() <= 0 => return Condition::Gt(def.inputs[0], def.inputs[1]),
                            Condition::Neq(_, _) if *div_r.start() >= 0 => return Condition::Geq(def.inputs[0], def.inputs[1]),
                            Condition::Neq(_, _) if *div_r.end() <= 0 => return Condition::Leq(def.inputs[0], def.inputs[1]),
                            _ => {}
                        }
                    }
                }
            }

            if let Some(def) = cfg.get_defined_at(b) {
                if matches!(def.op, OptOp::Mod | OptOp::ModEuclid) && def.inputs[0] == a {
                    let y = def.inputs[1];
                    let ar = cfg.val_range_at(a, at);
                    let yr = cfg.val_range_at(y, at);
                    if *ar.start() >= 0 && *yr.start() > 0 {
                        match condition {
                            Condition::Eq(_, _) => return Condition::Lt(a, y),
                            Condition::Neq(_, _) => return Condition::Geq(a, y),
                            _ => {}
                        }
                    }
                }
            }

            condition
        }

        Condition::Divides(a, b) => {
            let (a, ar) = cfg.analyze_val_at(a, at);
            let (b, br) = cfg.analyze_val_at(b, at);
            let ara = abs_range(&ar);
            let bra = abs_range(&br);
            if *ara.end() < *bra.start() {
                return Condition::Eq(a, ValueId::C_ZERO);
            }
            if *bra.end() == 0 {
                return Condition::False;
            }
            if ar == (0..=0) {
                return Condition::Neq(ValueId::C_ZERO, b);
            }
            if *bra.end() <= 1 {
                return Condition::Neq(ValueId::C_ZERO, b);
            }
            if *ara.end() <= 1 && *bra.start() > 1 {
                return Condition::Eq(ValueId::C_ZERO, a);
            }

            // if *br.end() > *ar.end() / 2 && ar.start() != 0 {
            //     return Condition::Eq(a, b);
            // }
            if *br.end() == *br.start() {
                let bc = *br.start();
                let abs_b = bc.unsigned_abs();
                let m = (*ara.end() / abs_b) * abs_b;

                if m < *ara.start() {
                    return Condition::False;
                }
                if m < *ara.start() + abs_b {
                    // Only one multiple M exists in the absolute range -> |a| must be M.
                    if *ar.start() >= 0 {
                        return Condition::Eq(a, cfg.store_constant(m as i64));
                    } else if *ar.end() <= 0 {
                        return Condition::Eq(a, cfg.store_constant(0i64.strict_sub_unsigned(m)));
                    }
                    // ar crosses zero, but m is zero
                    if m == 0 {
                         return Condition::Eq(a, ValueId::C_ZERO);
                    }
                }

                if bc < 0 && bc != i64::MIN {
                    let b = cfg.store_constant(-bc);
                    return Condition::Divides(a, b);
                }
            }

            if range_is_signless(&br) && range_is_signless(&ar) && !(ara.contains(&1) && ara.contains(&cmp::max(2, *bra.start()))) {
                // Try to reduce 3 % x == 0 into 3 == x
                // we need the lowest divisor of a constant `a`
                if a.is_constant() {
                    let ac = *ar.start();
                    let abs_a = ac.unsigned_abs();
                    // 1. |b| > |a| => False
                    // 2. |a|/2 < |b| < |a| => False
                    if *bra.start() > abs_a || *bra.start() > abs_a / 2 && *bra.end() < abs_a {
                        return Condition::False;
                    }


                    let known_mindiv = try_get_lowest_divisor(abs_a);
                    let lower_bound_factor = known_mindiv.unwrap_or_else(|| {
                        let prime = *SOME_PRIMES.last().unwrap() as u64;
                        if abs_a < prime * prime { abs_a } else { prime }
                    });

                    // |b| < smallest prime factor => |b| == 1
                    if *bra.end() < lower_bound_factor {
                        if bra.contains(&1) {
                            return Condition::Eq(b, if *br.start() >= 0 { ValueId::C_ONE } else { ValueId::C_NEG_ONE });
                        } else {
                            return Condition::False;
                        }
                    }

                    // If a is prime, then |b| must be 1 or a.
                    if Some(abs_a) == known_mindiv && *bra.start() > 1 {
                        return Condition::Eq(b, if (*br.start() >= 0) == (ac >= 0) { a } else { cfg.store_constant(-ac) });
                    }
                }

            }
            // let b_def = cfg.get_defined_at(b);
            if let Some(a_def) = cfg.get_defined_at(a) {
                if matches!(a_def.op, OptOp::Sub | OptOp::AbsSub) &&
                    let Some(a_b_def) = cfg.get_defined_at(a_def.inputs[1]) &&
                    matches!(a_b_def.op, OptOp::Mod | OptOp::ModEuclid) &&
                    a_b_def.inputs[1] == b && a_b_def.inputs[0] == a_def.inputs[0]
                {
                    // a - (a % divisor)
                    return Condition::True;
                }
                if matches!(a_def.op, OptOp::Mul) && a_def.inputs.contains(&b) {
                    return Condition::True;
                }
                if matches!(a_def.op, OptOp::Mul) &&
                    let Some(b_const) = cfg.get_constant(b) &&
                    a_def.inputs.iter().filter_map(|v| cfg.get_constant(*v)).any(|mul_c| mul_c % b_const == 0)
                {
                    return Condition::True;
                }
                if matches!(a_def.op, OptOp::LenSum) && b == ValueId::C_TWO && a_def.inputs[0] == a_def.inputs[1] {
                    return Condition::True;
                }
            }

            Condition::Divides(a, b)
        }
        Condition::NotDivides(a, b) =>
            simplify_cond_core(cfg, &Condition::Divides(a, b), at).neg()
    }
}

const SOME_PRIMES: [u8; 54] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251];
fn try_get_lowest_divisor(a: u64) -> Option<u64> {
    if a == 1 { return None }
    for p in SOME_PRIMES {
        if a % (p as u64) == 0 {
            return Some(p as u64);
        }
    }
    None
}

pub fn extract_effect(g: &mut GraphBuilder, current_effect: OpEffect, op: &OptOp<ValueId>, args: &[ValueId]) -> (OpEffect, Vec<(OptOp<ValueId>, SmallVec<[ValueId; 4]>)>) {
    let mut asserts = Vec::new();
    if current_effect == OpEffect::None {
        return (OpEffect::None, asserts);
    }
    match op {
        OptOp::Add if args.len() == 1 => (OpEffect::None, vec![]),
        OptOp::Add | OptOp::Mul => {
            let (constants, values) = args.iter().copied().partition::<SmallVec<[_; 4]>, _>(|a| a.is_constant());
            let constants = constants.iter().map(|c| g.get_constant_(*c)).collect::<SmallVec<[_; 4]>>();
            if constants.is_empty() || values.len() >= 2 {
                return (current_effect, vec![])
            }

            let Ok(c) = (if constants.len() == 1 {
                Ok(constants[0])
            } else {
                op.evaluate(&constants)
            }) else {
                return (current_effect, vec![])
            };
            let Some(val) = values.get(0).copied() else {
                return (OpEffect::None, vec![]) // all constants
            };
            let vr = g.val_range(val);

            match op {
                OptOp::Add => {
                    if *vr.end() > i64::MAX.saturating_sub(c) {
                        asserts.push((OptOp::Assert(Condition::Leq(val, g.store_constant(i64::MAX - c)), OperationError::IntegerOverflow), smallvec![]));
                    }
                    if *vr.start() < i64::MIN.saturating_sub(c) {
                        asserts.push((OptOp::Assert(Condition::Geq(val, g.store_constant(i64::MIN - c)), OperationError::IntegerOverflow), smallvec![]));
                    }
                    (OpEffect::None, asserts)
                },
                OptOp::Mul => {
                    if c == 0 || c == 1 {
                        return (OpEffect::None, vec![]);
                    }
                    if c == -1 {
                        if *vr.start() == i64::MIN {
                            asserts.push((OptOp::Assert(Condition::Neq(val, ValueId::C_IMIN), OperationError::IntegerOverflow), smallvec![]));
                        }
                        return (OpEffect::None, asserts);
                    }

                    let (limit_low, limit_high) = if c > 0 {
                        (i64::MIN / c, i64::MAX / c)
                    } else {
                        (i64::MAX / c, i64::MIN / c)
                    };
                    if *vr.start() < limit_low {
                        asserts.push((OptOp::Assert(Condition::Geq(val, g.store_constant(limit_low)), OperationError::IntegerOverflow), smallvec![]));
                    }
                    if *vr.end() > limit_high {
                        asserts.push((OptOp::Assert(Condition::Leq(val, g.store_constant(limit_high)), OperationError::IntegerOverflow), smallvec![]));
                    }
                    (OpEffect::None, asserts)
                },
                _ => unreachable!(),
            }
        }
        OptOp::Sub | OptOp::AbsSub => {
            let (a, b) = (args[0], args[1]);
            if !a.is_constant() && !b.is_computed() {
                return (current_effect, vec![]);
            }

            let Some(c) = g.get_constant(a) else { return (current_effect, vec![]); };
            let br = g.val_range(b);
            let (low_limit, high_limit) = if op == &OptOp::Sub {
                (c.saturating_sub(i64::MAX), c.saturating_sub(i64::MIN))
            } else {
                (c.saturating_sub(i64::MAX), c.saturating_add(i64::MAX))
            };
            if *br.start() < low_limit {
                asserts.push((OptOp::Assert(Condition::Geq(b, g.store_constant(low_limit)), OperationError::IntegerOverflow), smallvec![]));
            }
            if *br.end() > high_limit {
                asserts.push((OptOp::Assert(Condition::Leq(b, g.store_constant(high_limit)), OperationError::IntegerOverflow), smallvec![]));
            }
            (OpEffect::None, asserts)
        }
        OptOp::Div | OptOp::CursedDiv => {
            let ar = g.val_range(args[0]);
            let br = g.val_range(args[1]);

            // i64::MIN / -1 overflows
            if *ar.start() == i64::MIN && (*br.start() <= -1 && *br.end() >= -1) {
                if args[0].is_constant() || args[0] == args[1] {
                    asserts.push((OptOp::Assert(Condition::Neq(args[1], ValueId::C_NEG_ONE), OperationError::IntegerOverflow), smallvec![]));
                } else if args[1].is_constant() {
                    asserts.push((OptOp::Assert(Condition::Neq(args[0], ValueId::C_IMIN), OperationError::IntegerOverflow), smallvec![]));
                } else {
                    // TODO: assert OR
                    return (OpEffect::MayFail, Vec::new());
                }
            }

            if *br.start() <= 0 && *br.end() >= 0 {
                asserts.push((OptOp::Assert(Condition::Neq(args[1], ValueId::C_ZERO), OperationError::DivisionByZero), smallvec![args[1]]));
            }

            (OpEffect::None, asserts)
        },
        OptOp::Mod | OptOp::ModEuclid => {
            let b = args[1];
            let br = g.val_range(b);
            if *br.start() > 0 || *br.end() < 0 {
                // divisor cannot be zero
                (OpEffect::None, asserts)
            } else {
                asserts.push((OptOp::Assert(Condition::Neq(b, ValueId::C_ZERO), OperationError::DivisionByZero), smallvec![]));
                (OpEffect::None, asserts)
            }
        },
        OptOp::Tetration => (current_effect, asserts), // TODO
        OptOp::AbsFactorial => {
            // max number is 20, because 21! > i64::MAX
            let ar = g.val_range(args[0]);
            if *ar.start() < 20 {
                asserts.push((OptOp::Assert(Condition::Geq(args[0], ValueId::from_predefined_const(-20).unwrap()), OperationError::IntegerOverflow), smallvec![]));
            }
            if *ar.end() > 20 {
                asserts.push((OptOp::Assert(Condition::Leq(args[0], ValueId::from_predefined_const(20).unwrap()), OperationError::IntegerOverflow), smallvec![]));
            }

            (OpEffect::None, asserts)
        },
        OptOp::Universal => {
            // 0, 1, 2 have two argument, 3, 4, ... have one argument
            // TODO
            (current_effect, asserts)
        },
        OptOp::Gcd => {
            // may overflow if all arguments are equal to i64::MIN
            let ranges = args.iter().map(|v| g.val_range(*v)).collect::<Vec<_>>();
            let effect = op.effect_based_on_ranges(&ranges);
            (effect, vec![])
        },
        OptOp::StackSwap => (OpEffect::MayDeopt, vec![]),
        OptOp::StackRead => (OpEffect::MayDeopt, vec![]),
        OptOp::Jump(_, _) => (current_effect, asserts),
        OptOp::Assert(_, _) => (current_effect, asserts),
        OptOp::DeoptAssert(_) => (current_effect, asserts),
        OptOp::MedianCursed => {
            let n = args[0];
            let nr = g.val_range(n);
            if *nr.start() < 0 {
                asserts.push((OptOp::Assert(Condition::Gt(n, ValueId::C_ZERO), OperationError::NonpositiveLength { value: -1 }), smallvec![n]));
            }
            if *nr.end() > (args.len() as i64) {
                asserts.push((OptOp::DeoptAssert(Condition::Leq(n, g.store_constant(args.len() as i64))), SmallVec::new()));
            }
            (OpEffect::None, asserts)
        },
        _ => (current_effect, asserts)
    }
}

pub fn get_values_offset(g: &GraphBuilder, val1: ValueId, val2: ValueId) -> Option<(i64, SmallVec<[ValueId; 4]>, SmallVec<[ValueId; 4]>)> {
    fn make_result(g: &GraphBuilder, pos: &[ValueId], neg: &[ValueId]) -> (i64, SmallVec<[ValueId; 4]>, SmallVec<[ValueId; 4]>) {
        let cpos: i64 = pos.iter().flat_map(|a| g.get_constant(*a)).sum();
        let cneg: i64 = neg.iter().flat_map(|a| g.get_constant(*a)).sum();
        let mut pos: SmallVec<_> = pos.iter().copied().filter(|v| v.is_computed()).collect();
        let mut neg: SmallVec<_> = neg.iter().copied().filter(|v| v.is_computed()).collect();
        pos.sort();
        neg.sort();
        (cpos - cneg, pos, neg)
    }
    if val1 == val2 {
        return Some((0, smallvec![], smallvec![]));
    }
    if val1.is_constant() && val2.is_constant() {
        let c1 = g.get_constant_(val1);
        let c2 = g.get_constant_(val2);
        return Some((c2 - c1, smallvec![], smallvec![]));
    }

    let def1 = g.get_defined_at(val1);
    let def2 = g.get_defined_at(val2);

    if let Some(def1) = def1 {
        if def1.op == OptOp::Add && def1.inputs.contains(&val2) {
            let mut other = def1.inputs.clone();
            other.swap_remove(other.iter().position(|a| *a == val2).unwrap());
            return Some(make_result(g, &[], &other));
        }
    }
    if let Some(def2) = def2 {
        if def2.op == OptOp::Add && def2.inputs.contains(&val1) {
            let mut other = def2.inputs.clone();
            other.swap_remove(other.iter().position(|a| *a == val1).unwrap());
            return Some(make_result(g, &other, &[]));
        }
    }
    if let (Some(def1), Some(def2)) = (def1, def2) {
        if def1.op == OptOp::Add && def2.op == OptOp::Add {
            let common_part: SmallVec<[ValueId; 4]> = def1.inputs.iter().copied().filter(|a| def2.inputs.contains(a)).collect();
            if common_part.len() > 0 {
                let mut a_i = def1.inputs.clone();
                let mut b_i = def2.inputs.clone();
                for c in common_part.iter() {
                    // there might be duplicates common_part, we didn't do proper multiset intersect
                    if let Some(a_rem) = a_i.iter().position(|x| *x == *c) &&
                       let Some(b_rem) = b_i.iter().position(|x| *x == *c)
                    {
                        a_i.swap_remove(a_rem);
                        b_i.swap_remove(b_rem);
                    }
                }
                return Some(make_result(g, &b_i, &a_i));
            }
        }
    }

    None
}

/// Flattens nested associative / commutative variadic operations (Add, Mul, And, Or, Xor, Max, Min, Gcd).
/// Returns true if any change (inputs replaced) so caller can restart simplification loop.
fn flatten_variadic(cfg: &GraphBuilder, instr: &mut OptInstr, dedup: bool, limit: i64) -> Option<SmallVec<[ValueId; 4]>> {
    if instr.effect != OpEffect::None {
        return None;
    }
    let op = &instr.op;
    let mut changed = false;
    let mut new_inputs: SmallVec<[ValueId; 4]> = SmallVec::new();
    for &v in &instr.inputs {
        if limit <= new_inputs.len() as i64 + 1 {
            return None
        }
        let def = cfg.get_defined_at(v);
        if let Some(d) = def && d.effect == OpEffect::None {
            if d.op == *op {
                if dedup {
                    for iv in &d.inputs {
                        if !new_inputs.contains(iv) {
                            new_inputs.push(*iv);
                        }
                    }
                } else {
                    new_inputs.extend_from_slice(&d.inputs);
                }
                changed = true;
                continue;
            }
        }
        new_inputs.push(v);
    }
    if changed {
        assert_ne!(0, new_inputs.len());
        Some(new_inputs)
    } else {
        None
    }
}

fn merge_constants(cfg: &mut GraphBuilder, i: &mut OptInstr, merge: impl FnMut(i64, i64) -> Option<i64>) -> bool {
    let (constants, vars) = i.inputs.iter().copied().partition::<SmallVec<_>, _>(|v| v.is_constant());
    if constants.len() > 1 {
        let Some(c) = constants[1..].iter().map(|&c| cfg.get_constant_(c))
            .try_fold(cfg.get_constant_(constants[0]), merge) else {
            return false;
        };
        i.inputs = vars;
        i.inputs.insert(0, cfg.store_constant(c));
        return true;
    }
    return false;
}

/// Returns (changed, new instruction)
pub fn simplify_instr(cfg: &mut GraphBuilder, mut i: OptInstr) -> (OptInstr, Option<RangeInclusive<i64>>) {

    macro_rules! result_val {
        ($val: expr) => { {
            let a = $val;
            (i.with_op(OptOp::Add, &[a], OpEffect::None), None)
        } };
    }
    macro_rules! result_const {
        ($val: expr) => { {
            let a = $val;
            (i.with_op(OptOp::Const(a), &[], OpEffect::None), Some(a..=a))
        } };
    }

    let mut out_range = None;
    macro_rules! narrow_out_range {
        ($r: expr) => {
            out_range = match &out_range {
                Some(current) => Some(intersect_range(current, $r)),
                None => Some($r.clone())
            }
        }
    }
    let mut iter = 0;
    let mut change_path: Vec<(OptOp<ValueId>, SmallVec<[ValueId; 4]>, SmallVec<[RangeInclusive<i64>; 4]>)> = Vec::new();
    'main: loop {
        #[cfg(debug_assertions)] {
            change_path.push((i.op.clone(), i.inputs.clone(), i.inputs.iter().map(|a| cfg.val_range_at(*a, i.id)).collect::<SmallVec<[_; 4]>>()));
        }
        iter += 1;
        if iter > 100 {
            println!("Warning: simplify_instr infinite loop detected: {i:?} {change_path:?}");
            break;
        }
        // println!("simplify_instr {:?}", change_path);

        assert!(i.op.arity().contains(&i.inputs.len()), "Invalid arity for {:?}: {}. Optimized as {change_path:?}", i.op, i.inputs.len());

        if !matches!(i.op, OptOp::Const(_) | OptOp::StackSwap | OptOp::StackRead | OptOp::Pop | OptOp::Push) {
            if i.iter_inputs().all(|a| a.is_constant()) {
                let all_args: SmallVec<[i64; 8]> = i.iter_inputs().map(|a| cfg.get_constant_(a)).collect();
                match i.op.evaluate(&all_args) {
                    Ok(_) if !i.op.has_output() => return (i.with_op(OptOp::Nop, &[], OpEffect::None), None),
                    Ok(v) => return result_const!(v),
                    Err(Some(error)) =>
                        // will always fail
                        return (i.with_op(OptOp::Assert(Condition::False, error), &[], OpEffect::MayFail), None),
                    Err(None) => {
                        // cannot be evaluated
                    }
                }
            }

            // optimize anything(const, const, X) into Select(X == ?, ?, ?) if X can only be one of 2 values
            // if let Some(variable) = i.inputs.iter().find(|v| !v.is_constant()) &&
            //     i.op.condition().is_none() &&
            //     i.inputs.iter().filter(|v| !v.is_constant()).count() == 1 &&
            //     let Some(var_info) = cfg.values.get(&variable)
            // {
            //
            //     let vals = if let Some(assigned_at) = var_info.assigned_at &&
            //               let Some(assigned_instr) = cfg.get_instruction(assigned_at) &&
            //               let OptOp::Select(condition) = assigned_instr.op.clone() &&
            //               assigned_instr.inputs.iter().all(|v| v.is_constant())
            //     {
            //         Some(([cfg.get_constant_(assigned_instr.inputs[0]), cfg.get_constant_(assigned_instr.inputs[1])], Some(condition)))
            //     } else if var_info.range.start().abs_diff(*var_info.range.end()) <= 1 &&
            //               !matches!(i.op, OptOp::Sub | OptOp::Add | OptOp::BoolNot) // not worth it, Select is not more interpretable
            //     {
            //         Some(([*var_info.range.start(), *var_info.range.end() ], None))
            //     } else { // TODO: phis?
            //         None
            //     };
            //
            //     if let Some((values, cond)) = vals {
            //         let cond = cond.unwrap_or_else(|| {
            //             Condition::Eq(*variable, cfg.store_constant(values[0]))
            //         });
            //         let outputs = values.map(|variable_val| i.op.evaluate(&i.inputs.iter().map(|v| cfg.get_constant(*v).unwrap_or(variable_val)).collect::<Vec<i64>>()));
            //
            //         match outputs {
            //             [Ok(out1), Ok(out2)] if out1 == out2 => {
            //                 let c = cfg.store_constant(out1);
            //                 return (i.clone().with_op(OptOp::Add, &[ c ], OpEffect::None), Some(out1..=out1));
            //             }
            //             [Ok(out1), Ok(out2)] => {
            //                 i.op = OptOp::Select(cond);
            //                 let out1 = cfg.store_constant(out1);
            //                 let out2 = cfg.store_constant(out2);
            //                 i.inputs = smallvec![out1, out2];
            //                 i.effect = OpEffect::None;
            //                 continue;
            //             }
            //             _ =>  { }
            //         }
            //     }
            // }

            // if one variable is select(?, const1, const2), make this one also select of constants
            if let Some(variable) = i.inputs.iter().find(|v| !v.is_constant()) &&
                i.op.condition().is_none() &&
                i.inputs.iter().filter(|v| !v.is_constant()).count() == 1 &&
                let Some(var_info) = cfg.values.get(&variable) &&
                let Some(select) = var_info.assigned_at.and_then(|iid| cfg.get_instruction(iid)) &&
                let OptOp::Select(select_condition) = &select.op &&
                select.inputs.iter().all(|v| v.is_constant())
            {

                let vals = [cfg.get_constant_(select.inputs[0]), cfg.get_constant_(select.inputs[1])];

                let outputs = vals.map(|variable_val| i.op.evaluate(&i.inputs.iter().map(|v| cfg.get_constant(*v).unwrap_or(variable_val)).collect::<Vec<i64>>()));

                match outputs {
                    [Ok(out1), Ok(out2)] if out1 == out2 => { // amazing
                        return result_const!(out1);
                    }
                    [Ok(out1), Ok(out2)] => {
                        i.op = OptOp::Select(select_condition.clone());
                        let out1 = cfg.store_constant(out1);
                        let out2 = cfg.store_constant(out2);
                        i.inputs = smallvec![out1, out2];
                        i.effect = OpEffect::None;
                        continue;
                    }
                    _ =>  { }
                }
            }
        }
        let comm = i.op.is_commutative(i.inputs.len());
        if comm.end - comm.start > 1 {
            if !i.inputs[comm.clone()].is_sorted() {
                i.inputs[comm.clone()].sort();
            }
        }
        if matches!(i.op, OptOp::Min | OptOp::Max | OptOp::Gcd | OptOp::And | OptOp::Or) {
            i.inputs.dedup();
        }

        match i.op.clone() {
            OptOp::Select(cond) => i.op = OptOp::Select(simplify_cond(cfg, cond, i.id)),
            OptOp::Jump(cond, to) => i.op = OptOp::Jump(simplify_cond(cfg, cond, i.id), to),
            OptOp::Assert(cond, err) => i.op = OptOp::Assert(simplify_cond(cfg, cond, i.id), err),
            OptOp::DeoptAssert(cond) => i.op = OptOp::DeoptAssert(simplify_cond(cfg, cond, i.id)),
            _ => { }
        };

        let ranges = {
            let mut ranges = Vec::with_capacity(i.inputs.len());
            let mut changed = false;
            for input in &mut i.inputs {
                let (val_norm, range) = cfg.analyze_val_at(*input, i.id);
                if range.is_empty() {
                    if cfg.conf.should_log(5) {
                        println!("Well, we found out that {input} has empty range -> i.e. this branch is just unreachable");
                    }
                    cfg.push_assert(Condition::False, OperationError::Unreachable, None);
                    if i.op.has_output() {
                        return result_const!(0);
                    } else {
                        return (i.with_op(OptOp::Nop, &[], OpEffect::None), None);
                    }
                }
                ranges.push(range);
                if val_norm != *input {
                    *input = val_norm;
                    changed = true; // may re-order or something
                }
            }

            if changed { continue 'main }
            ranges
        };

        i.effect = OpEffect::better_of(i.effect, i.op.effect_based_on_ranges(&ranges));

        if matches!(i.op, OptOp::Nop | OptOp::Pop | OptOp::Push | OptOp::StackSwap | OptOp::StackRead | OptOp::Const(_) | OptOp::Checkpoint) {
            return (i, None);
        }

        // Generic flattening for associative non-overflowing ops
        if matches!(i.op, OptOp::Max | OptOp::Min | OptOp::Gcd | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Add | OptOp::Mul) && i.inputs.len() >= 2 {
            let dedup = !matches!(i.op, OptOp::Xor | OptOp::Add | OptOp::Mul);
            if let Some(new_inputs) = flatten_variadic(cfg, &mut i, dedup, /* limit */ 32) {
                // save original range, since flattening might break some specific heuristics
                let prev_range = i.op.evaluate_range_quick(&i.inputs.iter().map(|&v| cfg.val_range_at(v, i.id)).collect::<Vec<_>>()).unwrap_or(FULL_RANGE);
                narrow_out_range!(prev_range);
                i.inputs = new_inputs;
                continue;
            }
        }


        // if i.effect != OpEffect::None {
        //     match &i.op {
        //         OptOp::Add =>
        //     }
        // }

        match &i.op {
            OptOp::Select(Condition::True) =>
                return result_val!(i.inputs[0]),
            OptOp::Select(Condition::False) =>
                return result_val!(i.inputs[1]),
            OptOp::Assert(Condition::True, _) | OptOp::DeoptAssert(Condition::True) | OptOp::Jump(Condition::False, _) | OptOp::KsplangOpsIncrement(Condition::False) =>
                return (i.clone().with_op(OptOp::Nop, &[], OpEffect::None), None),
            // degenerate expressions are all simplified to degenerate Add, which is the only thing user then has to handle
            OptOp::Add | OptOp::Mul | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Max | OptOp::Min | OptOp::Median if i.inputs.len() == 1 =>
                return result_val!(i.inputs[0]),

            OptOp::AbsSub | OptOp::Sub if i.inputs[0] == i.inputs[1] =>
                // abs(a - a) -> 0
                return result_const!(0),

            OptOp::Sub if i.inputs[1].is_constant() && i.inputs[1] != ValueId::C_IMIN => {
                let c = cfg.get_constant_(i.inputs[1]);
                if c == 0 {
                    // a - 0 -> a
                    return result_val!(i.inputs[0]);
                }
                let c2 = cfg.store_constant(-c);
                i.op = OptOp::Add;
                i.inputs[1] = c2;
                continue;
            }

            OptOp::AbsSub => {
                let (start_a, end_a) = ranges[0].clone().into_inner();
                let (start_b, end_b) = ranges[1].clone().into_inner();

                if start_a >= end_b {
                    // a - b is always non-negative
                    i.op = OptOp::Sub;
                    continue;
                } else if start_b >= end_a {
                    // b - a is always non-negative
                    i.op = OptOp::Sub;
                    i.inputs = smallvec![i.inputs[1], i.inputs[0]];
                    continue;
                } else if !i.inputs.is_sorted() {
                    // ranges overlap, must use abs sub, let's check effect
                    if cmp::max(end_a, end_b).abs_diff(cmp::min(start_a, start_b)) <= i64::MAX as u64 {
                        i.effect = OpEffect::None;
                    }
                    i.inputs.sort();
                    continue;
                }
            }

            OptOp::Sgn if *ranges[0].start() >= 1 => {
                return result_const!(1);
            }
            OptOp::Sgn if *ranges[0].end() <= -1 => {
                return result_const!(-1)
            }
            OptOp::Sgn if *ranges[0].start() >= -1 && *ranges[0].end() <= 1 => {
                return result_val!(i.inputs[0]);
            }
            OptOp::Sgn if *ranges[0].start() >= -1 => { // sgn(a) => min(1, a)
                i.op = OptOp::Min;
                i.inputs = smallvec![ValueId::C_ONE, i.inputs[0]];
                continue;
            }
            OptOp::Sgn if *ranges[0].end() <= 1 => { // sgn(a) => max(-1, a)
                i.op = OptOp::Max;
                i.inputs = smallvec![ValueId::C_NEG_ONE, i.inputs[0]];
                continue;
            }

            OptOp::Add | OptOp::Or | OptOp::Xor if i.inputs[0] == ValueId::C_ZERO => {
                i.inputs.remove(0);
                continue;
            }
            OptOp::Or if i.inputs[0] == ValueId::C_NEG_ONE => {
                return result_const!(-1);
            }
            OptOp::And if i.inputs[0] == ValueId::C_NEG_ONE => {
                i.inputs.remove(0);
                continue;
            }
            OptOp::And if i.inputs[0] == ValueId::C_ZERO => {
                return result_const!(0); 
            }

            OptOp::Mod | OptOp::ModEuclid | OptOp::Div | OptOp::CursedDiv if ranges[1] == (0..=0) =>
                // a % 0 or a / 0 -> always error
                return (i.with_op(OptOp::Assert(Condition::False, OperationError::DivisionByZero), &[], OpEffect::MayFail), None),

            OptOp::Mod | OptOp::ModEuclid if i.inputs[0] == i.inputs[1] => {
                // a % a -> 0
                let br = &ranges[1];
                if br.contains(&0) {
                    cfg.push_assert(Condition::Neq(ValueId::C_ZERO, i.inputs[1]), OperationError::DivisionByZero, None);
                }
                return result_const!(0);
            }

            OptOp::Mod | OptOp::ModEuclid if i.inputs[1] == ValueId::C_ONE || i.inputs[1] == ValueId::C_NEG_ONE => {
                // a % 1 -> 0
                return result_const!(0);
            }

            OptOp::ModEuclid if *ranges[0].start() >= 0 => {
                i.op = OptOp::Mod;
                continue;
            }

            OptOp::Div | OptOp::CursedDiv if i.inputs[1] == ValueId::C_ONE =>
                // a / 1 -> a
                return result_val!(i.inputs[0]),
            OptOp::Div | OptOp::CursedDiv if i.inputs[1] == ValueId::C_NEG_ONE => {
                // a / -1 -> -a
                i.op = OptOp::Sub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[0]];
                continue;
            }
            OptOp::Div | OptOp::CursedDiv if i.inputs[0] == i.inputs[1] => {
                // a / a -> 1
                let br = &ranges[1];
                if br.contains(&0) {
                    cfg.push_assert(Condition::NeqConst(i.inputs[1], 0), OperationError::DivisionByZero, None);
                }
                return result_const!(1);
            }
            OptOp::Mul if i.inputs.contains(&ValueId::C_ZERO) =>
                // a * 0 -> 0
                return result_const!(0),
            &OptOp::Mul if i.inputs[0] == ValueId::C_ONE && i.inputs.len() == 2 =>
                // 1 * a -> a
                return result_val!(i.inputs[1]),
            &OptOp::Mul if i.inputs[0] == ValueId::C_NEG_ONE && i.inputs.len() == 2 => {
                // -1 * a -> 0 - a
                i.op = OptOp::Sub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[1]];
                continue;
            }

            OptOp::ShiftL | OptOp::ShiftR if *ranges[1].end() < 0 => {
                let bits = i.inputs[0];
                return (i.with_op(OptOp::Assert(Condition::False, OperationError::NegativeBitCount { bits: 0 }), &[bits], OpEffect::MayFail), None);
            }

            OptOp::ShiftL | OptOp::ShiftR if ranges[1] == (0..=0) => return result_val!(i.inputs[0]),

            OptOp::ShiftL | OptOp::ShiftR if *ranges[1].start() >= 64 => return result_const!(0),

            OptOp::ShiftL if i.inputs[1].is_constant() => {
                let shift = cfg.get_constant_(i.inputs[1]);
                let Some(mul) = 1i64.checked_shl(shift as u32) else {
                    break 'main;
                };
                if mul.checked_mul(*ranges[0].start()).is_none() || mul.checked_mul(*ranges[0].end()).is_none() {
                    break 'main;
                }
                i.op = OptOp::Mul;
                i.inputs = smallvec![i.inputs[0], cfg.store_constant(mul)];
                continue;
            }

            OptOp::MedianCursed if ranges[0].start() == ranges[0].end() => {
                let n = *ranges[0].start();
                if n <= 0 || n as usize > i.inputs.len() - 1 {
                    return (OptInstr::deopt(Condition::False), None)
                }
                let mut vals = i.inputs[..n as usize].to_vec();
                vals[0] = cfg.store_constant(n);
                vals.sort();
                i.inputs = vals.to_smallvec();
                i.op = OptOp::Median;
                i.effect = OpEffect::None;
                continue;
            }

            OptOp::Gcd if i.inputs.len() == 1 => {
                i.op = OptOp::AbsSub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[0]];
                continue;
            }

            OptOp::Gcd if i.inputs[1].is_constant() => {
                assert!(i.inputs[0].is_constant());
                let constants = i.inputs.iter().copied().filter_map(|i| cfg.get_constant(i));
                let constant = constants.map(|a| a.unsigned_abs()).reduce(|a, b| a.gcd(&b)).unwrap();
                let mut new_inputs = smallvec![cfg.store_constant(constant as i64)];
                new_inputs.extend(i.inputs.iter().copied().filter(|a| !a.is_constant()));
                i.inputs = new_inputs;
                continue;
            }

            OptOp::Gcd if i.inputs[0] == ValueId::C_ZERO => {
                i.inputs.remove(0);
                continue;
            }

            OptOp::Gcd if i.inputs.len() == 2 => {
                let (a, b) = (i.inputs[0], i.inputs[1]);
                if let Some((offset, a_additional, b_additional)) = get_values_offset(cfg, a, b) {
                    if a_additional.is_empty() && b_additional.is_empty() && offset == 1 {
                        // gcd(a, a + 1) -> 1
                        return result_const!(1);
                    }
                }
            }

            OptOp::Median if i.inputs.len() == 2 && i.inputs[0].is_constant() => {
                let c = cfg.get_constant_(i.inputs[0]);
                let a = if c % 2 == 1 {
                    // this can happen, i.e. when optimized from Median(4, 103, 101, x[-10..10]) -> Median(101, x)
                    // but that should be super rare, so I'm not interested in making it optimal
                    break 'main;
                } else {
                    // for 2: -1 will get rounded differently in (a + 2) / 2 than in a / 2 + 1
                    // we prefer the second form, so we need to make sure -1 cannot be an input
                    // for N (divisible by 2), problem value is -N + sgn(N)
                    let rounding_bug_value = -(c - c.signum());
                    debug_assert!(c != 2 || rounding_bug_value == -1);
                    let is_safe = simplify_cond(cfg, Condition::NeqConst(i.inputs[1], -1), i.id);
                    if is_safe == Condition::True {
                        i.inputs[1]
                    } else {
                        break 'main;
                    }
                };
                let div_2 = cfg.value_numbering(OptOp::Div, &[a, ValueId::C_TWO], None, Some(OpEffect::None));
                let const_c = cfg.store_constant(c / 2);
                i.op = OptOp::Add;
                i.inputs = smallvec![const_c, div_2];
                i.effect = OpEffect::None;
                continue;
            }

            OptOp::Median if i.inputs.len() == 3 && i.inputs[0].is_constant() && i.inputs[1].is_constant() => {
                let const1 = cfg.get_constant_(i.inputs[0]);
                let const2 = cfg.get_constant_(i.inputs[1]);
                if const1 == const2 {
                    // median(c, c, a) -> c
                    return result_const!(const1);
                } else if const1 > const2 {
                    //  median(c1, c2, a) -> clamp(a, c1, c2) = max(min(a, c1), c2)
                    let min = cfg.value_numbering(OptOp::Min, &[i.inputs[0], i.inputs[2]], None, None);
                    let max = cfg.value_numbering(OptOp::Max, &[min, i.inputs[1]], None, None);
                    return result_val!(max);
                } else {
                    // median(c1, c2, a) -> clamp(a, c2, c1) = max(min(a, c2), c1)
                    let min = cfg.value_numbering(OptOp::Min, &[i.inputs[1], i.inputs[2]], None, None);
                    let max = cfg.value_numbering(OptOp::Max, &[min, i.inputs[0]], None, None);
                    return result_val!(max);
                }
            }

            OptOp::Median if i.inputs.iter().cloned().collect::<BTreeSet<_>>().len() == 1 => {
                return result_val!(i.inputs[0]);
            }

            OptOp::Median if i.inputs.len() >= 3 => {
                let n = i.inputs.len();
                // Peeling: Remove pairs of (min, max) if we know that min <= other args <= max
                let min_idx = ranges.iter().enumerate().position(|(i, r)|
                    ranges.iter().enumerate().all(|(j, other)| i == j || r.end() <= other.start())
                );
                let max_idx = ranges.iter().enumerate().position(|(i, r)|
                    ranges.iter().enumerate().all(|(j, other)| i == j || r.start() >= other.end())
                );

                if let (Some(min), Some(max)) = (min_idx, max_idx) {
                    assert!(min != max, "what {:?}", i);
                    i.inputs = i.inputs.into_iter().enumerate().filter(|(ix, _)| *ix != min && *ix != max).map(|(_, v)| v).collect();
                    continue;
                }

                // if we know (n // 2) elements are <= all others, convert to Min
                //                                  >=                        Max
                if n % 2 == 1 {
                    let k = (n - 1) / 2;
                    let mut indices: SmallVec<[usize; 8]> = (0..n).collect();

                    indices.sort_by_key(|&idx| ranges[idx].end());
                    let (small, large) = indices.split_at(k);

                    if small.iter().map(|&i| ranges[i].end()).max().unwrap() <=
                       large.iter().map(|&i| ranges[i].start()).min().unwrap()
                    {
                        i.op = OptOp::Min;
                        i.inputs = large.iter().map(|&idx| i.inputs[idx]).collect();
                        continue;
                    }

                    indices.sort_by_key(|&idx| ranges[idx].start());
                    let (small, large) = indices.split_at(k + 1);

                    if small.iter().map(|&i| ranges[i].end()).max().unwrap() <=
                       large.iter().map(|&i| ranges[i].start()).min().unwrap()
                    {
                        i.op = OptOp::Max;
                        i.inputs = small.iter().map(|&idx| i.inputs[idx]).collect();
                        continue;
                    }
                }
            }

            OptOp::Max => {
                // Elide redundant arguments: in max(vs...), remove any argument 'a'
                // for which there exists some 'b' with max(range_a) <= min(range_b),
                // since b is always >= a.
                let keep: SmallVec<[ValueId; 4]> = i.inputs.iter().enumerate().filter(|(ix_a, _)| {
                    let a_range = &ranges[*ix_a];
                    ranges.iter().enumerate().all(|(ix_b, b_range)| {
                        *ix_a == ix_b || a_range.end() > b_range.start() // b always >= a
                    })
                }).map(|(_, a)| *a).collect();
                if keep.len() == 0 {
                    i.inputs.truncate(1); // keep the constant
                    continue;
                } else if keep.len() != i.inputs.len() {
                    i.inputs = keep;
                    continue;
                }
            }
            OptOp::Min => {
                // Elide redundant arguments: same as in Max
                let keep: SmallVec<[ValueId; 4]> = i.inputs.iter().enumerate().filter(|(ix_a, _)| {
                    let a_range = &ranges[*ix_a];
                    ranges.iter().enumerate().all(|(ix_b, b_range)| {
                        *ix_a == ix_b || a_range.start() < b_range.end() // b always <= a
                    })
                }).map(|(_, a)| *a).collect();
                if keep.len() == 0 {
                    i.inputs.truncate(1); // keep the constant
                    continue;
                } else if keep.len() != i.inputs.len() {
                    i.inputs = keep;
                    continue;
                }
                if i.inputs[0].is_constant() && i.inputs.len() == 2 &&
                    *ranges[1].start() == 0 && ranges[0] == (1..=1) {
                    // min(1, 0..=?) -> select(x != 0)
                    i.op = OptOp::Select(Condition::Neq(ValueId::C_ZERO, i.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ONE, ValueId::C_ZERO];
                    continue;
                }
            }
            OptOp::Select(cond) => {
                if i.inputs[0] > i.inputs[1] {
                    i.op = OptOp::Select(cond.clone().neg());
                    i.inputs = smallvec![i.inputs[1], i.inputs[0]];
                    continue;
                }
            }

            OptOp::And if i.inputs[1].is_constant() => { merge_constants(cfg, &mut i, |a, b| Some(a & b)); continue; }
            OptOp::Or if i.inputs[1].is_constant() => { merge_constants(cfg, &mut i, |a, b| Some(a | b)); continue; }
            OptOp::Xor if i.inputs[1].is_constant() => { merge_constants(cfg, &mut i, |a, b| Some(a ^ b)); continue; }
            OptOp::Add if i.inputs[1].is_constant() => {
                if merge_constants(cfg, &mut i, |a, b| a.checked_add(b)) {
                    continue;
                }
            },
            OptOp::Mul if i.inputs[1].is_constant() => {
                if merge_constants(cfg, &mut i, |a, b| a.checked_mul(b)) {
                    continue;
                }
            }
            OptOp::KsplangOpsIncrement(_) if i.inputs.len() == 0 || &ranges == &[0..=0] =>
                return (i.clone().with_op(OptOp::Nop, &[], OpEffect::None), None),
            OptOp::KsplangOpsIncrement(_) if i.inputs.len() > 1 && i.inputs[1].is_constant() => {
                if merge_constants(cfg, &mut i, |a, b| a.checked_add(b)) {
                    continue;
                }
            },
            OptOp::KsplangOpsIncrement(_) if i.inputs[0] == ValueId::C_ZERO => {
                i.inputs.remove(0);
                continue;
            }

            OptOp::KsplangOpsIncrement(Condition::True) if i.inputs.len() == 1 => {
                if let Some(def) = cfg.val_info(i.inputs[0]).and_then(|v| v.assigned_at).and_then(|iid| cfg.get_instruction(iid)) {
                    if let OptOp::Select(condition) = &def.op && def.inputs[0] == ValueId::C_ZERO {
                        i.op = OptOp::KsplangOpsIncrement(condition.clone().neg());
                        i.inputs = smallvec![def.inputs[1]];
                        continue;
                    }
                    if let OptOp::Select(condition) = &def.op && def.inputs[1] == ValueId::C_ZERO {
                        i.op = OptOp::KsplangOpsIncrement(condition.clone());
                        i.inputs = smallvec![def.inputs[0]];
                        continue;
                    }
                }
            }

            OptOp::Tetration if i.inputs[1] == ValueId::C_ONE => {
                return result_val!(i.inputs[0]);
            }
            OptOp::Tetration if i.inputs[0] == ValueId::C_ONE => {
                cfg.push_assert(Condition::Leq(ValueId::C_ZERO, i.inputs[1]),
                                OperationError::NegativeIterations { iterations: 0 },
                                Some(i.inputs[1]));
                return result_const!(1);
            }
            OptOp::Tetration if i.inputs[0] == ValueId::C_ZERO => { // 0 ^^ x -> x == 1 ? 0 : 1
                cfg.push_assert(Condition::Leq(ValueId::C_ZERO, i.inputs[1]),
                                OperationError::NegativeIterations { iterations: 0 },
                                Some(i.inputs[1]));
                i.op = OptOp::Select(Condition::Eq(ValueId::C_ONE, i.inputs[1]));
                i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                continue;
            }
            OptOp::Tetration if *ranges[1].start() >= 0 && *ranges[1].end() <= 1 => {
                // a ^^ x if x ∈ [0,1] -> x == 1 ? a : 1
                i.op = OptOp::Select(Condition::Eq(ValueId::C_ONE, i.inputs[1]));
                i.inputs = smallvec![i.inputs[0], ValueId::C_ONE];
                continue;
            }
            OptOp::Tetration if *ranges[1].start() >= 5 => {
                // with iters >= 5, it always fails for non-trivial inputs
                cfg.push_assert(Condition::Geq(ValueId::C_ONE, i.inputs[0]), OperationError::IntegerOverflow, None);
                cfg.push_assert(Condition::Leq(ValueId::C_ZERO, i.inputs[0]), OperationError::IntegerOverflow, None);
                return result_const!(1);
            }

            OptOp::DigitSum if *ranges[0].start() >= 0 && *ranges[0].end() < 10 => {
                return result_val!(i.inputs[0])
            }
            OptOp::DigitSum if *ranges[0].start() > -10 && *ranges[0].end() < 10 => {
                i.op = OptOp::AbsSub;
                i.inputs.insert(0, ValueId::C_ZERO);
            }
            OptOp::DigitSum if *abs_range(&ranges[0]).start() / 10 * 10 + 9 >= *abs_range(&ranges[0]).end() => {
                // CS(x) if x >= 120 and x <= 129
                //     -> x - 120 + CS(120)
                // CS(x) if x >= -129 and x <= -120
                //     -> -120 - x + CS(120)
                let offset = abs_range(&ranges[0]).start() / 10 * 10;
                assert_eq!(ranges[0].start().signum(), ranges[0].end().signum());
                let x = i.inputs[0];
                let cs_offset = digit_sum_u64(offset);
                let c = cs_offset.strict_sub_unsigned(offset);
                let c = cfg.store_constant(c);
                i.inputs = smallvec![c, x];
                if *ranges[0].start() < 0 {
                    i.op = OptOp::Sub;
                } else {
                    i.op = OptOp::Add;
                }
            }

            _ => { }
        }

        if OptOp::Add == i.op {
            // inline (a + const1) + const2, (a + const1) + (b + const2)
            let defines = i.inputs.iter().map(|v|
                if v.is_constant() { Err(cfg.get_constant_(*v)) }
                else {
                    Ok(cfg.val_info(*v).and_then(|i| i.assigned_at).and_then(|i| cfg.get_instruction(i)))
                }
            ).collect::<Vec<_>>();
            let add_or_const = defines.iter().copied().filter(|c| c.is_err() || c.unwrap().is_some_and(|i| i.op == OptOp::Add && i.inputs.iter().any(|v| v.is_constant()))).collect::<Vec<_>>();

            if add_or_const.len() >= 2 {
                let mut constant = 0i128;
                let mut promoted_positive = false;
                let mut promoted_negative = false;
                let mut new_args = SmallVec::new();
                for (def, arg) in defines.iter().zip(&i.inputs) {
                    match def {
                        Err(c) => constant += *c as i128,
                        Ok(None) => new_args.push(*arg),
                        Ok(Some(i)) => {
                            if i.op == OptOp::Add && i.inputs.len() == 2 && i.inputs[0].is_constant() {
                                let c =  cfg.get_constant_(i.inputs[0]);
                                if c > 0 { promoted_positive = true; }
                                else if c < 0 { promoted_negative = true; }
                                constant += c as i128;
                                new_args.extend_from_slice(&i.inputs[1..]);
                            } else {
                                new_args.push(*arg)
                            }
                        }
                    }
                }
                new_args.sort();

                let is_unsafe = promoted_positive && promoted_negative &&
                    OpEffect::None != OptOp::<ValueId>::Add.effect_based_on_ranges(&new_args.iter().map(|a| cfg.val_range_at(*a, i.id)).collect::<Vec<_>>());
                let Some(constant_i64) = constant.try_into().ok() else {
                    return (i.with_op(OptOp::Assert(Condition::False, OperationError::IntegerOverflow), &[], OpEffect::MayFail), None);
                };
                if !is_unsafe && constant == 0 {
                    if new_args != i.inputs {
                        i.inputs = new_args;
                        continue;
                    }
                }
                else if !is_unsafe && cfg.get_constant(i.inputs[0]) != Some(constant_i64) && i.inputs[1..] != new_args[..] {
                    if constant != 0 {
                        new_args.insert(0, cfg.store_constant(constant_i64));
                    }
                    i.inputs = new_args;
                    continue;
                }
            }

            if OptOp::<ValueId>::Add.effect_based_on_ranges(&ranges) == OpEffect::None {
                for (ix, d) in defines.iter().enumerate() {
                    if  let Ok(Some(add_i)) = d &&
                        let OptOp::Add = add_i.op &&
                        i.inputs.len() + add_i.inputs.len() <= 32
                    {
                        if add_i.effect == OpEffect::None {
                            i.inputs.remove(ix);
                            i.inputs.extend_from_slice(&add_i.inputs);
                            i.inputs.sort();
                            continue 'main;
                        }
                    }
                }
            }

            for (ix, d) in defines.iter().enumerate() {
                if let Ok(Some(sub_i)) = d &&
                    matches!(sub_i.op, OptOp::Sub)
                {
                    if i.inputs.contains(&sub_i.inputs[1]) {
                        // a + b + c + (d - c) => a + b + d
                        i.inputs.remove(ix);
                        let to_remove = i.inputs.iter().position(|v| *v == sub_i.inputs[1]).unwrap();
                        i.inputs.remove(to_remove);
                        i.inputs.push(sub_i.inputs[0]);
                        i.inputs.sort();
                        continue 'main
                    }

                    if i.inputs.len() == 2 && i.inputs[0].is_constant() && sub_i.inputs[0].is_constant() {
                        // C1 + (C2 - x) =>  (C1 + C2) - x
                        assert!(ix == 1);
                        i.op = OptOp::Sub;
                        let c1 = cfg.get_constant_(i.inputs[0]);
                        let c2 = cfg.get_constant_(sub_i.inputs[0]);
                        let negated = sub_i.inputs[1];
                        if let Some(c_new) = c1.checked_add(c2) {
                            i.inputs = smallvec![cfg.store_constant(c_new), negated];
                            continue 'main
                        }
                    }

                    if i.inputs.len() == 2 && sub_i.inputs[0] == ValueId::C_ZERO {
                        // a + (0 - b) => a - b
                        i.op = OptOp::Sub;
                        let other_add = i.inputs[1-ix];
                        i.inputs = smallvec![other_add, sub_i.inputs[1]];
                        continue 'main
                    }
                }
            }
        }

        if OptOp::Mul == i.op && i.inputs[0].is_constant() && i.inputs.len() == 2 {
            let c = cfg.get_constant_(i.inputs[0]);
            if let Some(def) = cfg.get_defined_at(i.inputs[1]) {
                // let def_ranges = get_ranges(cfg, def.inputs.iter().copied());
                // (-x) * const => x * (-const)
                if def.op == OptOp::Sub && def.inputs[0] == ValueId::C_ZERO && i.inputs[0] != ValueId::C_IMIN {
                    i.effect = OpEffect::worse_of(i.effect, def.effect);
                    i.inputs[1] = def.inputs[1];
                    i.inputs[0] = cfg.store_constant(-c);
                    continue;
                }
                // if def.op == OptOp::Sub {
                //
                // }
                // if def.op == OptOp::Add {
                //     let is_valid = def_ranges.
                // }
                if def.op == OptOp::Mul && def.inputs[0].is_constant() {
                    let c2 = cfg.get_constant_(def.inputs[0]);
                    if let Some(new_const) = c.checked_mul(c2) {
                        i.effect = OpEffect::worse_of(i.effect, def.effect);
                        i.inputs.remove(1);
                        i.inputs.extend(def.inputs.iter().skip(1).copied());
                        i.inputs[0] = cfg.store_constant(new_const);
                        continue;
                    } else {
                        cfg.push_assert(Condition::Eq(ValueId::C_ZERO, def.inputs[1]), OperationError::IntegerOverflow, None);
                        return (i.clone().with_op(OptOp::Add, &[ ValueId::C_ZERO ], OpEffect::None), None);
                    }
                }
            }
        }

        if OptOp::Mul == i.op {
            // (a + b) * c => a * c + b * c
            // only valid if at all a, b have the same sign, otherwise we are introducing overfows
            for (arg_ix, &val) in i.inputs.clone().iter().enumerate() {
                let Some(def) = cfg.get_defined_at(val) else { continue };
                if def.op == OptOp::Add {
                    let def_rs = get_ranges(cfg, def.inputs.iter().copied());
                    let is_valid = def_rs.iter().cloned().map(range_signum).reduce(union_range).unwrap().count() <= 2 || {
                        let mut range_clone = ranges.clone();
                        def_rs.iter().all(move |add_input| {
                            range_clone[arg_ix] = add_input.clone();
                            OptOp::<ValueId>::Mul.effect_based_on_ranges(&range_clone) == OpEffect::None
                        })
                    };
                    // println!("DBG Mul OPT: {} is_valid={} add_def={}", i, is_valid, def);
                    if is_valid {
                        let new_args = def.inputs.clone().iter().map(|v| {
                            let mut in_clone = i.inputs.clone();
                            in_clone[arg_ix] = *v;
                            cfg.value_numbering(OptOp::Mul, &in_clone, None, Some(i.effect))
                        }).collect();
                        // println!("DBG Mul OPT: end rec: {new_args:?}");

                        i.inputs = new_args;
                        i.op = OptOp::Add;
                        continue 'main;
                    }
                }
            }
        }

        // pattern::OptOptPattern::new(OptOp::Mul, vec![] ])

        if OptOp::Div == i.op && !i.inputs[0].is_constant() {
            // a * x / x -> a
            let divisor = i.inputs[1];
            if let Some(defined_at) = cfg.get_defined_at(i.inputs[0]) {
                if defined_at.op == OptOp::Mul && defined_at.inputs.contains(&divisor) {
                    let divisor_index = defined_at.inputs.iter().position(|&x| x == divisor).unwrap();
                    let mut others = defined_at.inputs.clone();
                    others.remove(divisor_index);
                    let other_mul = if others.len() == 1 {
                        others[0]
                    } else {
                        debug_assert!(others.len() > 1);
                        cfg.value_numbering(OptOp::Mul, &others, None, None)
                    };
                    if ranges[1].contains(&0) {
                        cfg.push_assert(Condition::Neq(ValueId::C_ZERO, i.inputs[1]), OperationError::DivisionByZero, None);
                    }
                    return (i.clone().with_op(OptOp::Add, &[ other_mul ], OpEffect::None), None);
                }
            }
        }
        // TODO: this breaks other optimizations
        // if OptOp::Mul == i.op && i.inputs[0].is_constant() {
        //     // a / c * c => a - (a % c)
        //     let c = cfg.get_constant_(i.inputs[0]);
        //     if let Some(defined_at) = cfg.get_defined_at(i.inputs[1]) {
        //         if defined_at.op == OptOp::Div && defined_at.inputs[1] == i.inputs[0] && c.abs() > 1 {
        //             let a = defined_at.inputs[0];
        //             let c_val = cfg.store_constant(c.abs());
        //             let modulo = cfg.value_numbering(OptOp::Mod, &[a, c_val], None, None);
        //             i.op = OptOp::Sub;
        //             i.effect = OpEffect::None;
        //             i.inputs = smallvec![a, modulo];
        //             continue;
        //         }
        //     }
        // }
        if matches!(i.op, OptOp::CursedDiv | OptOp::Div) &&
           let Some(divided) = cfg.get_defined_at(i.inputs[0])
        {
            if divided.op == OptOp::Sub &&
               let Some(divided_sub_mod) = cfg.get_defined_at(divided.inputs[1]) &&
               divided_sub_mod.op == OptOp::Mod &&
               divided_sub_mod.inputs[0] == divided.inputs[0] &&
               divided_sub_mod.inputs[1] == i.inputs[1]
            {
                // (a - (a % d)) / d   -> a / d
                i.op = OptOp::Div; // always divisible
                i.inputs[0] = divided.inputs[0];
                continue;
            }
        }
        if OptOp::CursedDiv == i.op {
            let cond = simplify_cond(cfg, Condition::Divides(i.inputs[0], i.inputs[1]), i.id);
            if cond == Condition::True {
                i.op = OptOp::Div;
                continue;
            }
            if cond == Condition::False {
                i.op = OptOp::Mod;
                continue;
            }
        }

        if OptOp::Sgn == i.op {
            let x = i.inputs[0];
            if let Some(nested) = cfg.get_defined_at(x) {
                // sgn(|a - b|) => condition(a != b)
                if nested.op == OptOp::AbsSub {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    continue;
                }
                // sgn(a - b) where a >= b => condition(a != b)
                else if nested.op == OptOp::Sub && *ranges[0].start() >= 0 {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    continue;
                }
                // sgn(a - b) where b >= a => a == b ? 0 : -1
                else if nested.op == OptOp::Sub && *ranges[0].end() <= 0 {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_NEG_ONE];
                    continue;
                }
                // sgn(digit_sum(a)) => condition(a != 0)
                else if nested.op == OptOp::DigitSum {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    continue;
                }
                else if *ranges[0].start() >= 0 {
                    i.op = OptOp::Select(Condition::Eq(x, ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    continue;
                } else if *ranges[0].end() <= 0 {
                    i.op = OptOp::Select(Condition::Eq(x, ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_NEG_ONE];
                    continue;
                }
            }
        }

        if OptOp::DigitSum == i.op {
            let x = i.inputs[0];
            if let Some(nested) = cfg.get_defined_at(x) {
                // CS(|x|) = CS(x)
                // CS(-x) = CS(x)
                if matches!(nested.op, OptOp::AbsSub | OptOp::Sub) && nested.inputs[0] == ValueId::C_ZERO {
                    i.inputs = smallvec![nested.inputs[1]];
                    continue;
                }
            }
        }

        if OptOp::AbsSub == i.op {
            let x = i.inputs[0];
            let y = i.inputs[1];
            assert!(y.is_computed());
            if let Some(nested) = cfg.get_defined_at(y) {
                // |0 - sgn(a)| => condition(a != 0)
                if nested.op == OptOp::Sgn && x == ValueId::C_ZERO {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    continue;
                }
                // |0 - (a - b)| => |a - b|
                else if nested.op == OptOp::Sub && x == ValueId::C_ZERO {
                    i.inputs = nested.inputs.clone();
                    continue;
                }
                else if nested.op == OptOp::Sgn && nested.inputs[0] == x {
                    // |a - sgn(a)| will not overflow, just mark it as without effect
                    i.effect = OpEffect::None;
                    // and range is known to be special
                    let ar = abs_range(&ranges[0]);
                    out_range = Some((ar.start().saturating_sub(1) as i64) ..= (ar.end().saturating_sub(1)) as i64);
                }
            }
        }

        if OptOp::Sub == i.op {
            let &[x, y] = i.inputs.as_slice() else { panic!() };
            if let Some(y_def) = cfg.get_defined_at(y) {
                if y_def.op == OptOp::Mod && y_def.inputs[0] == x {
                    // a - (a % something)    -- we won't simplify this, but we can be sure this won't overflow
                    i.effect = OpEffect::None;
                }
                if y_def.op == OptOp::Add && y_def.inputs.contains(&x) && y_def.inputs.len() == 2 {
                    // a - (x + a) -> 0 - x
                    let new_y = if y_def.inputs[0] == x { y_def.inputs[1] } else { y_def.inputs[0] };
                    i.inputs = smallvec![ValueId::C_ZERO, new_y];
                    continue;
                }
                if y_def.op == OptOp::Sub && y_def.inputs[0] == x {
                    // a - (a - b) -> b
                    return result_val!(y_def.inputs[1]);
                }
                if y_def.op == OptOp::Sub && y_def.inputs[0].is_constant() {
                    // a - (C - x) -> a + x + (-C)
                    let cc = cfg.get_constant_(y_def.inputs[0]);
                    let other_y = y_def.inputs[1];
                    i.op = OptOp::Add;
                    i.inputs = smallvec![cfg.store_constant(-cc), x, other_y];
                    continue;
                }
            }
            if let Some(x_def) = cfg.get_defined_at(x) {
                if x_def.op == OptOp::Add && x_def.inputs.contains(&y) {
                    // (x + a + y) - a -> x + y
                    i.op = OptOp::Add;
                    i.inputs = x_def.inputs.clone();
                    i.inputs.remove(x_def.inputs.iter().position(|&y2| y2 == y).unwrap());
                    continue;
                }
            }
        }

        // used in duplication:
        // a + ((a / 2) + 1) * -2
        // OR a + ((a / 2) * -2 - 2)
        // which is equivalent to (a % 2) - 2
        if OptOp::Add == i.op && !i.inputs[0].is_constant() && i.inputs.len() == 2 && i.inputs[0] != i.inputs[1] {
            const MUL_PATTERN: LazyLock<OptOptPattern> = LazyLock::new(||
                P::op2(OptOp::Mul,
                    -2,
                    P::op2(OptOp::Add,
                        1,
                        P::op2(OptOp::Div,
                            P::any().named("v2"),
                            2
                        )
                    )
                ).or_op(OptOp::Add, [
                    P::const_(-2),
                    P::op2(OptOp::Mul,
                        -2,
                        P::op2(OptOp::Div,
                            P::any().named("v2"),
                            2
                        )
                    )
                ])
            );
            if let Ok(r) = MUL_PATTERN.try_match(cfg, &i.inputs) {
                let a = r.get_named_single("v2").unwrap();
                if i.inputs.contains(&a) {
                    // rewrite to (a % 2) - 2
                    let modulo = cfg.value_numbering(OptOp::Mod, &[a, ValueId::C_TWO], None, None);
                    i.op = OptOp::Add;
                    i.inputs = smallvec![ValueId::C_NEG_TWO, modulo];
                    i.effect = OpEffect::None;
                    continue;
                }
            }
        }

        // used in duplication:
        // (a / 2 * 2) + (a % 2) which is equivalent to a
        if OptOp::Add == i.op && !i.inputs[0].is_constant() && i.inputs.len() == 2 && i.inputs[0] != i.inputs[1] {
            static MUL_PATTERN: LazyLock<OptOptPattern> = LazyLock::new(||
                P::op2(OptOp::Mul,
                    P::constant(2..).named("div1"),
                    P::op2(OptOp::Div,
                        P::any().named("v2"),
                        P::constant(2..).named("div2")
                    )
                )
            );
            if let Ok(r) = MUL_PATTERN.try_match(cfg, &i.inputs) &&
               r.get_named_single("div1") == r.get_named_single("div2") &&
               let Some(mod1) = cfg.get_defined_at(i.inputs[if i.inputs[0] == r.main_value() { 1 } else { 0 }]) &&
               mod1.op == OptOp::Mod &&
               mod1.inputs[0] == r.get_named_single("v2").unwrap() &&
               mod1.inputs[1] == r.get_named_single("div1").unwrap()
            {
                let a = r.get_named_single("v2").unwrap();
                return result_val!(a);
            }
        }

        // used in duplication:
        if OptOp::Add == i.op && i.inputs.len() == 2 && i.inputs[0].is_computed() && i.inputs[1].is_computed() {
            // a - 2*median(2, a)
            //   => ??
            static PATTERN_MOD_DEV: LazyLock<OptOptPattern> = LazyLock::new(||
                P::op2(OptOp::Mul, -2, P::op2(OptOp::Median, 2, P::any().named("a")))
            );
            if let Ok(r) = PATTERN_MOD_DEV.try_match(cfg, &i.inputs) &&
                let Some(a) = r.get_named_single("a") &&
                i.inputs.contains(&a)
            {
                // let add1 = cfg.value_numbering(OptOp::Add, &[a, ValueId::C_TWO], None, None);
                // let mod1 = cfg.value_numbering(OptOp::Mod, &[add1, ValueId::C_TWO], None, None);
                // i.op = OptOp::Add;
                // i.inputs = smallvec![ValueId::C_NEG_TWO, mod1]
                // let select1 = cfg.value_numbering(OptOp::Select(Condition::Leq(ValueId::C_NEG_TWO, a)), &[ ValueId::C_NEG_ONE, ValueId::C_NEG_THREE ], None, None);
                // i.op = OptOp::Select(Condition::Divides(a, ValueId::C_TWO));
                // i.inputs = smallvec![ValueId::C_NEG_TWO, select1];
                // continue;
                out_range = Some(-3..=-1);
                i.effect = OpEffect::None;
            }

            // main duplication logic:
            // m = median(2, a)
            // (2 * (m-1)) + (2 + a - 2 * m)
            static PATTERN2: LazyLock<OptOptPattern> = LazyLock::new(||
                P::op2(OptOp::Add,
                    P::op2(OptOp::Mul, 2, P::op2(OptOp::Add, -1, P::op2(OptOp::Median, 2, P::any().named("a1")))),
                    P::op3(OptOp::Add,
                        2,
                        P::any().named("a2"),
                        P::op2(OptOp::Mul, -2, P::op2(OptOp::Median, 2, P::any().named("a3")))
                    )
                )
            );
            if let Ok(r) = PATTERN2.try_match_instr(cfg, &i) &&
               r.get_named_single("a1") == r.get_named_single("a2") &&
               r.get_named_single("a2") == r.get_named_single("a3")
            {
                let a = r.get_named_single("a1").unwrap();
                return result_val!(a);
            }
        }

        match &i.op {
            OptOp::KsplangOpsIncrement(cond) | OptOp::Select(cond) | OptOp::Jump(cond, _) => {
                // simplify Select if we have some built-in condition which could imply a specific branch
                let mut changed = false;
                for (ix, input) in i.inputs.iter_mut().enumerate() {
                    if let Some(val_info) = cfg.val_info(*input) &&
                       let Some(defined_at) = val_info.assigned_at &&
                       let Some(def) = cfg.get_instruction(defined_at)
                    {
                        if let OptOp::Select(select_cond) = &def.op {
                            let cond = cond.clone().neg_if(ix == 1 && matches!(i.op, OptOp::Select(_)));
                            let select_cond = select_cond.clone();
                            let select_inputs = def.inputs.clone();
                            let cond2 = simplify_cond(cfg, select_cond.clone(), i.id);
                            match cond_implies(cfg, &cond, &cond2, i.id) {
                                Some(Condition::True) => {
                                    println!("Managed to simplify {input} ref under condition {cond} to {}, as it implies {select_cond} to be true\n in {} {:?}", select_inputs[0], i.id, i.op);
                                    *input = select_inputs[0];
                                    changed = true;
                                }
                                Some(Condition::False) => {
                                    println!("Managed to simplify {input} ref under condition {cond} to {}, as it implies {select_cond} to be false\n in {} {:?}", select_inputs[1], i.id, i.op);
                                    *input = select_inputs[1];
                                    changed = true;
                                }
                                _ => {}
                            }
                        }
                    }
                }

                if changed { continue }
            },
            _ => {}
        }

        break;
    }



    (i, out_range)
}

// fn get_defs(g: &GraphBuilder, vals: impl Iterator<Item = ValueId>) -> SmallVec<[Option<&OptInstr>; 4]> {
//     vals.map(|v| g.get_defined_at(v)).collect()
// }
fn get_ranges(g: &GraphBuilder, vals: impl Iterator<Item = ValueId>) -> SmallVec<[RangeInclusive<i64>; 4]> {
    vals.map(|v| g.val_range(v)).collect()
}

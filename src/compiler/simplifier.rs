use std::{cmp, ops::RangeInclusive};

use smallvec::{smallvec, SmallVec, ToSmallVec};

use crate::{compiler::{analyzer::cond_implies, cfg::GraphBuilder, ops::{InstrId, OpEffect, OptInstr, OptOp, ValueId}, pattern::OptOptPattern, range_ops::range_signum, utils::{abs_range, range_is_signless, union_range}, osmibytecode::Condition}, vm::OperationError};

fn overlap(a: &RangeInclusive<i64>, b: &RangeInclusive<i64>) -> Option<RangeInclusive<i64>> {
    let start = *a.start().max(b.start());
    let end = *a.end().min(b.end());
    if start <= end {
        Some(start..=end)
    } else {
        None
    }
}

pub fn simplify_cond(cfg: &mut GraphBuilder, condition: Condition<ValueId>, at: InstrId) -> Condition<ValueId> {
    let mut cond_mut = condition.clone();
    loop {
        let new_cond = simplify_cond_core(cfg, &cond_mut, at);
        let done = new_cond == cond_mut;
        cond_mut = new_cond;
        if done {
            break;
        }
    }

    if let Some(info) =
        cond_mut.regs().into_iter().filter(|x| x.is_computed()).next()
        .and_then(|v| cfg.val_info(v)) {
        for (assumption, _, _, _) in info.iter_assumptions(at, &cfg.block_(at.block_id()).predecessors) {
            if let Some(implied) = cond_implies(cfg, &assumption, &cond_mut, at) {
                cond_mut = implied;
                if cond_mut == Condition::True || cond_mut == Condition::False {
                    break;
                }
            }
        }
    }
    if cfg!(debug_assertions) && cond_mut != condition {
        println!("simplify_cond({condition}, {at}) -> {cond_mut}")
    }
    cond_mut
}


fn simplify_cond_core(cfg: &mut GraphBuilder, condition: &Condition<ValueId>, at: InstrId) -> Condition<ValueId> {
    match condition.clone() {
        Condition::EqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Eq(a, b)
        }
        Condition::NeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Neq(a, b)
        }
        Condition::LtConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Lt(a, b)
        }
        Condition::LeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Leq(a, b)
        }
        Condition::GtConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Gt(a, b)
        }
        Condition::GeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            Condition::Geq(a, b)
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
            let ar = cfg.val_range_at(a, at);
            let br = cfg.val_range_at(b, at);

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
            // Min/Max comparison simplification
            //  min(k, x) == k  -> x <= k
            if a.is_constant() {
                let ac = *ar.start();
                if let Some(def) = cfg.get_defined_at(b) {
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
                        let a2 = cfg.store_constant(ac - shift);

                        return condition.replace_arr(vec![a2, b2])
                    }

                    // if matches!(def.op, OptOp::Mul) && def.inputs.len() == 2 && def.inputs[0].is_constant() { // TODO
                    //     // A > (b * C) => (A / C) > b
                    //     let mul = cfg.get_constant_(def.inputs[0]);
                    //     let b2 = def.inputs[1];
                    //     let ac2 = if ac % mul == 0 {
                    //         ac / mul
                    //     } else {
                    //         match &condition {
                    //             Condition::Eq(_, _) => return Condition::False,
                    //             Condition::Neq(_, _) => return Condition::True,
                    //             _ => todo!()
                    //         }
                    //     };
                    //     let a2 = cfg.store_constant(ac2 / mul);
                    //
                    //     return canonicalize_condition(cfg, condition.replace_arr(vec![a2, b2]))
                    // }
                }
            }

            condition
        }

        Condition::Divides(a, b) => {
            let (ar, br) = (cfg.val_range_at(a, at), cfg.val_range_at(b, at));
            let ara = abs_range(ar.clone());
            let bra = abs_range(br.clone());
            if *ara.end() < *bra.start() || *bra.end() == 0 {
                return if *ara.start() == 0 {
                    Condition::Eq(b, ValueId::C_ZERO)
                } else {
                    Condition::False
                };
            }
            if *ara.end() == 0 {
                return Condition::Neq(b, ValueId::C_ZERO);
            }

            // if *br.end() > *ar.end() / 2 && ar.start() != 0 {
            //     return Condition::Eq(a, b);
            // }
            if *br.end() == *br.start() {
                let bc = *br.start();
                if bc == 1 || bc == -1 {
                    return Condition::True
                }
                if (*ara.end() / bc.abs_diff(0)) * bc.abs_diff(0) < *ara.start() {
                    return Condition::False;
                }
                if (*ara.end() / bc.abs_diff(0)) * bc.abs_diff(0) < *ara.start() + bc.abs_diff(0) {
                    return Condition::Eq(a, b);
                }
                if bc < 0 && bc != i64::MIN {
                    let b = cfg.store_constant(-bc);
                    return Condition::Divides(a, b);
                }
            }

            if range_is_signless(&br) && range_is_signless(&ar) && !(ara.contains(&1) && ara.contains(&cmp::max(2, *bra.start()))) {
                // Try to reduce 3 % x == 0 into 3 == x
                let mindiv = if *ar.start() == *ar.end() {
                    let ac = *ar.start();
                    if ac == 1 || ac == -1 {
                        return Condition::Eq(b, if *br.start() >= 0 { ValueId::C_ONE } else { ValueId::C_NEG_ONE });
                    }
                    try_get_lowest_divisor(ac.unsigned_abs()).unwrap_or(*SOME_PRIMES.last().unwrap() as u64)
                } else {
                    2 // assume it can be divided by 2
                };

                let min_divided = *bra.start() / mindiv;
                if *bra.start() > min_divided {
                    // so, condition is only true if |b| == |a|
                    // we just need to go though some hoops to express that...
                    if (*br.start() >= 0) == (*ar.start() >= 0) {
                        return Condition::Eq(a, b);
                    }

                    if *ar.start() == *ar.end() {
                        // flip sign, but it's a constant
                        let a_flip = cfg.store_constant(-*ar.start());
                        return Condition::Eq(a_flip, b);
                    }
                    // IDK, maybe later...
                }
                // TODO: maybe also check if there is some other number which is the only divisor of A
            }

            Condition::Divides(a, b)
        }
        Condition::NotDivides(a, b) =>
            simplify_cond_core(cfg, &Condition::Divides(a, b), at).neg()
    }
}

const SOME_PRIMES: [u8; 54] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251];
fn try_get_lowest_divisor(a: u64) -> Option<u64> {
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
            let may_fail = args.iter().any(|a| *g.val_range(*a).start() != i64::MIN);
            
            if may_fail {
                (OpEffect::MayFail, vec![])
            } else {
                (OpEffect::None, vec![])
            }
        },
        OptOp::StackSwap => (OpEffect::MayDeopt, vec![]),
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
                    a_i.swap_remove(a_i.iter().position(|x| *x == *c).unwrap());
                    b_i.swap_remove(b_i.iter().position(|x| *x == *c).unwrap());
                }
                return Some(make_result(g, &b_i, &a_i));
            }
        }
    }

    None
}

/// Flattens nested associative / commutative variadic operations (Add, Mul, And, Or, Xor, Max, Min, Gcd).
/// Returns true if any change (inputs replaced) so caller can restart simplification loop.
fn flatten_variadic(cfg: &GraphBuilder, instr: &mut OptInstr, dedup: bool, limit: i64) -> bool {
    let op = &instr.op;
    let mut changed = false;
    let mut new_inputs: SmallVec<[ValueId; 4]> = SmallVec::new();
    for &v in &instr.inputs {
        if limit <= new_inputs.len() as i64 + 1 {
            return false;
        }
        let def = cfg.get_defined_at(v);
        if let Some(d) = def {
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
        instr.inputs = new_inputs;
    }
    changed
}

/// Returns (changed, new instruction)
pub fn simplify_instr(cfg: &mut GraphBuilder, mut i: OptInstr) -> (OptInstr, Option<RangeInclusive<i64>>) {
    if matches!(i.op, OptOp::Nop | OptOp::Pop | OptOp::Push | OptOp::StackSwap | OptOp::Const(_)) {
        return (i, None);
    }
    
    let mut iter = 0;
    let mut changed = true;
    let mut change_path: Vec<(OptOp<ValueId>, SmallVec<[ValueId; 4]>, SmallVec<[RangeInclusive<i64>; 4]>)> = Vec::new();
    'main: while changed {
        #[cfg(debug_assertions)] {
            change_path.push((i.op.clone(), i.inputs.clone(), i.inputs.iter().map(|a| cfg.val_range_at(*a, i.id)).collect::<SmallVec<[_; 4]>>()));
        }
        changed = true;
        iter += 1;
        if iter > 100 {
            println!("Warning: simplify_instr infinite loop detected: {i:?} {change_path:?}");
            break;
        }

        assert!(i.op.arity().contains(&i.inputs.len()), "Invalid arity for {:?}: {}. Optimized as {change_path:?}", i.op, i.inputs.len());

        // Generic flattening for associative non-overflowing ops
        if matches!(i.op, OptOp::Max | OptOp::Min | OptOp::Gcd | OptOp::And | OptOp::Or | OptOp::Xor) && i.inputs.len() >= 2 {
            let dedup = !matches!(i.op, OptOp::Xor);
            flatten_variadic(cfg, &mut i, dedup, /* limit */ 32);
        }

        if !matches!(i.op, OptOp::Const(_) | OptOp::StackSwap | OptOp::Pop | OptOp::Push) &&
            i.iter_inputs().all(|a| a.is_constant()) {
            let all_args: SmallVec<[i64; 8]> = i.iter_inputs().map(|a| cfg.get_constant_(a)).collect();
            match i.op.evaluate(&all_args) {
                Ok(v) => return (i.with_op(OptOp::Const(v), &[], OpEffect::None), Some(v..=v)),
                Err(Some(error)) => {
                    // will always fail
                    return (i.with_op(OptOp::Assert(Condition::False, error), &[], OpEffect::None), None);
                },
                Err(None) => {
                    // cannot be evaluated
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

        let ranges = i.inputs.iter().map(|a| cfg.val_range_at(*a, i.id)).collect::<SmallVec<[_; 4]>>();

        // if i.effect != OpEffect::None {
        //     match &i.op {
        //         OptOp::Add =>
        //     }
        // }

        match &i.op {
            OptOp::Select(Condition::True) =>
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[0] ], OpEffect::None), Some(ranges[0].clone())),
            OptOp::Select(Condition::False) =>
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[1] ], OpEffect::None), Some(ranges[1].clone())),
            OptOp::Assert(Condition::True, _) | OptOp::DeoptAssert(Condition::True) | OptOp::Jump(Condition::False, _) =>
                return (i.clone().with_op(OptOp::Nop, &[], OpEffect::None), None),
            // degenerate expressions are all simplified to degenerate Add, which is the only thing user then has to handle
            OptOp::Add | OptOp::Mul | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Max | OptOp::Min if i.inputs.len() == 1 =>
                return (i.clone().with_op(OptOp::Add, &i.inputs, OpEffect::None), None),

            OptOp::AbsSub | OptOp::Sub if i.inputs[0] == i.inputs[1] =>
                // abs(a - a) -> 0
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), None),
            
            OptOp::Sub if i.inputs[1].is_constant() && i.inputs[1] != ValueId::C_IMIN => {
                let c = cfg.get_constant_(i.inputs[1]);
                if c == 0 {
                    // a - 0 -> a
                    return (i.clone().with_op(OptOp::Add, &[ i.inputs[0] ], OpEffect::None), Some(ranges[0].clone()));
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
                } else if start_b >= end_a {
                    // b - a is always non-negative
                    i.op = OptOp::Sub;
                    i.inputs = smallvec![i.inputs[1], i.inputs[0]];
                } else {
                    // ranges overlap, must use abs sub, let's check effect
                    if cmp::max(end_a, end_b).abs_diff(cmp::min(start_a, start_b)) <= i64::MAX as u64 {
                        i.effect = OpEffect::None;
                    }
                    i.inputs.sort();
                    changed = false;
                }

            }

            OptOp::Add if i.inputs[0] == ValueId::C_ZERO => {
                i.inputs.remove(0);
            }

            OptOp::Mod | OptOp::ModEuclid | OptOp::Div | OptOp::CursedDiv if ranges[1] == (0..=0) =>
                // a % 0 or a / 0 -> always error
                return (i.with_op(OptOp::Assert(Condition::False, OperationError::DivisionByZero), &[], OpEffect::None), None),

            OptOp::Mod | OptOp::ModEuclid if i.inputs[0] == i.inputs[1] => {
                // a % a -> 0
                let br = &ranges[1];
                if br.contains(&0) {
                    cfg.push_assert(Condition::NeqConst(i.inputs[1], 0), OperationError::DivisionByZero, None);
                }
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), None);
            }

            OptOp::Mod | OptOp::ModEuclid if i.inputs[1] == ValueId::C_ONE || i.inputs[1] == ValueId::C_NEG_ONE => {
                // a % 1 -> 0
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), Some(0..=0));
            }

            OptOp::ModEuclid if *ranges[0].start() >= 0 => {
                i.op = OptOp::Mod;
                continue;
            }

            OptOp::Div | OptOp::CursedDiv if i.inputs[1] == ValueId::C_ONE =>
                // a / 1 -> a
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[0] ], OpEffect::None), Some(ranges[0].clone())),
            OptOp::Div | OptOp::CursedDiv if i.inputs[1] == ValueId::C_NEG_ONE => {
                // a / -1 -> -a
                i.op = OptOp::Sub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[0]];
            }
            OptOp::Div | OptOp::CursedDiv if i.inputs[0] == i.inputs[1] => {
                // a / a -> 1
                let br = &ranges[1];
                if br.contains(&0) {
                    cfg.push_assert(Condition::NeqConst(i.inputs[1], 0), OperationError::DivisionByZero, None);
                }
                return (i.clone().with_op(OptOp::Const(1), &[], OpEffect::None), None);
            }
            OptOp::Mul if i.inputs.contains(&ValueId::C_ZERO) =>
                // a * 0 -> 0
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), Some(0..=0)),
            &OptOp::Mul if i.inputs[0] == ValueId::C_ONE && i.inputs.len() == 2 =>
                // 1 * a -> a
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[1] ], OpEffect::None), Some(ranges[1].clone())),
            &OptOp::Mul if i.inputs[0] == ValueId::C_NEG_ONE && i.inputs.len() == 2 => {
                // -1 * a -> 0 - a
                i.op = OptOp::Sub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[1]];
            }

            OptOp::ShiftL if i.inputs[1].is_constant() => {
                let shift = cfg.get_constant_(i.inputs[1]);
                if shift < 0 {
                    break 'main;
                }
                if shift >= 64 {
                    return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), Some(0..=0));
                }
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

            OptOp::MedianCursed if i.inputs[0].is_constant() => {
                let n = cfg.get_constant_(i.inputs[0]);
                if n <= 0 || n as usize > i.inputs.len() - 1 {
                    return (OptInstr::deopt(Condition::True), None)
                }
                let mut vals = i.inputs[0..n as usize].to_vec();
                vals.sort();
                i.inputs = vals.to_smallvec();
                i.op = OptOp::Median;
                i.effect = OpEffect::None;
            }

            OptOp::Gcd if i.inputs.len() == 1 => {
                i.op = OptOp::AbsSub;
                i.inputs = smallvec![ValueId::C_ZERO, i.inputs[0]];
            }

            OptOp::Gcd if i.inputs.len() == 2 => {
                let (a, b) = (i.inputs[0], i.inputs[1]);
                if let Some((offset, a_additional, b_additional)) = get_values_offset(cfg, a, b) {
                    if a_additional.is_empty() && b_additional.is_empty() && offset == 1 {
                        // gcd(a, a + 1) -> 1
                        return (i.clone().with_op(OptOp::Const(1), &[], OpEffect::None), Some(1..=1));
                    }
                }
                changed = false;
            }

            OptOp::Median if i.inputs.len() == 2 && i.inputs[0].is_constant() => {
                let mut c = cfg.get_constant_(i.inputs[0]);
                let ar = &ranges[1];
                let a = if c % 2 == 1 {
                    // we could optimize to (a + c) / 2, but we'll rather try (a + 1) / 2 + c / 2 and (a - 1) / 2 + c / 2
                    if *ar.start() != i64::MIN {
                        c += 1;
                        cfg.value_numbering(OptOp::Add, &[i.inputs[1], ValueId::C_NEG_ONE], None, Some(OpEffect::None))
                    } else if *ar.end() != i64::MAX {
                        c -= 1;
                        cfg.value_numbering(OptOp::Add, &[i.inputs[1], ValueId::C_ONE], None, Some(OpEffect::None))
                    } else {
                        break 'main;
                    }
                } else {
                    i.inputs[1]
                };
                let div_2 = cfg.value_numbering(OptOp::Div, &[a, ValueId::C_TWO], None, Some(OpEffect::None));
                let const_c = cfg.store_constant(c / 2);
                i.op = OptOp::Add;
                i.inputs = smallvec![const_c, div_2];
                i.effect = OpEffect::None;
            }

            OptOp::Median if i.inputs.len() == 3 && i.inputs[0].is_constant() && i.inputs[1].is_constant() => {
                let const1 = cfg.get_constant_(i.inputs[0]);
                let const2 = cfg.get_constant_(i.inputs[1]);
                if const1 == const2 {
                    // median(c, c, a) -> c
                    return (i.clone().with_op(OptOp::Const(const1), &[ ], OpEffect::None), Some(const1..=const1));
                } else if const1 > const2 {
                    //  median(c1, c2, a) -> clamp(a, c1, c2) = max(min(a, c1), c2)
                    let min = cfg.value_numbering(OptOp::Min, &[i.inputs[0], i.inputs[2]], None, None);
                    let max = cfg.value_numbering(OptOp::Max, &[min, i.inputs[1]], None, None);
                    return (i.clone().with_op(OptOp::Add, &[ max ], OpEffect::None), None);
                } else {
                    // median(c1, c2, a) -> clamp(a, c2, c1) = max(min(a, c2), c1)
                    let min = cfg.value_numbering(OptOp::Min, &[i.inputs[1], i.inputs[2]], None, None);
                    let max = cfg.value_numbering(OptOp::Max, &[min, i.inputs[0]], None, None);
                    return (i.clone().with_op(OptOp::Add, &[ max ], OpEffect::None), None);
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
                } else if keep.len() != i.inputs.len() {
                    i.inputs = keep;
                    continue;
                } else {
                    changed = false;
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
                } else if keep.len() != i.inputs.len() {
                    i.inputs = keep;
                    continue;
                } else {
                    changed = false;
                }
            }

            _ => {
                changed = false;
            }
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
                let mut constant = 0;
                let mut promoted_positive = false;
                let mut promoted_negative = false;
                let mut new_args = SmallVec::new();
                for (def, arg) in defines.iter().zip(&i.inputs) {
                    match def {
                        Err(c) => constant += c,
                        Ok(None) => new_args.push(*arg),
                        Ok(Some(i)) => {
                            if i.op == OptOp::Add && i.inputs.len() == 2 && i.inputs[0].is_constant() {
                                let c =  cfg.get_constant_(i.inputs[0]);
                                if c > 0 { promoted_positive = true; }
                                else if c < 0 { promoted_negative = true; }
                                constant += c;
                                new_args.extend_from_slice(&i.inputs[1..]);
                            } else {
                                new_args.push(*arg)
                            }
                        }
                    }
                }

                let is_unsafe = promoted_positive && promoted_negative &&
                    OpEffect::None != OptOp::<ValueId>::Add.effect_based_on_ranges(&new_args.iter().map(|a| cfg.val_range(*a)).collect::<Vec<_>>());
                if !is_unsafe {
                    i.op = OptOp::Add;
                    if constant != 0 {
                        new_args.push(cfg.store_constant(constant));
                    }
                    new_args.sort();
                    i.inputs = new_args;
                    changed = true;
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
                    changed = true;
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
                    i.effect = OpEffect::worse_of(i.effect, def.effect);
                    i.inputs[1] = def.inputs[1];
                    i.inputs[0] = cfg.store_constant(c * c2);
                    changed = true;
                    continue;
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
                    // println!("DEBUG Mul OPT: {} {} {}", i, is_valid, def);
                    if is_valid {
                        let new_args = def.inputs.clone().iter().map(|v| {
                            let mut in_clone = i.inputs.clone();
                            in_clone[arg_ix] = *v;
                            cfg.value_numbering(OptOp::Mul, &in_clone, None, Some(i.effect))
                        }).collect();

                        i.inputs = new_args;
                        i.op = OptOp::Add;
                        changed = true;
                        continue;
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
                    let other_mul = if defined_at.inputs.len() == 2 {
                        defined_at.inputs[1 - divisor_index]
                    } else {
                        let mut others = defined_at.inputs.clone();
                        others.remove(divisor_index);
                        cfg.value_numbering(OptOp::Mul, &others, None, None)
                    };
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
        //             changed = true; continue;
        //         }
        //     }
        // }

        if OptOp::Sgn == i.op {
            let x = i.inputs[0];
            if let Some(nested) = cfg.get_defined_at(x) {
                // sgn(|a - b|) => condition(a != b)
                if nested.op == OptOp::AbsSub {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    changed = true;
                }
                // sgn(a - b) where a >= b => condition(a != b)
                else if nested.op == OptOp::Sub && *ranges[0].start() >= 0 {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    changed = true;
                }
                // sgn(a - b) where b >= a => a == b ? 0 : -1
                else if nested.op == OptOp::Sub && *ranges[0].end() <= 0 {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], nested.inputs[1]));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_NEG_ONE];
                    changed = true;
                }
                // sgn(digit_sum(a)) => condition(a != 0)
                else if nested.op == OptOp::DigitSum {
                    i.op = OptOp::Select(Condition::Eq(nested.inputs[0], ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    changed = true;
                }
                else if *ranges[0].start() >= 0 {
                    i.op = OptOp::Select(Condition::Eq(x, ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_ONE];
                    changed = true;
                } else if *ranges[0].end() <= 0 {
                    i.op = OptOp::Select(Condition::Eq(x, ValueId::C_ZERO));
                    i.inputs = smallvec![ValueId::C_ZERO, ValueId::C_NEG_ONE];
                    changed = true;
                }
            }
        }

        // used in duplication:
        // a + ((a / 2) + 1) * -2
        // OR a + ((a / 2) * -2 - 2)
        // which is equivalent to (a % 2) - 2
        if OptOp::Add == i.op && !i.inputs[0].is_constant() && i.inputs.len() == 2 && i.inputs[0] != i.inputs[1] {
            let mul_pattern =
                OptOptPattern::new(OptOp::Mul, vec![
                    OptOptPattern::new_const(-2),
                    OptOptPattern::new(OptOp::Add, vec![
                        OptOptPattern::new_const(1),
                        OptOptPattern::new(OptOp::Div, vec![
                            OptOptPattern::new_any().named("v2"),
                            OptOptPattern::new_const(2)
                        ])
                    ])
                ]).or_op(OptOp::Add, vec![
                    OptOptPattern::new_const(-2),
                    OptOptPattern::new(OptOp::Mul, vec![
                        OptOptPattern::new_const(-2),
                        OptOptPattern::new(OptOp::Div, vec![
                            OptOptPattern::new_any().named("v2"),
                            OptOptPattern::new_const(2)
                        ])
                    ])
                ]);
            if let Ok(r) = mul_pattern.try_match(cfg, &i.inputs) {
                let a = r.get_named_single("v2").unwrap();
                if i.inputs.contains(&a) {
                    println!("DEBUG: bingo {:?}", r);
                    // rewrite to (a % 2) - 2
                    let modulo = cfg.value_numbering(OptOp::Mod, &[a, ValueId::C_TWO], None, None);
                    i.op = OptOp::Add;
                    i.inputs = smallvec![ValueId::C_NEG_TWO, modulo];
                    i.effect = OpEffect::None;
                    changed = true;
                }
            }
        }

        // used in duplication:
        // (a / 2 * 2) + (a % 2) which is equivalent to a
        // TODO: do the transform whenever (a / 2 * 2) is used in additive context?
        if OptOp::Add == i.op && !i.inputs[0].is_constant() && i.inputs.len() == 2 && i.inputs[0] != i.inputs[1] {
            let mul_pattern =
                OptOptPattern::new(OptOp::Mul, vec![
                    OptOptPattern::new_constant(2..=i64::MAX).named("div1"),
                    OptOptPattern::new(OptOp::Div, vec![
                        OptOptPattern::new_any().named("v2"),
                        OptOptPattern::new_constant(2..=i64::MAX).named("div2")
                    ])
                ]);
            if let Ok(r) = mul_pattern.try_match(cfg, &i.inputs) {
                if r.get_named_single("div1") == r.get_named_single("div2") {
                    let a = r.get_named_single("v2").unwrap();
                    // let c = cfg.get_constant_(r.get_named_single("div1").unwrap());
                    return (i.with_op(OptOp::Add, &[a], OpEffect::None), None)
                }
            }
        }
    }



    (i, None)
}

// fn get_defs(g: &GraphBuilder, vals: impl Iterator<Item = ValueId>) -> SmallVec<[Option<&OptInstr>; 4]> {
//     vals.map(|v| g.get_defined_at(v)).collect()
// }
fn get_ranges(g: &GraphBuilder, vals: impl Iterator<Item = ValueId>) -> SmallVec<[RangeInclusive<i64>; 4]> {
    vals.map(|v| g.val_range(v)).collect()
}

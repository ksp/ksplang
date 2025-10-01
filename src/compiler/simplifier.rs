use std::{borrow::Cow, cmp, ops::RangeInclusive};

use smallvec::{smallvec, SmallVec, ToSmallVec};

use crate::{compiler::{cfg::GraphBuilder, ops::{InstrId, OpEffect, OptInstr, OptOp, ValueId}, utils::{abs_range, sort_tuple}, vm_code::Condition}, ops::Op, vm::OperationError};

fn overlap(a: RangeInclusive<i64>, b: RangeInclusive<i64>) -> Option<RangeInclusive<i64>> {
    let start = *a.start().max(b.start());
    let end = *a.end().min(b.end());
    if start <= end {
        Some(start..=end)
    } else {
        None
    }
}

pub fn canonicalize_condition(cfg: &mut GraphBuilder, condition: Condition<ValueId>) -> Condition<ValueId> {
    match condition {
        Condition::EqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Eq(a, b))
        }
        Condition::NeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Neq(a, b))
        }
        Condition::LtConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Lt(a, b))
        }
        Condition::LeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Leq(a, b))
        }
        Condition::GtConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Gt(a, b))
        }
        Condition::GeqConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Geq(a, b))
        }
        Condition::DividesConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::Divides(a, b))
        }
        Condition::NotDividesConst(a, b) => {
            let b = cfg.store_constant(b as i64);
            canonicalize_condition(cfg, Condition::NotDivides(a, b))
        }
        Condition::False => Condition::False,
        Condition::True => Condition::True,
        Condition::Eq(a, b) | Condition::Leq(a, b) | Condition::Geq(a, b) | Condition::Divides(a, b)
            if a == b => Condition::True,
        Condition::Neq(a, b) | Condition::Lt(a, b) | Condition::Gt(a, b) | Condition::NotDivides(a, b)
            if a == b => Condition::False,
        Condition::Eq(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if overlap(ar, br).is_none() {
                Condition::False
            } else {
                Condition::Eq(a, b)
            }
        }
        Condition::Neq(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if overlap(ar, br).is_none() {
                Condition::True
            } else {
                Condition::Neq(a, b)
            }
        }
        Condition::Lt(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if ar.end() < br.start() {
                Condition::True
            } else if ar.start() >= br.end() {
                Condition::False
            } else {
                Condition::Lt(a, b)
            }
        }
        Condition::Leq(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if ar.end() <= br.start() {
                Condition::True
            } else if ar.start() > br.end() {
                Condition::False
            } else {
                Condition::Leq(a, b)
            }
        }
        Condition::Gt(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if ar.start() > br.end() {
                Condition::True
            } else if ar.end() <= br.start() {
                Condition::False
            } else {
                Condition::Gt(a, b)
            }
        }
        Condition::Geq(a, b) => {
            let (a, b) = sort_tuple(a, b);
            let ar = cfg.val_range(a);
            let br = cfg.val_range(b);
            if ar.start() >= br.end() {
                Condition::True
            } else if ar.end() < br.start() {
                Condition::False
            } else {
                Condition::Geq(a, b)
            }
        }
        Condition::Divides(a, b) => {
            let ar = abs_range(cfg.val_range(a));
            let br = abs_range(cfg.val_range(b));
            if *ar.end() < *br.start() || *br.end() == 0 {
                return if *ar.start() == 0 {
                    Condition::Eq(b, ValueId::C_ZERO)
                } else {
                    Condition::False
                };
            }
            // if *br.end() > *ar.end() / 2 && ar.start() != 0 {
            //     return Condition::Eq(a, b);
            // }
            if let Some(bc) = cfg.get_constant(b) {
                if bc == 1 || bc == -1 {
                    return Condition::True
                }
                if (*ar.end() / bc.abs_diff(0)) * bc.abs_diff(0) < *ar.start() {
                    return Condition::False;
                }
                if (*ar.end() / bc.abs_diff(0)) * bc.abs_diff(0) < *ar.start() + bc.abs_diff(0) {
                    return Condition::Eq(a, b);
                }
                if bc < 0 && bc != i64::MIN {
                    let b = cfg.store_constant(-bc);
                    return canonicalize_condition(cfg, Condition::Divides(a, b));
                }
            }

            Condition::Divides(a, b)
        }
        Condition::NotDivides(a, b) => {
            canonicalize_condition(cfg, Condition::Divides(a, b)).neg()
        }
    }
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

/// Returns (changed, new instruction)
pub fn simplify_instr(cfg: &mut GraphBuilder, mut i: OptInstr) -> (OptInstr, Option<RangeInclusive<i64>>) {
    if matches!(i.op, OptOp::Nop | OptOp::Pop | OptOp::Push | OptOp::StackSwap | OptOp::Const(_)) {
        return (i, None);
    }
    
    let mut iter = 0;
    'main: loop {
        iter += 1;
        if iter > 100 {
            println!("Warning: simplify_instr infinite loop detected: {i:?}");
            break;
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

        match i.op.clone() {
            OptOp::Condition(cond) => i.op = OptOp::Condition(canonicalize_condition(cfg, cond)),
            OptOp::Select(cond) => i.op = OptOp::Select(canonicalize_condition(cfg, cond)),
            OptOp::Jump(cond, to) => i.op = OptOp::Jump(canonicalize_condition(cfg, cond), to),
            OptOp::Assert(cond, err) => i.op = OptOp::Assert(canonicalize_condition(cfg, cond), err),
            OptOp::DeoptAssert(cond) => i.op = OptOp::DeoptAssert(canonicalize_condition(cfg, cond)),
            x => { }
        };

        let ranges = i.inputs.iter().map(|a| cfg.val_range(*a)).collect::<SmallVec<[_; 4]>>();

        // if i.effect != OpEffect::None {
        //     match &i.op {
        //         OptOp::Add =>
        //     }
        // }

        match &i.op {
            OptOp::Condition(Condition::True) =>
                return (i.with_op(OptOp::Const(1), &[], OpEffect::None), Some(1..=1)),
            OptOp::Condition(Condition::False) =>
                return (i.with_op(OptOp::Const(0), &[], OpEffect::None), Some(0..=0)),
            OptOp::Select(Condition::True) =>
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[0] ], OpEffect::None), None),
            OptOp::Select(Condition::False) =>
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[0] ], OpEffect::None), None),
            // degenerate expressions are all simplified to degenerate Add, which is the only thing user then has to handle
            OptOp::Add | OptOp::Mul | OptOp::And | OptOp::Or | OptOp::Xor | OptOp::Gcd | OptOp::Max | OptOp::Min if i.inputs.len() == 1 =>
                return (i.clone().with_op(OptOp::Add, &i.inputs, OpEffect::None), None),

            OptOp::AbsSub | OptOp::Sub if i.inputs[0] == i.inputs[1] =>
                // abs(a - a) -> 0
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), None),
            
            OptOp::AbsSub => {
                let (start_a, end_a) = ranges[0].clone().into_inner();
                let (start_b, end_b) = ranges[1].clone().into_inner();

                if start_a > end_b {
                    // a - b is always positive
                    i.op = OptOp::Sub;
                } else if start_b > end_a {
                    // b - a is always positive
                    i.op = OptOp::Sub;
                    i.inputs = smallvec![i.inputs[1], i.inputs[0]];
                } else {
                    // ranges overlap, must use abs sub, let's check effect
                    if cmp::max(end_a, end_b).abs_diff(cmp::min(start_a, start_b)) <= i64::MAX as u64 {
                        i.effect = OpEffect::None;
                    }
                    i.inputs.sort();
                }

            }

            OptOp::Mod | OptOp::ModEuclid | OptOp::Div | OptOp::CursedDiv if ranges[1] == (0..=0) =>
                // a % 0 or a / 0 -> always error
                return (i.with_op(OptOp::Assert(Condition::False, OperationError::DivisionByZero), &[], OpEffect::None), None),

            OptOp::Mod | OptOp::ModEuclid if i.inputs[0] == i.inputs[1] => {
                // a % a -> 0
                let br = &ranges[2];
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
            OptOp::Mul if i.inputs.contains(&ValueId::C_ZERO) =>
                // a * 0 -> 0
                return (i.clone().with_op(OptOp::Const(0), &[], OpEffect::None), Some(0..=0)),
            &OptOp::Mul if i.inputs[0] == ValueId::C_ONE =>
                // 1 * a -> a
                return (i.clone().with_op(OptOp::Add, &[ i.inputs[1] ], OpEffect::None), Some(ranges[1].clone())),

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
                return (i.clone().with_op(OptOp::Add, &[ div_2, const_c ], OpEffect::None), None);
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

            _ => {
                break 'main;
            }
        }

        if OptOp::Div == i.op && !i.inputs[0].is_constant() {
            let divisor = i.inputs[1];
            if let Some(defined_at) = cfg.val_info(i.inputs[0])
                                                    .and_then(|i| i.assigned_at)
                                                    .and_then(|id| cfg.get_instruction(id)) {
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
    }



    (i, None)
}

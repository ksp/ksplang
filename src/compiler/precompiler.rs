use std::{cmp, collections::{BTreeSet, HashSet}, ops::RangeInclusive, result, vec};

use num_integer::Integer;
use smallvec::SmallVec;

use crate::{compiler::{cfg::GraphBuilder, ops::{OpEffect, OptOp, ValueId, ValueInfo}, range_ops::{eval_combi, range_num_digits}, utils::{abs_range, add_range, eval_combi_u64, range_2_i64, sort_tuple}, vm_code::Condition}, digit_sum::digit_sum_range, funkcia::funkcia, vm::{self, solve_quadratic_equation, OperationError, QuadraticEquationResult}};

pub struct Options {
    pub allow_pruning: bool
}
impl Default for Options {
    fn default() -> Self {
        Self {
            allow_pruning: true
        }
    }
}

pub trait TraceProvider {
    // type TracePointer
    fn get_results<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = (u32, SmallVec<[i64; 2]>)> + 'a;
    fn is_lazy(&self) -> bool;

    fn get_branch_targets<'a>(&'a mut self, ip: usize) -> impl Iterator<Item = usize>;
    // fn get_push_pop_count(&mut self, ip: usize) -> impl Iterator<Item = (u32, u32)>;
}

pub struct NoTrace();
impl TraceProvider for NoTrace {
    fn get_results<'a>(&'a mut self, _ip: usize) -> impl Iterator<Item = (u32, SmallVec<[i64; 2]>)> + 'a {
        std::iter::empty()
    }
    fn is_lazy(&self) -> bool { false }

    fn get_branch_targets<'a>(&'a mut self, _ip: usize) -> impl Iterator<Item = usize> {
        std::iter::empty()
    }
}

pub struct Precompiler<'a, TP: TraceProvider> {
    pub ops: &'a [crate::ops::Op],
    pub initial_stack_size: usize,
    pub reversed_direction: bool,
    pub initial_position: usize,
    pub g: GraphBuilder,
    // deopt_info: HashMap<u32, DeoptInfo<u32>>,
    pub position: usize,
    pub interpretation_limit: usize,
    pub termination_ip: Option<usize>,
    pub opt: Options,
    pub tracer: TP
}

impl<'a, TP: TraceProvider> Precompiler<'a, TP> {
    pub fn new(
        ops: &'a [crate::ops::Op],
        initial_stack_size: usize,
        reversed_direction: bool,
        initial_position: usize,
        interpretation_limit: usize,
        termination_ip: Option<usize>,
        initial_graph: GraphBuilder,
        tracer: TP
    ) -> Self {
        Self {
            ops,
            initial_stack_size,
            reversed_direction,
            initial_position,
            position: initial_position,
            interpretation_limit,
            g: initial_graph,
            termination_ip,
            opt: Options::default(),
            tracer
        }
    }

    fn next_position(&self) -> usize {
        if self.reversed_direction {
            self.position.wrapping_sub(1)
        } else {
            self.position + 1
        }
    }

    fn instr_add(&mut self, a: ValueId, b: ValueId) -> ValueId {
        let (a, b) = sort_tuple(a, b);
        self.g.value_numbering(OptOp::Add, &[a, b], None, None)
    }

    pub fn step(&mut self) -> Result<(), ()> {
        let op = self.ops[self.position as usize];

        match op {
            crate::ops::Op::Nop => Ok(()),
            crate::ops::Op::Praise => {
                let n = self.g.peek_stack();
                if let Some(constant) = self.g.get_constant(n) {
                    if constant > 100 || constant < 0 {
                        return Err(());
                    }

                    self.g.pop_stack();

                    if constant > 0 {
                        let str = "Mám rád KSP";
                        let mut vals = Vec::new();
                        for chr in str.chars() {
                            vals.push(ValueId::from_predefined_const(chr as i64).unwrap());
                        }

                        for _ in 0..constant {
                            for &v in &vals { self.g.stack.push(v); }
                        }
                    }
                    Ok(())
                } else {
                    Err(())
                }
            }
            crate::ops::Op::Pop => {
                self.g.pop_stack();
                Ok(())
            }
            crate::ops::Op::Pop2 => {
                let orig = self.g.pop_stack();
                self.g.pop_stack();
                self.g.stack.push(orig);
                Ok(())
            }
            crate::ops::Op::Max => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();

                let out = self.g.value_numbering(OptOp::Max, &[a, b], None, None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::LSwap => {
                let x = self.g.peek_stack();
                // TODO: try finding anti-swap
                let out = self.g.push_instr_may_deopt(OptOp::StackSwap, &[ValueId::C_ZERO, x]).out;
                self.g.pop_stack();
                self.g.stack.push(out);

                self.g.push_instr_may_deopt(OptOp::Nop, &[]); // checkpoint after side effect
                Ok(())
            }
            crate::ops::Op::Swap => {
                let (i, x) = self.g.peek_stack_2();
                // let i_range = self.reg_range(i_reg); // TODO: try finding anti-swap

                let out = self.g.push_instr_may_deopt(OptOp::StackSwap, &[i, x]).out;
                self.g.pop_stack();
                self.g.stack.push(out);

                self.g.push_instr_may_deopt(OptOp::Nop, &[]); // after side effect
                Ok(())
            }
            crate::ops::Op::Roll => {
                let (n, x) = self.g.peek_stack_2();

                let Some(n) = self.g.get_constant(n) else {
                    return Err(());
                };

                if n > 128 { return Err(()) }

                if n == 0 {
                    self.g.pop_stack_n(2);
                    return Ok(())
                }

                if n < 0 {
                    self.g.push_assert(Condition::False, OperationError::NegativeLength { value: n }, None);
                    return Ok(())
                }

                if let Some(x) = self.g.get_constant(x) {
                    self.g.pop_stack_n(2);
                    let rotate_by = x.rem_euclid(n);
                    if rotate_by == 0 {
                        return Ok(())
                    }
                    let mut vals = self.g.pop_stack_n(n as usize);
                    println!("Roll({n}, {rotate_by}) {vals:?}");
                    vals[..].rotate_left(rotate_by as usize);
                    println!("        -> {vals:?}");
                    for v in vals.iter().rev() {
                        self.g.stack.push(*v)
                    }
                    return Ok(())
                }

                return Err(()) // TODO:
            }
            crate::ops::Op::FF => Err(()),
            crate::ops::Op::KPi => Err(()),
            crate::ops::Op::Increment => {
                let a = self.g.peek_stack();
                let (start, _end) = self.g.val_range(a).into_inner();
                if start == i64::MAX {
                    return Err(());
                }
                let out = if a.is_constant() {
                    let c = self.g.get_constant_(a);
                    self.g.store_constant(c + 1)
                } else {
                    self.instr_add(a, ValueId::C_ONE)
                };
                self.g.pop_stack();
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Universal => {
                let control = self.g.peek_stack();
                let mut control_range = self.g.val_range(control);
                if *control_range.end() != *control_range.start() {
                    // TODO: fucking hack
                    let info = self.g.val_info(control);
                    if let Some(instr) = info.and_then(|i| i.assigned_at).and_then(|i| self.g.get_instruction(i)) {
                        if instr.op == OptOp::Funkcia {
                            // this will be 0 for sure, nobody uses funkcia for anything else
                            self.g.push_deopt_assert(Condition::EqConst(control, 0), false);
                            control_range = 0..=0;
                        }
                    }
                }
                let out = match control_range.into_inner() {
                    (0, 0) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        self.instr_add(a, b)
                    }
                    (1, 1) => {
                        // abs(a - b)
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();

                        if a == b {
                            ValueId::C_ZERO
                        } else {
                            let (a, b) = sort_tuple(a, b);
                            self.g.value_numbering(OptOp::AbsSub, &[a, b], None, None)
                        }
                    }
                    (2, 2) => {
                        // a * b
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        let (a, b) = sort_tuple(a, b);
                        self.g.value_numbering(OptOp::Mul, &[a, b], None, None)
                    }
                    (3, 3) => {
                        self.g.pop_stack();
                        //  a % b if non-zero, otherwise a / b
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        self.g.value_numbering(OptOp::CursedDiv, &[a, b], None, None)
                    }
                    (4, 4) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        self.g.value_numbering(OptOp::AbsFactorial, &[a], None, None)
                    }
                    (5, 5) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        self.g.value_numbering(OptOp::Sgn, &[a], None, None)
                    }

                    _ => return Err(()),
                };
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Remainder | crate::ops::Op::Modulo => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let euclidean = matches!(op, crate::ops::Op::Modulo);

                let op = if euclidean { OptOp::ModEuclid } else { OptOp::Mod };
                let out = self.g.value_numbering(op, &[a, b], None, None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::TetrationNumIters | crate::ops::Op::TetrationItersNum => {
                let val1 = self.g.pop_stack();
                let val2 = self.g.pop_stack();
                let (num, iters) = if matches!(op, crate::ops::Op::TetrationNumIters) {
                    (val1, val2)
                } else {
                    (val2, val1)
                };

                let num_range = self.g.val_range(num);
                let iters_range = self.g.val_range(iters);

                let range = eval_combi(num_range, iters_range, 16, |num, iters| {
                        vm::tetration(num, iters).ok()
                    });

                let out = self.g.value_numbering(OptOp::Tetration, &[num, iters], range, None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Median => {
                let n = self.g.peek_stack();
                let n_range = self.g.val_range(n);

                if *n_range.end() > 64 || *n_range.end() <= 0 {
                    println!("Median range too crazy: {n} {n_range:?}");
                    return Err(());
                }

                let vals = self.g.peek_stack_n(0..*n_range.end() as usize);
                assert_eq!(n, vals[0]);

                if n_range.start() == n_range.end() {
                    let out = self.g.value_numbering(OptOp::Median, &vals, None, None);
                    self.g.stack.push(out);
                } else {
                    let out = self.g.value_numbering(OptOp::MedianCursed, &vals, None, None);
                    self.g.stack.push(out);
                }
                Ok(())
            }
            crate::ops::Op::DigitSum => {
                let x = self.g.peek_stack();
                let range = self.g.val_range(x);

                if *range.start() >= 0 && *range.end() < 10 {
                    self.g.stack.push(x);
                    return Ok(());
                }

                let out = self.g.value_numbering(OptOp::DigitSum, &[x], None, None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::LenSum => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);

                let range_a = range_num_digits(&a_range);
                let range_b = range_num_digits(&b_range);

                // TODO: fucking hack which will add unnecessary deopts
                let out =
                    if *a_range.start() >= 1 && *a_range.start() < 10 && *a_range.end() <= 11 && *b_range.start() >= 1 && *b_range.start() < 10 && *b_range.end() <= 11 {
                        // this is likely creating a constnant which we could not infer, so let's add a deopt and call it a day
                        if *a_range.end() >= 10 {
                            println!("DEBUG LenSumDeoptHack {a_range:?} {b_range:?} {a}* {b}");
                            self.g.push_deopt_assert(Condition::LtConst(a, 10), false);
                        }
                        if *b_range.end() >= 10 {
                            println!("DEBUG LenSumDeoptHack {a_range:?} {b_range:?} {a} {b}*");
                            self.g.push_deopt_assert(Condition::LtConst(b, 10), false);
                        }
                        ValueId::C_TWO
                    } else {
                        self.g.value_numbering(OptOp::LenSum, &[a, b], Some(add_range(&range_a, &range_b)), None)
                    };

                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Bitshift => {
                let bits = self.g.pop_stack();
                let num = self.g.pop_stack();
                let bits_range = self.g.val_range(bits);
                let num_range = self.g.val_range(num);

                if *bits_range.end() < 0 || *bits_range.start() > 63 {
                    return Err(());
                }

                let out = self.g.value_numbering(OptOp::ShiftL, &[num, bits], None, None);
                    // let (num_start, num_end) = num_range.into_inner(); // TODO: migrate to simplifier
                    // let (bits_start, bits_end) = bits_range.into_inner();

                    // let max_shift = 1u64 << bits_end.clamp(0, 63);
                    // let min_shift = 1u64 << bits_start.clamp(0, 63);

                    // let candidates = [
                    //     (num_start as u64).saturating_mul(min_shift) as i64,
                    //     (num_start as u64).saturating_mul(max_shift) as i64,
                    //     (num_end as u64).saturating_mul(min_shift) as i64,
                    //     (num_end as u64).saturating_mul(max_shift) as i64,
                    // ];

                    // let min_result = *candidates.iter().min().unwrap();
                    // let max_result = *candidates.iter().max().unwrap();
                    // info.range = min_result..=max_result;
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::And => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);
                let range = eval_combi(a_range, b_range, 1024, |a, b| Some(a & b));

                let out = self.g.value_numbering(OptOp::And, &[a, b], range, None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Funkcia => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);

                let (a_start, a_end) = self.g.val_range(a).into_inner();
                let (b_start, b_end) = self.g.val_range(b).into_inner();

                if a == b || a_end <= 1 && b_end <= 1 {
                    self.g.stack.push(ValueId::C_ZERO);
                    return Ok(());
                }

                let range = eval_combi(
                    cmp::min(cmp::max(1, a_start), a_end)..=a_end,
                    cmp::min(cmp::max(1, b_start), b_end)..=b_end,
                    256,
                    |a, b: i64| Some(funkcia(a, b) as i64),
                );

                let out = self.g.value_numbering(OptOp::Funkcia, &[a, b], None, None);

                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Gcd2 => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = abs_range(self.g.val_range(a));
                let b_range = abs_range(self.g.val_range(b));
                let range = eval_combi_u64(a_range.clone(), b_range.clone(), 256, |a, b| {
                        Some(a.gcd(&b))
                    });

                let out = self.g.value_numbering(OptOp::Gcd, &[a, b], range.map(range_2_i64), None);
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::GcdN => {
                let n = self.g.peek_stack();
                let Some(n_const) = self.g.get_constant(n) else {
                    return Err(())
                };

                if n_const > 128 || n_const <= 0 {
                    return Err(())
                }

                self.g.pop_stack();
                let vals = self.g.pop_stack_n(n_const as usize);
                // TODO: migrate to simplifier
                // let (constants, vals): (BTreeSet<ValueId>, BTreeSet<ValueId>) = vals.iter().partition(|x| x.is_constant());
                // let constants: Vec<i64> = constants.into_iter().map(|c| self.g.get_constant_(c)).collect();
                // let const_gcd = constants.into_iter().map(|v| v.abs_diff(0)).reduce(|a, b| a.gcd(&b));

                // if const_gcd == Some(1) || vals.len() == 0 {
                //     if const_gcd.unwrap() > i64::MAX as u64 {
                //         self.g.push_instr_internal(OptOp::Assert(Condition::False, OperationError::IntegerOverflow), &[], ValueId(0));
                //         return Ok(());
                //     }
                //     let result = self.g.store_constant(const_gcd.unwrap() as i64);
                //     self.g.stack.push(result);
                //     return Ok(());
                // }

                // let ranges: Vec<RangeInclusive<u64>> = vals.iter().map(|v| abs_range(self.g.val_range(*v))).collect();

                // if const_gcd == None && vals.len() == 1 {
                //     let val = *vals.first().unwrap();
                //     if *ranges[0].end() > i64::MAX as u64 {
                //         self.g.push_assert(Condition::Neq(val, ValueId::C_IMIN), OperationError::IntegerOverflow, None);
                //     }
                //     self.g.stack.push(val);
                //     return Ok(());
                // }

                // let min_end = ranges.iter().map(|r| *r.end())
                //     .chain(const_gcd).max().unwrap();

                // let all_zero: bool = matches!(const_gcd, Some(0) | None) && ranges.iter().all(|r| *r.start() == 0);
                // let out_range = if all_zero { 0 } else { 1 }..=min_end;

                // // `as i64` will correctly convert to i64::MIN
                // let args: Vec<ValueId> = vals.iter().copied()
                //                                     .chain(const_gcd.map(|c| self.g.store_constant(c as i64)))
                //                                     .collect();

                let result = self.g.value_numbering(OptOp::Gcd, &vals, None, None);

                self.g.stack.push(result);

                Ok(())
            },
            crate::ops::Op::Qeq => {
                let (a, b, c) = self.g.peek_stack_3();
                let (a_start, a_end) = self.g.val_range(a).into_inner();
                let (b_start, b_end) = self.g.val_range(b).into_inner();
                let (c_start, c_end) = self.g.val_range(c).into_inner();

                if self.g.get_constant(a) == Some(0) {
                    self.g.pop_stack_n(3);

                    if self.g.get_constant(b) == Some(0) {
                        // equation is `c == 0`
                        if c_start <= 0 && c_end >= 0 {
                            let cond = if (c_start, c_end) == (0, 0) {
                                Condition::False
                            } else {
                                Condition::NeqConst(c, 0)
                            };
                            self.g.push_assert(cond, OperationError::QeqZeroEqualsZero, None);
                        }

                        // zero solutions:
                        return Ok(())
                    }

                    if b_start <= 0 && b_end >= 0 {
                        self.g.push_deopt_assert(Condition::NeqConst(b, 0), false);
                    }

                    if b_start == 1 && b_end == 1 {
                        // -c
                        let r = self.g.value_numbering(OptOp::Sub, &[ValueId::C_ZERO, c], None, None);
                        self.g.stack.push(r);
                        return Ok(())
                    }

                    // result = -(c / b) assuming b divides c
                    let can_overflow = a_start == i64::MIN && b_start <= 1 && b_end >= 1;
                    let mut must_assert_divisibility = false;
                    let out_range = eval_combi(c_start..=c_end, b_start..=b_end, 256, |c, b| {
                            if c % b == 0 { Some(c / b) }
                            else { must_assert_divisibility = true; None }
                    });

                    if out_range.as_ref().is_some_and(|r| r.is_empty()) {
                        self.g.push_assert(Condition::False, OperationError::IntegerOverflow, None);
                        return Ok(())
                    }
                    if (must_assert_divisibility || out_range.is_none()) &&
                        !matches!((b_start, b_end), (1, 1) | (-1, -1) | (-1, 1)) {

                        self.g.push_deopt_assert(Condition::Divides(c, b), false);
                    }

                    let (elide_neg, dividend, divisor) = if b_start == b_end && b_start != i64::MIN {
                        (true, c, self.g.store_constant(-b_start))
                    } else if c_start == c_end && c_start != i64::MIN {
                        (true, self.g.store_constant(-c_end), b)
                    } else {
                        (false, c, b)
                    };

                    // overflow will happen even when it shouldn't for
                    // c == i64::MIN, b==-1 (but neither is recognized as constant)
                    if !elide_neg && c_start == i64::MIN && b_start <= -1 && b_end >= -1 {
                        // TODO: test this shit
                        self.g.push_deopt_assert(Condition::Neq(c, ValueId::C_IMIN), false);
                    }

                    let negated_range =
                        out_range.as_ref().map(|r| r.end().saturating_neg()..=r.start().saturating_neg())
                                          .unwrap_or(i64::MIN+1..=i64::MAX);

                    let div = self.g.value_numbering(OptOp::Div, &[dividend, divisor], if elide_neg { Some(negated_range.clone()) } else { out_range.clone() }, Some(OpEffect::None)); // all failures must be handled specially here

                    if !elide_neg {
                        let neg = self.g.value_numbering(OptOp::Sub, &[ValueId::C_ZERO, div],
                            Some(negated_range),
                            Some(if can_overflow { OpEffect::MayFail } else { OpEffect::None })
                        );
                        self.g.stack.push(neg);
                    } else {
                        self.g.stack.push(div);
                    }

                    return Ok(())
                }

                if a_start == a_end && b_start == b_end && c_start == c_end {
                    // all constants
                    self.g.pop_stack_n(3);
                    match solve_quadratic_equation(a_start, b_start, c_start) {
                        Ok(QuadraticEquationResult::None) => {},
                        Ok(QuadraticEquationResult::One(sol1)) => {
                            let sol1 = self.g.store_constant(sol1);
                            self.g.stack.push(sol1);
                        },
                        Ok(QuadraticEquationResult::Two(sol1, sol2)) => {
                            let sol1 = self.g.store_constant(sol1);
                            let sol2 = self.g.store_constant(sol2);
                            self.g.stack.push(sol1);
                            self.g.stack.push(sol2);
                        },
                        Err(error) => {
                            self.g.push_assert(Condition::False, error, None);
                        }
                    }
                    return Ok(())
                }

                Err(())
            },
            crate::ops::Op::BulkXor => {
                let n = self.g.peek_stack();
                let Some(n) = self.g.get_constant(n) else {
                    return Err(())
                };
                if n < 0 || n > 2 * self.g.stack.stack.len() as i64 + 64 {
                    return Err(())
                }

                let vals = self.g.peek_stack_n(1..n as usize * 2 + 1);
                let mut xors = vec![];
                for i in 0..(n as usize) {
                    let (a, b) = (vals[i * 2], vals[i * 2 + 1]);
                    let ar = self.g.val_range(a);
                    let br = self.g.val_range(b);
                    if *ar.start() > 0 && *br.start() > 0 {
                        xors.push(Ok(ValueId::C_ONE))
                    } else if *ar.start() > 0 && *br.end() <= 0 {
                        xors.push(Ok(ValueId::C_ZERO))
                    } else if *ar.end() <= 0 && *br.end() > 0 {
                        xors.push(Ok(ValueId::C_ZERO))
                    } else if *ar.end() <= 0 && *br.end() <= 0 {
                        xors.push(Ok(ValueId::C_ONE))
                    } else {
                        xors.push(Err((a, ar, b, br)))
                    }
                }

                if xors.iter().filter(|x| x.is_err()).count() > 8 {
                    return Err(())
                }

                self.g.pop_stack_n(n as usize + 1);

                for x in xors {
                    match x {
                        Ok(c) => self.g.stack.push(c),
                        Err((a, ar, b, br)) => {
                            let mut try_opt = |ar: RangeInclusive<i64>, b: ValueId, br: RangeInclusive<i64>| {
                                if *ar.end() <= 0 { // 0 ^ b
                                    if br == (0..=1) {
                                        Some(b)
                                    } else {
                                        Some(self.g.value_numbering(OptOp::Condition(Condition::GtConst(b, 0)), &[], None, None))
                                    }
                                } else if *ar.start() > 0 { // 1 ^ b
                                    Some(self.g.value_numbering(OptOp::Condition(Condition::LeqConst(b, 0)), &[], None, None))
                                } else {
                                    None
                                }
                            };

                            let r = try_opt(ar.clone(), b, br.clone())
                                .or_else(|| try_opt(br, a, ar))
                                .unwrap_or_else(|| {
                                    let a_cond = self.g.value_numbering(OptOp::Condition(Condition::GtConst(a, 0)), &[], None, None);
                                    let b_cond = self.g.value_numbering(OptOp::Condition(Condition::GtConst(b, 0)), &[], None, None);
                                    self.g.value_numbering(OptOp::Condition(Condition::Neq(a_cond, b_cond)), &[], None, None)
                                });
                            self.g.stack.push(r);
                        }
                    }
                }

                Ok(())
            },
            crate::ops::Op::BranchIfZero => todo!(),
            crate::ops::Op::Call => todo!(),
            crate::ops::Op::Goto => todo!(),
            crate::ops::Op::Jump => todo!(),
            crate::ops::Op::Rev => Err(()),
            crate::ops::Op::Sleep => Err(()),
            crate::ops::Op::Deez => Err(()),
            crate::ops::Op::Sum => Err(()),
        }
    }


    pub fn interpret(&mut self) -> () {
        loop {
            if self.termination_ip == Some(self.position) || self.position >= self.ops.len() {
                break;
            }
            if self.g.stack.stack.len() + 1 >= self.initial_stack_size {
                break;
            }
            if self.interpretation_limit == 0 {
                break;
            }
            self.interpretation_limit -= 1;

            self.g.set_program_position(Some(self.position));
            println!("Interpreting op {}: {:?}", self.position, self.ops[self.position]);

            println!("  Stack: {}", self.g.fmt_stack());
            println!("  Current Block: {}", self.g.current_block_ref());

            let stack_counts = (self.g.stack.push_count, self.g.stack.pop_count);
            let result = self.step();
            match result {
                Ok(()) => {}
                Err(()) => {
                    if stack_counts != (self.g.stack.push_count, self.g.stack.pop_count) {
                        panic!("Error when interpreting OP {} {:?}: modifed stack, but then returned Err()", self.position, self.ops[self.position])
                    }
                    break;
                }
            }


            if self.opt.allow_pruning {
                self.g.clean_poped_values();
            }

            self.position = self.next_position();
        }

        self.g.set_program_position(Some(self.position));
        self.g.push_instr_may_deopt(OptOp::DeoptAssert(Condition::False), &[]);
        self.g.set_program_position(None);
        println!("F Stack: {}", self.g.fmt_stack());
        println!("  FINAL   Block: {}", self.g.current_block_ref());
    }
}

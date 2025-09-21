use std::{cmp, collections::HashSet, ops::RangeInclusive};

use num_integer::Integer;

use crate::{compiler::{cfg::{GraphBuilder, OpEffect, OptOp, ValueId}, utils::{abs_range, eval_combi, eval_combi_u64, median, sort_tuple, u64neg}, vm_code::Condition}, digit_sum::digit_sum_range, funkcia::funkcia, vm::{self, OperationError}};

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

pub struct Precompiler<'a> {
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
}

impl<'a> Precompiler<'a> {
    pub fn new(
        ops: &'a [crate::ops::Op],
        initial_stack_size: usize,
        reversed_direction: bool,
        initial_position: usize,
        interpretation_limit: usize,
        termination_ip: Option<usize>,
        initial_graph: GraphBuilder,
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
        let (start_a, end_a) = self.g.val_range(a).into_inner();
        let (start_b, end_b) = self.g.val_range(b).into_inner();
        let start = start_a.saturating_add(start_b);
        let end = end_a.saturating_add(end_b);
        self.g.value_numbering(OptOp::Add, vec![a, b], |info: &mut crate::compiler::cfg::ValueInfo| {
            info.range = start..=end;
        }, |instr| {
            let can_overflow = start_a.checked_add(start_b).is_none() || end_a.checked_add(end_b).is_none();
            instr.effect = if can_overflow { OpEffect::MayFail } else { OpEffect::None };
        })
    }

    // fn instr_sub(&mut self, a: u32, b: u32) -> u32 {
    //     let (start_a, end_a) = self.reg_range(a).into_inner();
    //     let (start_b, end_b) = self.reg_range(b).into_inner();
    //     let start = start_a.saturating_sub(end_b);
    //     let end = end_a.saturating_sub(start_b);
    //     self.graph.value_numbering(PrecompiledOp::Sub(0, a, b), |this| {
    //         let out = this.new_register(move |info| {
    //             info.range = start..=end;
    //         });
    //         this.push_instr(PrecompiledOp::Sub(out, a, b));
    //         out
    //     })
    // }

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
                        let mut regs = Vec::new();
                        for chr in str.chars() {
                            let reg = self.g.store_constant(chr as i64);
                            regs.push(reg);
                        }

                        for _ in 0..constant {
                            for &reg in &regs {
                                self.g.stack.push(reg);
                            }
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
                let range_a = self.g.val_range(a).into_inner();
                let range_b = self.g.val_range(b).into_inner();
                let range = cmp::max(range_a.0, range_b.0)..=cmp::max(range_a.1, range_b.1);

                let out = self.g.value_numbering(OptOp::Max, vec![a, b], |info| {
                    info.range = range;
                }, |_|{});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::LSwap => {
                let x = self.g.peek_stack();
                let zero = self.g.store_constant(0);
                let out = self.g.new_value().id;
                // TODO: try finding anti-swap
                self.g.push_instr_may_deopt(OptOp::StackSwap, &[zero, x], out);
                self.g.pop_stack();
                self.g.stack.push(out);

                self.g.push_instr_may_deopt(OptOp::Nop, &[], ValueId(0)); // after side effect
                Ok(())
            }
            crate::ops::Op::Swap => {
                let (i, x) = self.g.peek_stack_2();
                // let i_range = self.reg_range(i_reg); // TODO: try finding anti-swap

                let out = self.g.new_value().id;
                // self.save_deopt(|_|{ });
                self.g.push_instr_may_deopt(OptOp::StackSwap, &[i, x], out);
                self.g.pop_stack();
                self.g.stack.push(out);

                self.g.push_instr_may_deopt(OptOp::Nop, &[], ValueId(0)); // after side effect
                Ok(())
            }
            crate::ops::Op::Roll => {
                let (n, x) = self.g.peek_stack_2();
                let n_range = self.g.val_range(n);
                let x_range = self.g.val_range(x);

                // TODO

                Err(())
            }
            crate::ops::Op::FF => Err(()),
            crate::ops::Op::KPi => Err(()),
            crate::ops::Op::Increment => {
                let a = self.g.peek_stack();
                let (start, _end) = self.g.val_range(a).into_inner();
                if start == i64::MAX {
                    return Err(());
                }
                let one = self.g.store_constant(1);
                let out = self.instr_add(a, one);
                self.g.pop_stack();
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Universal => {
                let control = self.g.peek_stack();
                let control_range = self.g.val_range(control);
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
                        let (start_a, end_a) = self.g.val_range(a).into_inner();
                        let (start_b, end_b) = self.g.val_range(b).into_inner();

                        if start_a > end_b {
                            // a - b is always positive
                            self.g.value_numbering(OptOp::Sub, vec![a, b], |info| {
                                info.range =
                                    start_a.saturating_sub(end_b)..=end_a.saturating_sub(start_b)
                            }, |instr| {
                                let can_overflow = start_a.checked_sub(end_b).is_none() || end_a.checked_sub(start_b).is_none();
                                instr.effect = if can_overflow { OpEffect::MayFail } else { OpEffect::None };
                            })
                        } else if start_b > end_a {
                            // b - a is always positive
                            self.g.value_numbering(OptOp::Sub, vec![b, a], |info| {
                                info.range =
                                    start_b.saturating_sub(end_a)..=end_b.saturating_sub(start_a)
                            }, |instr| {
                                let can_overflow = start_b.checked_sub(end_a).is_none() || end_b.checked_sub(start_a).is_none();
                                instr.effect = if can_overflow { OpEffect::MayFail } else { OpEffect::None };
                            })
                        } else {
                            // ranges overlap, must use abs sub
                            let (a, b) = sort_tuple(a, b);
                            self.g.value_numbering(OptOp::AbsSub, vec![a, b], |info| {
                                let start = 0;
                                let end = cmp::max(end_a, end_b) - cmp::min(start_a, start_b);
                                info.range = start..=end;
                            }, |instr| {
                                // TODO: may fail?
                            })
                        }
                    }
                    (2, 2) => {
                        // a * b
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        let (a, b) = sort_tuple(a, b);
                        let (start_a, end_a) = self.g.val_range(a).into_inner();
                        let (start_b, end_b) = self.g.val_range(b).into_inner();
                        self.g.value_numbering(OptOp::Mul, vec![a, b], |info| {
                            let points = [
                                start_a.saturating_mul(start_b),
                                start_a.saturating_mul(end_b),
                                end_a.saturating_mul(start_b),
                                end_a.saturating_mul(end_b),
                            ];
                            info.range =
                                *points.iter().min().unwrap()..=*points.iter().max().unwrap();
                        }, |instr| {
                            // TODO: may overflow?
                        })
                    }
                    (3, 3) => {
                        self.g.pop_stack();
                        //  a % b if non-zero, otherwise a / b
                        let a = self.g.pop_stack();
                        let b = self.g.pop_stack();
                        // let (start_a, end_a) = self.reg_range(a).into_inner();
                        let (start_b, end_b) = self.g.val_range(b).into_inner();
                        // TODO: try to detect pattern of division? (depends on dup detection, so ...)
                        // TODO: ranges
                        self.g.value_numbering(OptOp::CursedDiv, vec![a, b], |_info| {
                            // let points = [
                            //     if end_b != 0 { start_a.saturating_div(end_b) } else { i64::MIN },
                            //     if end_b != 0 { end_a.saturating_div(end_b) } else { i64::MIN },
                            //     if start_b != 0 { start_a.saturating_div(start_b) } else { i64::MIN },
                            //     if start_b != 0 { end_a.saturating_div(start_b) } else { i64::MIN },
                            //     if end_b != 0 { start_a.saturating_rem(end_b) } else { i64::MIN },
                            //     if end_b != 0 { end_a.saturating_rem(end_b) } else { i64::MIN },
                            //     if start_b != 0 { start_a.saturating_rem(start_b) } else { i64::MIN },
                            //     if start_b != 0 { end_a.saturating_rem(start_b) } else { i64::MIN },
                            // ];
                            // info.range = *points.iter().min().unwrap()..=*points.iter().max().unwrap();
                        }, |instr| {
                            // div by zero
                            instr.effect = if start_b <= 0 && end_b >= 0 { OpEffect::MayFail } else { OpEffect::None };
                        })
                    }
                    (4, 4) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        self.g.value_numbering(OptOp::AbsFactorial, vec![a], |info| {
                            info.range = 1..=2432902008176640000; // TODO
                        }, |instr| {})
                    }
                    (5, 5) => {
                        self.g.pop_stack();
                        let a = self.g.pop_stack();
                        let (start_a, end_a) = self.g.val_range(a).into_inner();
                        self.g.value_numbering(OptOp::Sgn, vec![a], |info| {
                            info.range = start_a.signum()..=end_a.signum();
                        }, |_| {})
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
                let (start_a, end_a) = self.g.val_range(a).into_inner();
                let (start_b, end_b) = abs_range(self.g.val_range(b)).into_inner();

                if a == b || (start_a == end_a && start_a == start_b as i64 && start_b == end_b) {
                    if start_b <= 0 && end_b >= 0 {
                        self.g.push_instr(
                            OptOp::Assert(
                                Condition::NeqConst(a, 0),
                                OperationError::DivisionByZero,
                                None,
                            ),
                            &[a],
                            ValueId(0),
                        );
                    }
                    let zero = self.g.store_constant(0);
                    self.g.stack.push(zero);
                    return Ok(());
                }

                let range = if euclidean {
                    if start_b > end_a.abs_diff(0) && start_a >= 0 {
                        start_a..=end_a
                    } else {
                        0..=(end_b - 1) as i64
                    }
                } else {
                    if start_a >= end_a.saturating_neg() && (start_b as i64) > end_a {
                        start_a..=end_a
                    } else {
                        u64neg(end_b)..=(end_b - 1) as i64
                    }
                };

                let op = if euclidean { OptOp::ModEuler } else { OptOp::Mod };
                let out = self.g.value_numbering(op, vec![a, b], |info| {
                    info.range = range;
                }, |instr| {
                    instr.effect = if start_b <= 0 && end_b >= 0 { OpEffect::MayFail } else { OpEffect::None };
                });
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

                let out = self.g.value_numbering(OptOp::Tetration, vec![num, iters], |info| {
                    let range = eval_combi(num_range, iters_range, 16, |num, iters| {
                        vm::tetration(num, iters).ok()
                    })
                    .unwrap_or(i64::MIN..=i64::MAX);
                    info.range = range;
                }, |_|{});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Median => {
                let n = self.g.peek_stack();
                let n_range = self.g.val_range(n);

                if *n_range.end() > 64 || *n_range.end() <= 0 {
                    return Err(());
                }

                let vals = self.g.peek_stack_n(0..*n_range.end() as usize);
                assert_eq!(n, vals[0]);
                let ranges: Vec<_> = vals.iter().map(|&v| self.g.val_range(v)).collect();
                let mut starts: Vec<i64> = ranges.iter().map(|r| *r.start()).collect();
                let mut ends: Vec<i64> = ranges.iter().map(|r| *r.end()).collect();
                assert_eq!(starts.len(), *n_range.end() as usize);

                let mut min_start = i64::MAX;
                let mut max_start = i64::MIN;
                for i in n_range.clone() {
                    let med_start = median(&mut starts[..i as usize]);
                    let med_end = median(&mut ends[..i as usize]);
                    min_start = cmp::min(min_start, med_start);
                    max_start = cmp::max(max_start, med_end);
                }
                let out_range = min_start..=max_start;

                if n_range.start() == n_range.end() {
                    let out = self.g.value_numbering(OptOp::Median, vals, |info| {
                        info.range = out_range;
                    }, |_| {});
                    self.g.stack.push(out);
                    Ok(())
                } else {
                    let out = self.g.value_numbering(OptOp::MedianCursed, vals, |info| {
                        info.range = out_range;
                    }, |instr| {
                        // we only get here if n_range has an upper bound -> deopt cannot occur, but it can still fail on <=zero
                        instr.effect = if *n_range.start() <= 0 { OpEffect::MayFail } else { OpEffect::None };
                    });
                    self.g.stack.push(out);
                    Ok(())
                }
            }
            crate::ops::Op::DigitSum => {
                let x = self.g.peek_stack();
                let range = self.g.val_range(x);

                if *range.end() < 10 {
                    self.g.stack.push(x);
                    return Ok(());
                }

                let out_range = digit_sum_range(range);
                let out = self.g.value_numbering(OptOp::DigitSum, vec![x], |info| {
                    info.range = out_range;
                }, |_|{});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::LenSum => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);

                fn num_digits(r: RangeInclusive<i64>) -> RangeInclusive<i64> {
                    let max = cmp::max(r.start().abs_diff(0), r.end().abs_diff(0));
                    let min = if *r.start() <= 0 && *r.end() >= 0 {
                        0
                    } else {
                        cmp::min(r.start().abs_diff(0), r.end().abs_diff(0))
                    };

                    vm::decimal_len(u64neg(min))..=vm::decimal_len(u64neg(max))
                }

                let out = self.g.value_numbering(OptOp::LenSum, vec![a, b], |info| {
                    let range_a = num_digits(a_range);
                    let range_b = num_digits(b_range);
                    info.range = (*range_a.start() + *range_b.start())..=(*range_a.end() + *range_b.end());
                }, |_|{});
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

                let out = self.g.value_numbering(OptOp::ShiftL, vec![num, bits], |info| {
                    let (num_start, num_end) = num_range.into_inner();
                    let (bits_start, bits_end) = bits_range.into_inner();

                    let max_shift = 1u64 << bits_end.clamp(0, 63);
                    let min_shift = 1u64 << bits_start.clamp(0, 63);

                    let candidates = [
                        (num_start as u64).saturating_mul(min_shift) as i64,
                        (num_start as u64).saturating_mul(max_shift) as i64,
                        (num_end as u64).saturating_mul(min_shift) as i64,
                        (num_end as u64).saturating_mul(max_shift) as i64,
                    ];

                    let min_result = *candidates.iter().min().unwrap();
                    let max_result = *candidates.iter().max().unwrap();
                    info.range = min_result..=max_result;
                }, |_| {});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::And => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = self.g.val_range(a);
                let b_range = self.g.val_range(b);

                let out = self.g.value_numbering(OptOp::And, vec![a, b], |info| {
                    let (a_start, a_end) = a_range.into_inner();
                    let (b_start, b_end) = b_range.into_inner();

                    info.range =
                        eval_combi(a_start..=a_end, b_start..=b_end, 256, |a, b| Some(a & b))
                            .unwrap_or(
                                0..=(cmp::min(a_end as u64, b_end as u64).saturating_mul(2) as i64),
                            ) // TODO: less dumb heuristic
                }, |_| {});
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
                    let zero = self.g.store_constant(0);
                    self.g.stack.push(zero);
                    return Ok(());
                }

                let out = self.g.value_numbering(OptOp::Funkcia, vec![a, b], |info| {
                    info.range = eval_combi(
                        cmp::max(1, a_start)..=a_end,
                        cmp::max(1, b_start)..=b_end,
                        256,
                        |a, b: i64| Some(funkcia(a, b) as i64),
                    )
                    .unwrap_or_else(|| {
                        // can be at most a * b or FUNKCIA_MOD - 1
                        let max = cmp::min(1_000_000_007 - 1, a_end.saturating_mul(b_end));
                        0..=max
                    });
                }, |_| {});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::Gcd2 => {
                let a = self.g.pop_stack();
                let b = self.g.pop_stack();
                let (a, b) = sort_tuple(a, b);
                let a_range = abs_range(self.g.val_range(a));
                let b_range = abs_range(self.g.val_range(b));

                let out = self.g.value_numbering(OptOp::Gcd, vec![a, b], |info| {
                    let range = eval_combi_u64(a_range.clone(), b_range.clone(), 256, |a, b| {
                        Some(a.gcd(&b))
                    })
                    .unwrap_or_else(|| {
                        let min =
                            if a_range.start() == &0 && b_range.start() == &0 { 0 } else { 1 };
                        let max = cmp::min(*a_range.end(), *b_range.end());
                        min..=max
                    });
                    info.range = (*range.start() as i64)..=(*range.end() as i64);
                }, |_| {});
                self.g.stack.push(out);
                Ok(())
            }
            crate::ops::Op::GcdN => Err(()),
            crate::ops::Op::Qeq => todo!(),
            crate::ops::Op::BulkXor => todo!(),
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
            let result = self.step();
            match result {
                Ok(()) => {}
                Err(()) => break,
            }

            println!("  Stack: {}", self.g.fmt_stack());
            println!("  Current Block: {}", self.g.current_block_ref());

            if self.opt.allow_pruning {
                self.g.clean_poped_values();
            }

            self.position = self.next_position();
        }

        self.g.set_program_position(Some(self.position));
        self.g.push_instr_may_deopt(OptOp::Deopt(Condition::True), &[], ValueId(0));
        self.g.set_program_position(None);
    }
}

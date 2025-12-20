use core::fmt;
use std::{cmp, collections::{BTreeMap, BTreeSet, BinaryHeap}, mem, u32};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::{SmallVec, smallvec};

use crate::compiler::{analyzer::dataflow, cfg::{BasicBlock, GraphBuilder}, ops::{BlockId, InstrId, OpEffect, OptInstr, OptOp, ValueId}, osmibytecode::{Condition, DeoptInfo, OsmibyteOp, OsmibytecodeBlock, RegId}, utils::{AssertInto, SaturatingInto}};
use crate::vm::OperationError;

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Compiler<'a> {
    g: &'a GraphBuilder,
    program: Vec<OsmibyteOp<RegId>>,
    large_constants: Vec<i64>,
    large_constant_lookup: BTreeMap<i64, u16>,
    deopts: Vec<DeoptInfo>,
    deopts_lookup: HashMap<DeoptInfo, u32>,
    ip2deopt: BTreeMap<u32, u32>,
    block_starts: BTreeMap<BlockId, u16>,
    register_allocation: RegisterAllocation,
    jump_fixups: Vec<(usize, BlockId)>,
    temp_regs: TempRegPool,
    current_deopt: Option<DeoptInfo>,
}


#[derive(Clone, Copy, Debug)]
enum OutputSpec {
    Register(RegId),
    Spill { reg: RegId, slot: u32 },
}

impl OutputSpec {
    fn target_reg(&self) -> RegId {
        match self {
            OutputSpec::Register(reg) => *reg,
            OutputSpec::Spill { reg, .. } => *reg,
        }
    }
    fn load_instr(&self) -> Option<OsmibyteOp<RegId>> {
        match self {
            OutputSpec::Register(_) => None,
            OutputSpec::Spill { reg, slot } => Some(OsmibyteOp::Unspill(*reg, *slot))
        }
    }
}

impl<'a> Compiler<'a> {
    pub fn new(g: &'a GraphBuilder, register_allocation: RegisterAllocation) -> Self {
        Self {
            g,
            program: Vec::new(),
            large_constants: Vec::new(),
            large_constant_lookup: BTreeMap::new(),
            deopts: Vec::new(),
            deopts_lookup: HashMap::default(),
            ip2deopt: BTreeMap::new(),
            block_starts: BTreeMap::new(),
            register_allocation,
            jump_fixups: Vec::new(),
            temp_regs: TempRegPool::new(),
            current_deopt: None
        }
    }

    pub fn compile(&mut self) {
        for block in &self.g.blocks {
            let start = self.program.len();
            let start_u16: u16 = start.try_into().expect("precompiled program exceeds 65535 ops");
            self.block_starts.insert(block.id, start_u16);
            self.compile_block(block);
        }
    }

    fn compile_block(&mut self, block: &BasicBlock) {
        self.current_deopt = self.prepare_block_deopt(block.id);
        let instrs: Vec<_> = block.instructions.values().collect();
        let mut i = 0;
        let mut added_increment = false;
        while i < instrs.len() {
            if matches!(&instrs[i].op, OptOp::Jump(_, _)) && !added_increment {
                added_increment = true;

                if block.ksplang_instr_count != 0 {
                    self.program.push(OsmibyteOp::KsplangOpsIncrement(block.ksplang_instr_count as i32));
                    if let Some(deopt) = &mut self.current_deopt {
                        deopt.ksplang_ops_increment -= block.ksplang_instr_count as i64;
                    }
                }
            }
            let consumed = self.compile_instruction(&instrs[i..]);
            assert_ne!(0, consumed);
            i += consumed;
        }
        assert_eq!(i, instrs.len())
    }

    /// Returns the number of instructions consumed (1 or more).
    fn compile_instruction(&mut self, instrs: &[&OptInstr]) -> usize {
        use OptOp::*;
        let instr = instrs[0];
        let mut consumed = 1;

        fn follows_checkpoint(instrs: &[&OptInstr]) -> bool {
            for i in &instrs[1..] {
                if i.op == OptOp::Checkpoint {
                    return true
                }
                if i.effect != OpEffect::None {
                    return false
                }
            }
            return false
        }

        match &instr.op {
            Const(_) => panic!("Special op, should not be in CfG"),
            Add => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Add(out, a, b), |out, a, c| Some(OsmibyteOp::AddConst(out, a, c.try_into().ok()?))),
            Mul => self.lower_mul(instr),
            Sub => self.lower_binary(instr, |out, a, b| OsmibyteOp::Sub(out, a, b), |_, _, _| None, |out, c, b| Some(OsmibyteOp::SubConst(out, c.try_into().ok()?, b))),
            AbsSub => self.lower_variadic(instr, |out, a, b| OsmibyteOp::AbsSub(out, a, b), |out, a, c| Some(OsmibyteOp::AbsSubConst(out, a, c.try_into().ok()?))),
            Div => return self.lower_div(instrs),
            CursedDiv => self.lower_binary(instr, |out, a, b| OsmibyteOp::CursedDiv(out, a, b), |_, _, _| None, |_, _, _| None),
            Mod => {
                let lhs_range = self.g.val_range_at(instr.inputs[0], instr.id);
                let lhs_non_negative = *lhs_range.start() >= 0;
                self.lower_binary(instr, |out, a, b| OsmibyteOp::Mod(out, a, b), {
                    move |out, a, c| {
                        let c: i32 = c.try_into().ok()?;
                        if c > 0 && (c as u64).is_power_of_two() && lhs_non_negative {
                            Some(OsmibyteOp::AndConst(out, a, c.wrapping_sub(1)))
                        } else {
                            Some(OsmibyteOp::ModConst(out, a, c))
                        }
                    }
                }, |_, _, _| None);
            }
            ModEuclid => {
                self.lower_binary(instr, |out, a, b| OsmibyteOp::ModEuclid(out, a, b), move |out, a, c| {
                    let c: i32 = c.try_into().ok()?;
                    if c > 0 && (c as u64).is_power_of_two() {
                        Some(OsmibyteOp::AndConst(out, a, c.wrapping_sub(1)))
                    } else {
                        Some(OsmibyteOp::ModEuclidConst(out, a, c))
                    }
                }, |_, _, _| None);
            }
            Tetration => self.lower_binary(instr, |out, a, b| OsmibyteOp::Tetration(out, a, b), |_, _, _| None, |_, _, _| None),
            Funkcia => self.lower_binary(instr, |out, a, b| OsmibyteOp::Funkcia(out, a, b), |_, _, _| None, |_, _, _| None),
            Max => consumed = self.lower_max(instrs),
            Min => self.lower_min(instr),
            Sgn => self.lower_unary(instr, |out, a| OsmibyteOp::Sgn(out, a)),
            AbsFactorial => self.lower_unary(instr, |out, a| OsmibyteOp::AbsFactorial(out, a)),
            LenSum => self.lower_binary(instr, |out, a, b| OsmibyteOp::Lensum(out, a, b), |_, _, _| None, |_, _, _| None),
            And => self.lower_variadic(instr, |out, a, b| OsmibyteOp::And(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::AndConst(out, a, mask))),
            Or => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Or(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::OrConst(out, a, mask))),
            Xor => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Xor(out, a, b), |out, a, c| c.try_into().ok().map(|mask| OsmibyteOp::XorConst(out, a, mask))),
            ShiftL => self.lower_binary(instr, |out, a, b| OsmibyteOp::ShiftL(out, a, b), |out, a, c| Some(OsmibyteOp::ShiftConst(out, a, c.try_into().ok()?)), |_, _, _| None),
            ShiftR => self.lower_binary(instr, |out, a, b| OsmibyteOp::ShiftR(out, a, b), |out, a, c: i64| Some(OsmibyteOp::ShiftConst(out, a, c.checked_neg()?.try_into().ok()?)), |_, _, _| None),
            BinNot => self.lower_unary(instr, |out, a| OsmibyteOp::BinNot(out, a)),
            BoolNot => self.lower_unary(instr, |out, a| OsmibyteOp::BoolNot(out, a)),
            Select(condition) => self.lower_select(instr, condition.clone()),
            DigitSum => consumed = self.lower_digit_sum(instrs),
            Gcd => self.lower_variadic(instr, |out, a, b| OsmibyteOp::Gcd(out, a, b), |_, _, _| None),
            Median => self.lower_median(instr),
            Push => self.lower_push(&instr.inputs, false),
            Pop => return self.lower_pop(instrs),
            StackSwap => self.lower_stack_swap(instr, follows_checkpoint(instrs)),
            StackRead => self.lower_stack_read(instr),
            Jump(condition, target) => self.lower_jump(instr, condition.clone(), *target),
            Assert(condition, error) => {
                if self.g.conf.error_as_deopt {
                    self.lower_deopt(instr, condition.clone());
                } else {
                    self.lower_assert(instr, condition.clone(), error.clone())
                }
            }
            DeoptAssert(condition) => self.lower_deopt(instr, condition.clone()),
            KsplangOpsIncrement(condition) => self.lower_ops_increment(instr, condition.clone()),
            Checkpoint => self.lower_checkpoint(instr),
            Nop => { },
            MedianCursed | Universal => todo!("{instr:?}"),
        }
        self.temp_regs.clear();
        consumed
    }

    fn lower_variadic<F, FC>(&mut self, instr: &OptInstr, op: F, op_const: FC)
    where
        F: Fn(RegId, RegId, RegId) -> OsmibyteOp<RegId>,
        FC: Fn(RegId, RegId, i64) -> Option<OsmibyteOp<RegId>>,
    {
        assert!(!instr.inputs.is_empty());

        let spec = self.prepare_output(instr.out);
        let dest = spec.target_reg();
        let tmp_inter = if instr.inputs.iter().skip(2).any(|i| self.register_allocation.location(*i) == Some(ValueLocation::Register(dest))) {
            self.temp_regs.alloc().unwrap()
        } else {
            dest
        };

        let mut inputs = instr.inputs.iter().copied();
        let first_val = inputs.next().unwrap();

        if let Some(second_val) = inputs.next() {
            debug_assert!(!second_val.is_constant(), "{instr}");
            let second_reg = self.materialize_value_(second_val);
            // Check if first input is a constant (due to commutative property)
            if let Some(const_op) = self.g.get_constant(first_val).and_then(|v| op_const(tmp_inter, second_reg, v)) {
                self.save_deopt_maybe(instr);
                self.program.push(const_op);
            } else {
                let first_reg = self.materialize_value_(first_val);
                self.save_deopt_maybe(instr);
                self.program.push(op(tmp_inter, first_reg, second_reg));
            }
            for value in inputs {
                let reg = self.materialize_value_(value);
                self.save_deopt_maybe(instr);
                self.program.push(op(tmp_inter, tmp_inter, reg));
            }
        } else {
            let first_reg = self.materialize_value_(first_val);
            self.program.push(OsmibyteOp::AddConst(dest, first_reg, 0));
        }
        let fixup = self.program.last().unwrap().replace_regs(|&r, w| if (r, w) == (tmp_inter, true) { dest } else { r });
        *self.program.last_mut().unwrap() = fixup;

        self.finalize_output(spec);
    }

    fn lower_binary<F, FC1, FC2>(&mut self, instr: &OptInstr, op: F, op_const_rhs: FC1, op_const_lhs: FC2)
    where
        F: Fn(RegId, RegId, RegId) -> OsmibyteOp<RegId>,
        FC1: Fn(RegId, RegId, i64) -> Option<OsmibyteOp<RegId>>,
        FC2: Fn(RegId, i64, RegId) -> Option<OsmibyteOp<RegId>>,
    {
        debug_assert_eq!(instr.inputs.len(), 2, "{instr}");
        let spec = self.prepare_output(instr.out);

        if let Some(const_val) = self.g.get_constant(instr.inputs[0]) {
            if let Some(const_op) = op_const_lhs(spec.target_reg(), const_val, RegId(0)) {
                let rhs = self.materialize_value_(instr.inputs[1]);
                // Replace the dummy register with the actual one
                self.save_deopt_maybe(instr);
                self.program.push(const_op.replace_regs(|reg, is_write| if is_write { *reg } else { rhs }));
                self.finalize_output(spec);
                return;
            }
        }

        if let Some(const_val) = self.g.get_constant(instr.inputs[1]) {
            if let Some(const_op) = op_const_rhs(spec.target_reg(), RegId(0), const_val) {
                let lhs = self.materialize_value_(instr.inputs[0]);
                // Replace the dummy register with the actual one
                self.save_deopt_maybe(instr);
                self.program.push(const_op.replace_regs(|reg, is_write| if is_write { *reg } else { lhs }));
                self.finalize_output(spec);
                return;
            }
        }

        let lhs = self.materialize_value_(instr.inputs[0]);
        let rhs = self.materialize_value_(instr.inputs[1]);
        self.save_deopt_maybe(instr);
        self.program.push(op(spec.target_reg(), lhs, rhs));

        self.finalize_output(spec);
    }

    fn lower_max(&mut self, instrs: &[&OptInstr]) -> usize {
        let max = instrs[0];

        if let Some(lo_const) = self.g.get_constant(max.inputs[0]) && max.inputs.len() == 2 {
            if let Some(&min) = instrs.get(1) {
                // min(hi_const, max(lo_const, x)) -> clamp(x, lo_const, hi_const)
                if min.op == OptOp::Min && min.inputs.len() == 2 && min.inputs[1] == max.out &&
                    self.used_exactly_at(max.out, &[min.id])
                {
                    if let Some(hi_const) = self.g.get_constant(min.inputs[0]) {
                        assert!(lo_const < hi_const);
                        if let (Ok(lo_i16), Ok(hi_i16)) = (lo_const.try_into(), hi_const.try_into()) {
                            let spec = self.prepare_output(min.out);
                            let value_reg = self.materialize_value_(max.inputs[1]);
                            self.program.push(OsmibyteOp::ClampConst(spec.target_reg(), value_reg, lo_i16, hi_i16));
                            self.finalize_output(spec);
                            return 2; // Consumed Max, Min
                        }
                    }
                }
            }
        }

        self.lower_variadic(max, |out, a, b| OsmibyteOp::Max(out, a, b), |out, a, c| Some(OsmibyteOp::MaxConst(out, a, c.try_into().ok()?)));
        1
    }

    fn lower_min(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| OsmibyteOp::Min(out, a, b), |out, a, c| Some(OsmibyteOp::MinConst(out, a, c.try_into().ok()?)));
    }

    fn lower_div(&mut self, instrs: &[&OptInstr]) -> usize {
        let div = instrs[0];
        assert_eq!(2, div.inputs.len());

        if let Some(divisor) = self.g.get_constant(div.inputs[1]) {
            if let Some(&next) = instrs.get(1) {
                // (a / 2) + 1 -> median a 2
                if divisor == 2 &&
                    next.op == OptOp::Add && &next.inputs[..] == &[ValueId::C_ONE, div.out] &&
                    self.used_exactly_at(div.out, &[next.id])
                {
                    let spec = self.prepare_output(next.out);
                    let value_reg = self.materialize_value_(div.inputs[0]);
                    self.program.push(OsmibyteOp::MedianCursed2(spec.target_reg(), value_reg));
                    self.finalize_output(spec);
                    return 2; // Consumed Div, Add
                }
            }
        }

        // negative numbers get rounded down with bitshift
        let can_use_shift = *self.g.val_range(div.inputs[0]).start() >= 0;

        self.lower_binary(div, |out, a, b| OsmibyteOp::Div(out, a, b), |out, a, c| {
            if can_use_shift && c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = -(c.trailing_zeros() as i32) as i8;
                return Some(OsmibyteOp::ShiftConst(out, a, shift_amount));
            }
            Some(OsmibyteOp::DivConst(out, a, c.try_into().ok()?))
        }, |_, _, _| None);
        1
    }

    fn lower_mul(&mut self, instr: &OptInstr) {
        self.lower_variadic(instr, |out, a, b| OsmibyteOp::Mul(out, a, b), |out, a, c| {
            if c > 0 && (c as u64).is_power_of_two() {
                let shift_amount = c.trailing_zeros() as i8;
                return Some(OsmibyteOp::ShiftConst(out, a, shift_amount));
            }
            Some(OsmibyteOp::MulConst(out, a, c.try_into().ok()?))
        });
    }

    fn lower_digit_sum(&mut self, instrs: &[&OptInstr]) -> usize {
        let ds1 = instrs[0];
        assert_eq!(1, ds1.inputs.len());

        let input_reg = self.materialize_value_(ds1.inputs[0]);

        if let Some(&ds2) = instrs.get(1) {
            // digit_sum(digit_sum(x))
            if ds2.op == OptOp::DigitSum && &ds2.inputs[..] == &[ds1.out] {
                if let Some(&lensum) = instrs.get(2) {
                    // lensum(digit_sum(digit_sum(x)), digit_sum(x))
                    if lensum.op == OptOp::LenSum
                        && (&lensum.inputs[..] == &[ds2.out, ds1.out] || &lensum.inputs[..] == &[ds1.out, ds2.out])
                        && self.used_exactly_at(ds2.out, &[lensum.id])
                        && self.used_exactly_at(ds1.out, &[lensum.id, ds2.id])
                    {
                        let spec = self.prepare_output(lensum.out);
                        self.program.push(OsmibyteOp::DigitSumDigitSumLensum(spec.target_reg(), input_reg));
                        self.finalize_output(spec);
                        return 3; // Consumed DigitSum, DigitSum, LenSum
                    }
                }

                if self.used_exactly_at(ds1.out, &[ds2.id]) {
                    let spec = self.prepare_output(ds2.out);
                    self.program.push(OsmibyteOp::DigitSumTwice(spec.target_reg(), input_reg));
                    self.finalize_output(spec);
                    return 2; // Consumed DigitSum, DigitSum
                }
            }
        }

        let input_range = self.g.val_range(ds1.inputs[0]);
        let spec = self.prepare_output(ds1.out);
        if *input_range.start() >= 0 && *input_range.end() < 10_000 {
            self.program.push(OsmibyteOp::DigitSumSmall(spec.target_reg(), input_reg));
        } else {
            self.program.push(OsmibyteOp::DigitSum(spec.target_reg(), input_reg));
        }
        self.finalize_output(spec);
        1
    }

    fn lower_unary<F>(&mut self, instr: &OptInstr, op: F)
    where
        F: Fn(RegId, RegId) -> OsmibyteOp<RegId>,
    {
        if instr.inputs.is_empty() {
            return;
        }

        let spec = self.prepare_output(instr.out);
        let input = self.materialize_value_(instr.inputs[0]);
        self.save_deopt_maybe(instr);
        self.program.push(op(spec.target_reg(), input));
        self.finalize_output(spec);
    }

    fn lower_select(&mut self, instr: &OptInstr, condition: Condition<ValueId>) {
        debug_assert_eq!(instr.inputs.len(), 2, "select should have exactly two value inputs");
        let spec = self.prepare_output(instr.out);
        let lowered_condition = self.lower_condition(condition.clone());

        if let (Some(true_const), Some(false_const)) = (self.g.get_constant(instr.inputs[0]), self.g.get_constant(instr.inputs[1])) {
            // select(x == 0, 1, 0) -> BoolNot(x)
            if matches!(lowered_condition, Condition::EqConst(_, 0)) && true_const == 1 && false_const == 0 {
                let Condition::EqConst(val_reg, 0) = &lowered_condition else { unreachable!() };
                self.program.push(OsmibyteOp::BoolNot(spec.target_reg(), *val_reg));
                self.finalize_output(spec);
                return;
            }
            if matches!(lowered_condition, Condition::NeqConst(_, 0)) && true_const == 0 && false_const == 1 {
                let Condition::NeqConst(val_reg, 0) = &lowered_condition else { unreachable!() };
                self.program.push(OsmibyteOp::BoolNot(spec.target_reg(), *val_reg));
                self.finalize_output(spec);
                return;
            }
            let cond_val = condition.regs().into_iter().find(|i| i.is_computed()).unwrap();
            let cond_reg = lowered_condition.regs().into_iter().next().unwrap();
            let val_range = self.g.val_range(cond_val);

            // select(x == 0, 0, 1) -> Sgn(x) if x >= 0
            // or select(x != 0, 1, 0) -> Sgn(x) if x >= 0
            if (matches!(lowered_condition, Condition::EqConst(_, 0)) && true_const == 0 && false_const == 1)
                || (matches!(lowered_condition, Condition::NeqConst(_, 0)) && true_const == 1 && false_const == 0)
            {
                if *val_range.start() >= 0 {
                    self.program.push(OsmibyteOp::Sgn(spec.target_reg(), cond_reg));
                    self.finalize_output(spec);
                    return;
                }

                if *val_range.start() >= -1 && *val_range.end() <= 1 { // TODO: generalize this optimization? Make a CFG pass from this?
                    self.program.push(OsmibyteOp::AbsSubConst(spec.target_reg(), cond_reg, 0));
                }
            }

            if false_const == 0 {
                if let Ok(true_i16) = true_const.try_into() {
                    self.program.push(OsmibyteOp::SelectConst0(spec.target_reg(), lowered_condition, true_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if true_const == 0 {
                if let Ok(false_i16) = false_const.try_into() {
                    self.program.push(OsmibyteOp::SelectConst0(spec.target_reg(), lowered_condition.neg(), false_i16));
                    self.finalize_output(spec);
                    return;
                }
            }
            if let (Ok(true_i8), Ok(false_i8)) = (true_const.try_into(), false_const.try_into()) {
                self.program.push(OsmibyteOp::SelectConst(spec.target_reg(), lowered_condition, true_i8, false_i8));
                self.finalize_output(spec);
                return;
            }
        } else if let Some(true_const) = self.g.get_constant(instr.inputs[0]).and_then(|v| v.try_into().ok()) {
            // True branch is constant, false branch is register or out of range
            let false_reg = self.materialize_value_(instr.inputs[1]);
            self.program.push(OsmibyteOp::SelectConstReg(spec.target_reg(), lowered_condition, true_const, false_reg));
            self.finalize_output(spec);
            return;
        } else if let Some(false_const) = self.g.get_constant(instr.inputs[1]).and_then(|v| v.try_into().ok()) {
            let true_reg = self.materialize_value_(instr.inputs[0]);
            self.program.push(OsmibyteOp::SelectConstReg(spec.target_reg(), lowered_condition.neg(), false_const, true_reg));
            self.finalize_output(spec);
            return;
        }

        let true_reg = self.materialize_value_(instr.inputs[0]);
        let false_reg = self.materialize_value_(instr.inputs[1]);

        self.program.push(OsmibyteOp::Select(spec.target_reg(), lowered_condition, true_reg, false_reg));
        self.finalize_output(spec);
    }

    fn lower_median(&mut self, instr: &OptInstr) {
        let spec = self.prepare_output(instr.out);
        macro_rules! vals_without {
            ($x:expr) => { {
                let mut first = true;
                self.materialize_values(instr.inputs.iter().copied().filter(|v| if first && *v == $x { first = false; false } else { true }))
            } }
        }
        match instr.inputs.len() {
            0 | 1 => unreachable!("wtf {instr}"),
            2 if instr.inputs.contains(&ValueId::C_TWO) => {
                let xs = vals_without!(ValueId::C_TWO);
                let [a] = xs.as_slice() else { unreachable!() };
                self.program.push(OsmibyteOp::MedianCursed2(spec.target_reg(), *a));
            }
            2 => {
                let xs = self.materialize_values(instr.inputs.iter().copied());
                let [a, b] = xs.as_slice() else { unreachable!() };
                self.program.push(OsmibyteOp::Median2(spec.target_reg(), *a, *b));
            }
            3 if instr.inputs.contains(&ValueId::C_THREE) => {
                let xs = vals_without!(ValueId::C_THREE);
                let [a, b] = xs.as_slice() else { unreachable!() };
                self.program.push(OsmibyteOp::MedianCursed3(spec.target_reg(), *a, *b));
            }
            3 => {
                let xs = self.materialize_values(instr.inputs.iter().copied());
                let [a, b, c] = xs.as_slice() else { unreachable!() };
                self.program.push(OsmibyteOp::Median3(spec.target_reg(), *a, *b, *c));
            }
            5 if instr.inputs.contains(&ValueId::C_FIVE) => {
                let xs = vals_without!(ValueId::C_FIVE);
                let [a, b, c, d] = xs.as_slice() else { unreachable!("{xs:?} {instr}") };
                self.program.push(OsmibyteOp::MedianCursed5(spec.target_reg(), *a, *b, *c, *d));
            }
            _ => todo!("Median {instr}\n\n{}", self.g)
        }
    }

    fn lower_push(&mut self, inputs: &[ValueId], save_deopts: bool) {
        let mut remaining = inputs;

        while !remaining.is_empty() {
            let mut regs: SmallVec<[RegId; 7]> = SmallVec::new();

            // Try to materialize up to 7 values, stop if we run out of temp registers
            for &value in remaining.iter().take(7) {
                match self.materialize_value(value) {
                    Ok(reg) => regs.push(reg),
                    Err(()) => break, // Out of temp registers, emit what we have
                }
            }

            if regs.is_empty() {
                // No registers available at all - this shouldn't happen with proper register allocation
                panic!("ran out of temp registers completely in lower_push");
            }

            if save_deopts {
                _ = self.save_deopt();
            }
            self.emit_push(&regs);

            remaining = &remaining[regs.len()..];
            self.temp_regs.clear();

            if let Some(deopt) = &mut self.current_deopt {
                if deopt.stack_reconstruction.starts_with(&regs) {
                    deopt.stack_reconstruction.drain(0..regs.len());
                } else {
                    todo!()
                }
            }
        }
    }

    fn emit_push(&mut self, regs: &[RegId]) {
        self.program.push(OsmibyteOp::create_push(regs))
    }

    fn lower_pop(&mut self, instrs: &[&OptInstr]) -> usize {
        self.save_deopt_maybe(&instrs[0]);
        let mut pops = vec![];
        let mut out_specs = vec![];
        let mut out_regs = vec![];
        for i in instrs {
            if pops.len() >= 4 { break; }
            if let OptOp::Pop = i.op {
                pops.push(i.out);
                let spec = self.prepare_output(i.out);
                out_specs.push(spec);
                out_regs.push(spec.target_reg());
            } else {
                break;
            }
        }
        self.program.push(match &out_regs[..] {
            &[a] => OsmibyteOp::Pop(a),
            &[a, b] => OsmibyteOp::Pop2(a, b),
            &[a, b, c] => OsmibyteOp::Pop3(a, b, c),
            &[a, b, c, d] => OsmibyteOp::Pop4(a, b, c, d),
            _ => unreachable!()
        });
        for &spec in &out_specs {
            self.finalize_output(spec);
        }

        if let Some(deopt) = &mut self.current_deopt {
            out_specs.reverse();
            out_regs.reverse();
            let new_code = out_specs.iter().filter_map(|s| s.load_instr())
                .chain([OsmibyteOp::create_push(&out_regs)])
                .chain(deopt.opcodes.iter().cloned())
                .collect();
            deopt.opcodes = new_code;
        }
        pops.len()
    }

    fn lower_stack_swap(&mut self, instr: &OptInstr, ignore_deopt: bool) {
        debug_assert_eq!(instr.inputs.len(), 2);

        let index_reg = self.materialize_value_(instr.inputs[0]);
        let value_reg = self.materialize_value_(instr.inputs[1]);

        if instr.out == ValueId(0) ||
            ignore_deopt && self.g.values.get(&instr.out).is_some_and(|v| v.used_at.is_empty())
        {
            self.save_deopt().unwrap();
            self.program.push(OsmibyteOp::StackWrite(index_reg, value_reg, 0));
            self.current_deopt = None;
        }
        else {
            let spec = self.prepare_output(instr.out);
            self.save_deopt().unwrap();
            self.program.push(OsmibyteOp::StackSwap(spec.target_reg(), index_reg, value_reg, 0));
            self.finalize_output(spec);

            if !ignore_deopt && self.current_deopt.is_some() {
                let new_code = spec.load_instr().into_iter()
                    .chain(self.mk_materialization(instr.inputs[0], index_reg))
                    .chain([OsmibyteOp::StackWrite(index_reg, spec.target_reg(), 0)])
                    .chain(self.current_deopt.as_ref().unwrap().opcodes.iter().cloned())
                    .collect();
                self.current_deopt.as_mut().unwrap().opcodes = new_code;
            } else {
                self.current_deopt = None
            }
        }
    }

    fn lower_stack_read(&mut self, instr: &OptInstr) {
        debug_assert_eq!(instr.inputs.len(), 1);

        let index_reg = self.materialize_value_(instr.inputs[0]);
        let spec = self.prepare_output(instr.out);
        self.save_deopt().unwrap();
        self.program.push(OsmibyteOp::StackRead(spec.target_reg(), index_reg, 0));
        self.finalize_output(spec);
    }

    fn lower_jump(&mut self, instr: &OptInstr, condition: Condition<ValueId>, target: BlockId) {
        if condition == Condition::False { return }

        let condition = self.lower_condition(condition);

        let target_block = self.g.block_(target);
        assert_eq!(target_block.parameters.len(), instr.inputs.len(), "jump {instr} has mismatched argument count");

        let mut register_moves: Vec<(RegId, RegId)> = Vec::new();
        let mut unspills: Vec<(u32, RegId)> = Vec::new();
        let mut spills: Vec<(ValueId, u32)> = Vec::new();
        let mut consts: Vec<(i64, RegId)> = Vec::new();

        for (param, arg) in target_block.parameters.iter().zip(instr.inputs.iter()) {
            match self.register_allocation.location(*param) {
                Some(ValueLocation::Register(dest_reg)) => {
                    if arg.is_constant() {
                        consts.push((self.g.get_constant_(*arg), dest_reg));
                        continue;
                    }
                    match self.register_allocation.location(*arg) {
                        Some(ValueLocation::Register(src)) if src == dest_reg => {}
                        Some(ValueLocation::Register(src)) => register_moves.push((src, dest_reg)),
                        Some(ValueLocation::Spill(src_spill)) => unspills.push((src_spill, dest_reg)),
                        None => panic!()
                    }
                }
                Some(ValueLocation::Spill(slot)) => {
                    if self.register_allocation.location(*arg) != Some(ValueLocation::Spill(slot)) {
                        spills.push((*arg, slot))
                    }
                },
                None => {}
            }
        }

        let jump_fixup = if condition != Condition::True && register_moves.len() + unspills.len() + spills.len() + consts.len() > 0 {
            // first check condition, then move values
            self.program.push(OsmibyteOp::Jump(condition.clone().neg(), 0));
            self.temp_regs.clear();
            Some(self.program.len() - 1)
        } else {
            None
        };

        for (value, slot) in spills {
            let reg = self.materialize_value_(value);
            self.program.push(OsmibyteOp::Spill(slot, reg));
            self.temp_regs.release(reg);
        }

        self.emit_register_moves(register_moves);

        for (slot, reg) in unspills {
            self.program.push(OsmibyteOp::Unspill(reg, slot));
        }

        for (value, reg) in consts {
            let const_op = self.mk_load_constant(reg, value);
            self.program.push(const_op);
        }

        if let Some(jump_fixup) = jump_fixup {
            let current_loc = self.program.len();
            let OsmibyteOp::Jump(_, target) = &mut self.program[jump_fixup] else { panic!() };
            *target = (current_loc + 1).assert_into();
            // condition is already in the first jump
            self.program.push(OsmibyteOp::Jump(Condition::True, 0))
        } else {
            self.program.push(OsmibyteOp::Jump(condition, 0));
        }
        self.jump_fixups.push((self.program.len() - 1, target));
    }

    fn emit_register_moves(&mut self, mut moves: Vec<(RegId, RegId)>) {
        moves.retain(|(from, to)| from != to);
        let mut inputs: BTreeMap<RegId, usize> = BTreeMap::new();
        for (from, _to) in &moves {
            *inputs.entry(*from).or_default() += 1;
        }

        let mut sequential_moves = vec![];
        while let Some(mv_ix) = moves.iter().position(|(_from, to)| *inputs.get(to).unwrap_or(&0) == 0) {
            let mv = moves.swap_remove(mv_ix);
            *inputs.get_mut(&mv.0).unwrap() -= 1;
            sequential_moves.push(mv);
        }
        let mut atomic_moves = moves; // rest has some cycles, we need to be careful
        assert_ne!(1, atomic_moves.len());
        // sequence of swaps
        let mut reg_remap = BTreeMap::new();
        while let Some((from, to)) = atomic_moves.pop() {
            // TODO: test this properly
            // println!("{from} -> {to}   in {atomic_moves:?}  | {reg_remap:?}");
            let from = *reg_remap.get(&from).unwrap_or(&from);
            // println!("{from_loc} -> {to}");
            if from == to {
                continue
            }
            self.program.push(OsmibyteOp::Mov2(to, from, from, to));
            // `from` is now temporarily swapped with `to`

            reg_remap.insert(from, to);
            reg_remap.insert(to, from);
        }
        for chunk in sequential_moves.chunks(3) {
            match chunk {
                [a, b, c] => self.program.push(OsmibyteOp::Mov3(a.1, a.0, b.1, b.0, c.1, c.0)),
                [a, b] => self.program.push(OsmibyteOp::Mov2(a.1, a.0, b.1, b.0)),
                [a] => self.program.push(OsmibyteOp::OrConst(a.1, a.0, 0)),
                wtf => unreachable!("{wtf:?}")
            }
        }
    }

    fn lower_assert(&mut self, instr: &OptInstr, condition: Condition<ValueId>, error: OperationError) {
        let lowered_condition = self.lower_condition(condition);

        if matches!(error, OperationError::Unreachable) {
            self.program.push(OsmibyteOp::DebugAssert(lowered_condition));
            return;
        }

        let code = Self::encode_error(&error);

        let arg_reg = if instr.inputs.len() > 0 {
            let id = instr.inputs[0];
            self.materialize_value_(id)
        } else {
            RegId(0) // undefined value
        };

        self.program.push(OsmibyteOp::Assert(lowered_condition, code, arg_reg));
    }

    fn lower_deopt(&mut self, instr: &OptInstr, condition: Condition<ValueId>) {
        let lowered_condition = self.lower_condition(condition);
        assert_ne!(lowered_condition, Condition::True, "{instr}");

        let deopt = self.current_deopt.as_ref().unwrap();

        if lowered_condition == Condition::False &&
            deopt.ip <= u32::MAX as usize &&
            deopt.stack_reconstruction.len() <= 7 * 3 &&
            deopt.ksplang_ops_increment.unsigned_abs() <= i16::MAX as u64
        {
            // compile to Done instruction
            self.program.extend(deopt.opcodes.iter().cloned());
            let ctr_inc = deopt.ksplang_ops_increment.try_into();
            if ctr_inc.is_err() {
                self.program.push(OsmibyteOp::KsplangOpsIncrement(deopt.ksplang_ops_increment.assert_into()));
            }
            let ip = deopt.ip;
            for regs in deopt.stack_reconstruction.clone().chunks(7) {
                self.emit_push(regs);
            }
            self.program.push(OsmibyteOp::Done(ip as u32, ctr_inc.unwrap()));
            return;
        }

        let id = self.save_deopt().unwrap();
        self.program.push(OsmibyteOp::DeoptAssert(lowered_condition, id.try_into().expect("TODO")));
    }

    fn lower_ops_increment(&mut self, instr: &OptInstr, condition: Condition<ValueId>) {
        let cond = self.lower_condition(condition);
        let mut deopt: Vec<OsmibyteOp<RegId>> = vec![];
        let mut deopt_const: i64 = 0;
        for &value in &instr.inputs {
            if let Some(c) = self.g.get_constant(value) {
                if cond == Condition::True {
                    deopt_const -= c;
                    if let Ok(c_i32) = c.try_into() {
                        self.program.push(OsmibyteOp::KsplangOpsIncrement(c_i32));
                        continue;
                    } else {
                        let reg = self.materialize_value_(value);
                        self.program.push(OsmibyteOp::KsplangOpsIncrementVar(reg, 1));
                        continue;
                    }
                } else if let Ok(c_i16) = c.try_into() {
                    self.program.push(OsmibyteOp::KsplangOpsIncrementCond(cond.clone(), c_i16));
                    deopt.push(OsmibyteOp::KsplangOpsIncrementCond(cond.clone(), -c_i16));
                    continue;
                }
            }
            let reg = self.materialize_value_(value);
            deopt.extend(self.mk_materialization(value, reg));
            if cond == Condition::True {
                self.program.push(OsmibyteOp::KsplangOpsIncrementVar(reg, 1));
                deopt.push(OsmibyteOp::KsplangOpsIncrementVar(reg, -1));
            } else {
                let tmp = self.temp_regs.alloc().unwrap();
                self.program.push(OsmibyteOp::SelectConstReg(tmp, cond.clone().neg(), 0, reg));
                self.program.push(OsmibyteOp::KsplangOpsIncrementVar(tmp, 1));
                deopt.push(OsmibyteOp::SelectConstReg(tmp, cond.clone().neg(), 0, reg));
                deopt.push(OsmibyteOp::KsplangOpsIncrementVar(tmp, -1));
                self.temp_regs.release(tmp);
            }
        }

        if let Some(deopt_mut) = self.current_deopt.as_mut() {
            deopt.extend_from_slice(&deopt_mut.opcodes[..]);
            deopt_mut.opcodes = deopt.into_boxed_slice();
            deopt_mut.ksplang_ops_increment += deopt_const;
        }
    }

    fn lower_condition(
        &mut self,
        condition: Condition<ValueId>,
    ) -> Condition<RegId> {
        use Condition::*;
        fn i16conv(x: i64) -> Option<i16> {
            return x.try_into().ok()
        }
        match condition {
            Eq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    EqConst(self.materialize_value_(b), c)
                } else {
                    Eq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Neq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    NeqConst(self.materialize_value_(b), c)
                } else {
                    Neq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Lt(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a < b  where a is const  =>  b > const
                    GtConst(self.materialize_value_(b), c)
                } else {
                    Lt(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Leq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a <= b  where a is const  =>  b >= const
                    GeqConst(self.materialize_value_(b), c)
                } else {
                    Leq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Gt(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a > b  where a is const  =>  b < const
                    LtConst(self.materialize_value_(b), c)
                } else {
                    Gt(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Geq(a, b) => {
                if let Some(c) = self.g.get_constant(a).and_then(i16conv) {
                    // a >= b  where a is const  =>  b <= const
                    LeqConst(self.materialize_value_(b), c)
                } else {
                    Geq(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            Divides(a, b) => {
                if let Some(c) = self.g.get_constant(b).and_then(|c| u16::try_from(c).ok()) {
                    DividesConst(self.materialize_value_(a), c)
                } else {
                    Divides(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            NotDivides(a, b) => {
                if let Some(c) = self.g.get_constant(b).and_then(|c| u16::try_from(c).ok()) {
                    NotDividesConst(self.materialize_value_(a), c)
                } else {
                    NotDivides(self.materialize_value_(a), self.materialize_value_(b))
                }
            }
            // Already const variants
            EqConst(a, c) => EqConst(self.materialize_value_(a), c),
            NeqConst(a, c) => NeqConst(self.materialize_value_(a), c),
            LtConst(a, c) => LtConst(self.materialize_value_(a), c),
            LeqConst(a, c) => LeqConst(self.materialize_value_(a), c),
            GtConst(a, c) => GtConst(self.materialize_value_(a), c),
            GeqConst(a, c) => GeqConst(self.materialize_value_(a), c),
            DividesConst(a, c) => DividesConst(self.materialize_value_(a), c),
            NotDividesConst(a, c) => NotDividesConst(self.materialize_value_(a), c),
            True => True,
            False => False,
        }
    }

    fn mk_load_constant(&mut self, reg: RegId, value: i64) -> OsmibyteOp<RegId> {
        if value >= i32::MIN as i64 && value <= i32::MAX as i64 {
            OsmibyteOp::LoadConst(reg, value as i32)
        } else { // TODO: pow2 offset
            let idx = self.get_large_constant_index(value);
            OsmibyteOp::LoadConst64(reg, idx)
        }
    }

    fn materialize_value(&mut self, value: ValueId) -> Result<RegId, ()> {
        if let Some(cached_reg) = self.temp_regs.get_cached(value) {
            return Ok(cached_reg);
        }

        let reg = if value.is_constant() {
            let constant = self.g.get_constant_(value);
            let reg = self.temp_regs.alloc().ok_or(())?;
            let const_op = self.mk_load_constant(reg, constant);
            self.program.push(const_op);
            self.temp_regs.insert_cache(value, reg);
            reg
        } else if let Some(location) = self.register_allocation.location(value) {
            match location {
                ValueLocation::Register(reg) => reg,
                ValueLocation::Spill(slot) => {
                    let reg = self.temp_regs.alloc().ok_or(())?;
                    self.program.push(OsmibyteOp::Unspill(reg, slot));
                    self.temp_regs.insert_cache(value, reg);
                    reg
                }
            }
        } else {
            panic!("value {:?} has no register allocation", value);
        };

        Ok(reg)
    }

    fn materialize_values(&mut self, values: impl Iterator<Item = ValueId>) -> SmallVec<[RegId; 8]> {
        let mut result = smallvec![];
        for v in values {
            result.push(self.materialize_value_(v))
        }
        result
    }

    fn mk_materialization(&mut self, value: ValueId, reg: RegId) -> SmallVec<[OsmibyteOp<RegId>; 2]> {
        if value.is_constant() {
            let constant = self.g.get_constant_(value);
            let const_op = self.mk_load_constant(reg, constant);
            smallvec![const_op]
        } else if let Some(location) = self.register_allocation.location(value) {
            match location {
                ValueLocation::Register(reg2) => {
                    assert_eq!(reg2, reg);
                    smallvec![]
                }
                ValueLocation::Spill(slot) =>
                    smallvec![OsmibyteOp::Unspill(reg, slot)]
            }
        } else {
            panic!("value {:?} has no register allocation", value)
        }
    }

    fn get_usages(&'_ self, value: ValueId) -> Option<&'_ BTreeSet<InstrId>> {
        if let Some(inf) = self.g.values.get(&value) {
            Some(&inf.used_at)
        } else {
            None
        }
    }

    fn used_exactly_at(&self, value: ValueId, at: &[InstrId]) -> bool {
        let Some(used_at) = self.get_usages(value) else {
            return false;
        };
        return used_at.len() == at.len() && at.iter().all(|i| used_at.contains(i));
    }

    fn materialize_value_(&mut self, value: ValueId) -> RegId {
        self.materialize_value(value).expect("ran out of temp registers")
    }

    fn get_large_constant_index(&mut self, value: i64) -> u16 {
        if let Some(&idx) = self.large_constant_lookup.get(&value) {
            return idx;
        }

        let idx = self.large_constants.len();
        assert!(idx < u16::MAX as usize, "too many large constants");
        let idx_u16 = idx as u16;
        self.large_constants.push(value);
        self.large_constant_lookup.insert(value, idx_u16);
        idx_u16
    }

    fn prepare_output(&mut self, value: ValueId) -> OutputSpec {
        if !value.is_computed() {
            // Return a dummy temp register that will be discarded
            let reg = self.temp_regs.alloc().expect("ran out of temp registers");
            return OutputSpec::Register(reg);
        }

        match self.register_allocation.location(value) {
            Some(ValueLocation::Register(reg)) => OutputSpec::Register(reg),
            Some(ValueLocation::Spill(slot)) => {
                let reg = self.temp_regs.alloc().expect("ran out of scratch registers for spill dest");
                OutputSpec::Spill { reg, slot }
            }
            None => panic!("no register allocation for output value {value}\n{allocation}", allocation = &self.register_allocation),
        }
    }

    fn finalize_output(&mut self, spec: OutputSpec) {
        if let OutputSpec::Spill { reg, slot } = spec {
            self.program.push(OsmibyteOp::Spill(slot, reg));
            self.temp_regs.release(reg);
        }
    }

    fn encode_error(error: &OperationError) -> u16 {
        use OperationError::*;
        match error {
            IntegerOverflow => 0,
            DivisionByZero => 1,
            InvalidArgumentForUniversal { .. } => 2,
            NegativeLength { .. } => 3,
            NegativeIterations { .. } => 4,
            NegativeBitCount { .. } => 5,
            NonpositiveLength { .. } => 6,
            NegativeInstructionIndex { .. } => 7,
            NegativePraiseCount { .. } => 8,
            QeqZeroEqualsZero => 9,
            ArgumentAMustBeNonNegative { .. } => 10,
            ArgumentBMustBeNonNegative { .. } => 11,
            ArgumentCMustBeNonNegative { .. } => 12,
            _ => panic!("Unsupported {error:?}"),
        }
    }

    fn lower_checkpoint(&mut self, instr: &OptInstr) {
        let deopt = self.with_clean_program(|this| {
            let stack = this.materialize_deopt_stack(&instr.inputs[1..]);
            DeoptInfo::new(instr.program_position, &stack, instr.ksp_instr_count as i64, &this.program)
        });
        self.current_deopt = Some(deopt)
    }

    fn needs_deopt(&self, instr: &OptInstr) -> bool {
        match instr.effect {
            OpEffect::None | OpEffect::ControlFlow | OpEffect::CtrIncrement => false,
            OpEffect::MayFail => self.g.conf.error_as_deopt,
            _ => true
        }
    }

    fn save_deopt_maybe(&mut self, instr: &OptInstr) -> Option<u32> {
        if self.needs_deopt(instr) {
            self.save_deopt().ok()
        } else {
            None
        }
    }

    fn save_deopt(&mut self) -> Result<u32, String> {
        assert!(self.program.len() < u32::MAX as usize);
        assert!(self.deopts.len() < u32::MAX as usize);

        let deopt = self.current_deopt.clone().ok_or_else(|| format!("No deopt at {}", self.program.len()))?;
        if let Some(&id) = self.deopts_lookup.get(&deopt) {
            self.ip2deopt.insert(self.program.len() as u32, id);
            return Ok(id)
        }

        let id = self.deopts.len() as u32;
        self.deopts_lookup.insert(deopt.clone(), id);
        self.deopts.push(deopt);
        self.ip2deopt.insert(self.program.len() as u32, id);
        Ok(id)
    }

    fn with_clean_program<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let program_backup = mem::take(&mut self.program);
        let regs_backup = mem::take(&mut self.temp_regs);
        let deopt_backup = mem::take(&mut self.current_deopt);
        let jumps_check = self.jump_fixups.len();
        let blocks_check = self.block_starts.len();

        let result = f(self);

        self.program = program_backup;
        self.temp_regs = regs_backup;
        self.current_deopt = deopt_backup;
        assert_eq!(jumps_check, self.jump_fixups.len());
        assert_eq!(blocks_check, self.block_starts.len());

        result
    }

    fn prepare_block_deopt(&mut self, bid: BlockId) -> Option<DeoptInfo> {
        let b = self.g.block_(bid);
        if b.is_entry() {
            return Some(DeoptInfo::new(b.ksplang_start_ip, &[], 0, &[]))
        }
        if b.incoming_jumps.len() != 1 {
            return None
        }

        self.with_clean_program(move |this| {
            this.prepare_block_deopt_core(bid)
        })
    }

    fn prepare_block_deopt_core(&mut self, bid: BlockId) -> Option<DeoptInfo> {
        let b = self.g.block_(bid);
        if b.is_entry() {
            return Some(DeoptInfo::new(b.ksplang_start_ip, &[], 0, &self.program))
        }
        if b.incoming_jumps.len() != 1 {
            return None
        }
        let incoming = b.incoming_jumps[0].0;
        let incoming_ctr_inc = self.g.block_(incoming).ksplang_instr_count as i64;
        // let mut ops = vec![];
        let mut stack_push = vec![];
        let mut stack_pop = 0;
        let mut result = None;
        for (_iid, i) in self.g.block_(incoming).instructions.iter().rev() {
            match &i.op {
                OptOp::Pop => {
                    if !i.out.is_computed() {
                        return None
                    }
                    stack_push.push(i.out);
                }
                OptOp::Push => {
                    for _ in &i.inputs {
                        if stack_push.len() > 0 {
                            stack_push.pop().unwrap();
                        } else {
                            stack_pop += 1;
                        }
                    }
                }
                OptOp::StackSwap => {
                    if !i.out.is_computed() {
                        return None
                    }
                    let val = self.materialize_value_(i.out);
                    let ix = self.materialize_value_(i.inputs[0]);
                    self.program.push(OsmibyteOp::StackWrite(ix, val, 0));
                    self.temp_regs.release(val);
                    self.temp_regs.release(ix);
                }
                // TODO: ksplang counter increment revert
                OptOp::Checkpoint => {
                    result = Some((i.program_position, i.ksp_instr_count, i.inputs[1..].to_vec()));
                    break;
                }
                _ => { }
            }
        }
        // println!("Prepared deopt of {bid} with incoming {incoming}");
        // println!(" Stack: -{stack_pop}  + {stack_push:?}");

        if let Some((ip, ksplang_count, mut stack)) = result {
            let ksplang_count = ksplang_count as i64 - incoming_ctr_inc;
            stack.splice(0..stack_pop, stack_push);
            let stack = self.materialize_deopt_stack(&stack);
            Some(DeoptInfo::new(ip, &stack, ksplang_count, &self.program))
        } else {
            self.lower_push(&stack_push, false);

            if let Some(mut deopt) = self.prepare_block_deopt_core(incoming) {
                assert_eq!(0, stack_pop);
                deopt.stack_reconstruction.drain(0..stack_pop);
                deopt.ksplang_ops_increment -= incoming_ctr_inc;
                Some(deopt)
            } else {
                return None;
            }
        }
    }

    fn materialize_deopt_stack(&mut self, stack: &[ValueId]) -> Vec<RegId> {
        if stack.len() > self.temp_regs.available.len() {
            let mut free_registers: BTreeSet<RegId> = (0..u8::MAX).map(RegId).collect();
            for s in stack {
                if let Some(ValueLocation::Register(reg)) = self.register_allocation.location(*s){
                    free_registers.remove(&reg);
                }
            }
            self.temp_regs.available.clear();
            self.temp_regs.available.extend(free_registers);
        }

        let available_regs = self.temp_regs.available.clone();
        let mut todo = stack.to_vec();
        todo.reverse();

        let mut result = vec![];
        'outer: loop {
            for chunk in result.chunks(7) {
                self.emit_push(chunk);
            }
            result.clear();
            self.temp_regs.cache.clear();
            self.temp_regs.available = available_regs.clone();
            while let Some(s) = todo.pop() {
                let Ok(reg) = self.materialize_value(s) else {
                    todo.push(s);
                    continue 'outer;
                };
                result.push(reg)
            }
            return result
        }
    }

    pub fn finish(mut self) -> OsmibytecodeBlock {
        for (pos, target) in self.jump_fixups {
            let target_ip = *self
                .block_starts
                .get(&target)
                .unwrap_or_else(|| panic!("jump target block {:?} was not compiled", target));
            if let Some(OsmibyteOp::Jump(_, dest)) = self.program.get_mut(pos) {
                *dest = target_ip;
            } else {
                panic!("expected jump at position {}", pos);
            }
        }

        OsmibytecodeBlock {
            program: self.program.into_boxed_slice(),
            stack_space_required: 0,
            stack_values_required: 0,
            start_ip: self.g.blocks.first().map(|b| b.ksplang_start_ip).unwrap_or(0),
            large_constants: self.large_constants.into_boxed_slice(),
            ip2deopt: self.ip2deopt.into_iter().collect(),
            deopts: self.deopts.into_boxed_slice(),
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
pub struct RegisterAllocation {
    locations: BTreeMap<ValueId, ValueLocation>,
}

impl RegisterAllocation {
    fn location(&self, value: ValueId) -> Option<ValueLocation> {
        self.locations.get(&value).copied()
    }
}

impl fmt::Display for RegisterAllocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut regs: BTreeMap<RegId, BTreeSet<ValueId>> = BTreeMap::new();
        let mut spills: Vec<(u32, ValueId)> = Vec::new();

        for (&value, &location) in &self.locations {
            match location {
                ValueLocation::Register(reg) => { regs.entry(reg).or_default().insert(value); },
                ValueLocation::Spill(slot) => spills.push((slot, value)),
            }
        }

        spills.sort_by_key(|(slot, _)| *slot);

        writeln!(f, "RegisterAllocation {{")?;
        for (&value, &location) in &self.locations {
            writeln!(f, "    {value:05}   {location:?}")?
        }
        if !regs.is_empty() {
            writeln!(f, "  registers:")?;
            for (reg, values) in regs {
                writeln!(f, "    r{:02}: {values:?}", reg.0)?;
            }
        }

        if !spills.is_empty() {
            writeln!(f, "  spills:")?;
            for (slot, value) in spills {
                writeln!(f, "    {slot:02}: {value}")?;
            }
        }

        write!(f, "}}")
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueLocation {
    Register(RegId),
    Spill(u32),
}

const RESERVED_REG_COUNT: u32 = 8;
const TOTAL_REG_COUNT: u32 = u8::MAX as u32 + 1;
pub const ALLOCATABLE_REG_COUNT: u32 = TOTAL_REG_COUNT - RESERVED_REG_COUNT;
const FIRST_TEMP_REG: u8 = ALLOCATABLE_REG_COUNT as u8;

#[derive(Clone, Debug)]
struct TempRegPool {
    available: SmallVec<[RegId; 16]>,
    cache: BTreeMap<ValueId, RegId>,
}

impl Default for TempRegPool {
    fn default() -> Self {
        Self::new()
    }
}

impl TempRegPool {
    fn new() -> Self {
        let available = (FIRST_TEMP_REG..=u8::MAX).rev().map(RegId).collect();
        Self { available, cache: BTreeMap::new() }
    }

    fn alloc(&mut self) -> Option<RegId> {
        self.available.pop()
    }

    fn release(&mut self, reg: RegId) {
        if reg.0 >= FIRST_TEMP_REG && !self.available.contains(&reg) {
            self.available.push(reg);
        }
    }

    fn clear(&mut self) {
        self.available.clear();
        self.available.extend((FIRST_TEMP_REG..=u8::MAX).rev().map(RegId));
        self.cache.clear();
    }

    fn get_cached(&self, value: ValueId) -> Option<RegId> {
        self.cache.get(&value).copied()
    }

    fn insert_cache(&mut self, value: ValueId, reg: RegId) {
        self.cache.insert(value, reg);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ValueSegment {
    block: BlockId,
    from: u32,
    to: u32,
    instr_count: u32,
}

impl ValueSegment {
    fn new(block: &BasicBlock, from: u32, to: u32) -> Self {
        assert!(from <= to);
        let instr_count = if from == to {
            1
        } else if from == 0 && to == u32::MAX {
            block.instructions.len().saturating_into()
        } else {
            block.instructions.range(from..=to).count().saturating_into()
        };
        assert!(instr_count != 0);
        ValueSegment {
            block: block.id,
            from, to, instr_count
        }
    }

    fn overlap(&self, other: &ValueSegment) -> bool {
        if self.block != other.block {
            return false
        }
        self.from < other.to && other.from < self.to
    }
}

#[derive(Clone, Debug)]
struct ValueCandidate {
    value: ValueId,
    segments: HashMap<BlockId, ValueSegment>,
    weight: u64,
    use_count: usize,
    has_phi_friends: bool,
}

pub fn allocate_registers(g: &GraphBuilder, reg_count: u32, error_will_deopt: bool) -> RegisterAllocation {
    if reg_count == 0 {
        return RegisterAllocation::default();
    }

    assert!(reg_count <= u8::MAX as u32 + 1, "reg_count exceeds register file size");

    let phi_friends = equivalence_preferences(g);

    let lifetimes = analyze_value_lifetimes(g, error_will_deopt);
    if g.conf.should_log(16) {
        println!("{lifetimes}");
    }

    let mut value_segments: HashMap<ValueId, HashMap<BlockId, ValueSegment>> = Default::default();
    let mut candidates: Vec<ValueCandidate> = lifetimes
        .ranges
        .iter()
        .filter(|(val, _)| val.is_computed())
        .filter_map(|(val, blocks)| {
            let segments: HashMap<BlockId, ValueSegment> =
                blocks.iter().map(|(&block, &(from, to))| (block, ValueSegment::new(g.block_(block), from.1, to.1)))
                             .collect();
            if segments.is_empty() {
                return None;
            }
            value_segments.insert(*val, segments.clone());
            let weight = segments.values().map(|seg| seg.instr_count as u64).sum::<u64>();
            let use_count = g.val_info(*val).map_or(0, |info| info.used_at.len());
            let has_phi_friends = phi_friends
                .range((*val, ValueId(i32::MIN))..=(*val, ValueId(i32::MAX)))
                .next().is_some();
            Some(ValueCandidate { value: *val, segments, weight, use_count, has_phi_friends })
        })
        .collect();

    candidates.sort_by_key(|a|
        (a.weight / cmp::max(a.use_count as u64, 1), usize::MAX - a.use_count, a.value));

    let mut register_segments: Vec<HashMap<BlockId, Vec<ValueSegment>>> = (0..reg_count).map(|_| Default::default()).collect();
    let mut register_values: Vec<HashSet<ValueId>> = (0..reg_count).map(|_| Default::default()).collect();
    let mut allocation = RegisterAllocation::default();
    let mut next_spill_slot: u32 = 0;

    for candidate in candidates {
        let ValueCandidate { value, segments, weight: _, use_count: _, has_phi_friends } = candidate;
        if allocation.locations.contains_key(&value) {
            continue;
        }

        let mut options = register_segments.iter().enumerate()
            .filter(|(_reg_ix, reg_segments)| !has_conflict(reg_segments, &segments))
            .map(|(reg_ix, _)| reg_ix);

        let (chosen_reg, merged_friends) = if !has_phi_friends {
            (options.next(), smallvec![])
        } else {
            let mut candidate_regs: BTreeSet<usize> = options.collect();
            let merged_friends = reduce_registers_with_phi_friends(
                value,
                &mut candidate_regs,
                &phi_friends,
                &allocation,
                &value_segments,
                &register_segments,
            );
            (candidate_regs.into_iter().next(), merged_friends)
        };
        assert!(!merged_friends.contains(&value));

        let Some(chosen_reg) = chosen_reg else {
            allocation.locations.insert(value, ValueLocation::Spill(next_spill_slot)); // TODO same spill for friends?
            next_spill_slot += 1;
            continue;
        };

        for val in [value].into_iter().chain(merged_friends.clone()) {
            assert!(!allocation.locations.contains_key(&val));

            let segments = &value_segments[&val];
            assert!(!has_conflict(&register_segments[chosen_reg], segments),
                    "Unexpected conflicts between reg {chosen_reg} and {val}:\nAllocating {value} with {merged_friends:?}\nSegments: {value_segments:?}\nRegister segments: {:?}\nCFG: {g}", register_segments[chosen_reg]);

            for (block, segment) in segments.iter() {
                register_segments[chosen_reg].entry(*block).or_default().push(*segment);
            }
            allocation.locations.insert(val, ValueLocation::Register(RegId(chosen_reg as u8)));
            register_values[chosen_reg].insert(val);
        }
    }

    allocation
}

fn has_conflict(existing: &HashMap<BlockId, Vec<ValueSegment>>, candidate: &HashMap<BlockId, ValueSegment>) -> bool {
    for (block, candidate_segment) in candidate {
        if let Some(existing_segments) = existing.get(block) {
            for present in existing_segments {
                if candidate_segment.overlap(present) {
                    return true;
                }
            }
        }
    }
    false
}

fn reduce_registers_with_phi_friends(
    value: ValueId,
    candidate_regs: &mut BTreeSet<usize>,
    phi_friends: &BTreeMap<(ValueId, ValueId), u32>,
    allocation: &RegisterAllocation,
    value_segments: &HashMap<ValueId, HashMap<BlockId, ValueSegment>>,
    register_segments: &[HashMap<BlockId, Vec<ValueSegment>>],
) -> SmallVec<[ValueId; 8]> {
    if candidate_regs.is_empty() { return smallvec![] }
    let mut visited: HashSet<ValueId> = HashSet::default();
    let mut queue: BinaryHeap<(u32, ValueId)> = BinaryHeap::new();
    let mut selected_friends: SmallVec<[ValueId; 8]> = SmallVec::new();

    for ((_, friend), weight) in phi_friends.range((value, ValueId(i32::MIN))..=(value, ValueId(i32::MAX))) {
        if *friend != value {
            queue.push((*weight, *friend));
        }
    }

    'main: while let Some((_weight, friend)) = queue.pop() {
        if !visited.insert(friend) {
            continue;
        }

        assert!(!candidate_regs.is_empty());

        if allocation.locations.contains_key(&friend) {
            // already tried to allocate here, but there was a conflict
            continue;
        }

        let friend_segments = &value_segments[&friend];
        // Check no self-conflict with already-selected friends
        for &already_selected in selected_friends.iter().chain(&[value]) {
            let selected_segments = &value_segments[&already_selected];
            for (block, friend_seg) in friend_segments {
                if let Some(ready_seg) = selected_segments.get(block) {
                    if friend_seg.overlap(ready_seg) {
                        // conflicts with already selected friendly value, skip it
                        continue 'main;
                    }
                }
            }
        }

        let mut to_remove: SmallVec<[usize; 8]> = SmallVec::new();
        for &reg_index in candidate_regs.iter() {
            if has_conflict(&register_segments[reg_index], friend_segments) {
                to_remove.push(reg_index);
            }
        }

        if to_remove.len() == candidate_regs.len() {
            continue;
        }

        for reg in to_remove {
            candidate_regs.remove(&reg);
        }
        selected_friends.push(friend);

        for ((_, next), weight) in phi_friends.range((friend, ValueId(i32::MIN))..=(friend, ValueId(i32::MAX))) {
            if *next != value && !visited.contains(next) {
                queue.push((*weight, *next));
            }
        }
    }

    selected_friends
}

fn equivalence_preferences(g: &GraphBuilder) -> BTreeMap<(ValueId, ValueId), u32> {
    let mut result = BTreeMap::new();

    for block in &g.blocks {
        for i in block.instructions.values() {
            if i.inputs.len() == 0 { continue; }
            let OptOp::Jump(condition, into_block) = &i.op else { continue; };

            // conditional branches are bit costlier, as we need to add one more jump if there are moves
            let weight = if condition == &Condition::True { 1 } else { 2 };
            let into_block = g.block_(*into_block);
            for (param, val) in into_block.parameters.iter().zip(i.inputs.iter()) {
                if val.is_computed() {
                    *result.entry((*param, *val)).or_insert(0u32) += weight;
                    *result.entry((*val, *param)).or_insert(0u32) += weight;
                }
            }
        }
    }

    result
}

#[allow(dead_code)]
fn remat_cost(g: &GraphBuilder, lr: &LiveRanges, max_cost: u32) -> HashMap<ValueId, HashMap<InstrId, u32>> {
    let mut rematerializable: HashMap<ValueId, (u32, SmallVec<[ValueId; 4]>)> = HashMap::default();
    let mut pulls_in: HashMap<(ValueId, InstrId), SmallVec<[ValueId;4]>> = HashMap::default();
    for v in g.values.values() {
        let Some(i) = v.assigned_at.and_then(|i| g.get_instruction(i)) else { continue; };
        // if i.effect != OpEffect::None && i.effect != OpEffect::MayFail { }
        let rmat_cost = match i.op {
            OptOp::BinNot | OptOp::ShiftR | OptOp::BoolNot | OptOp::Or | OptOp::And | OptOp::Xor | OptOp::Min | OptOp::Max | OptOp::AbsFactorial | OptOp::Sgn | OptOp::ShiftL | OptOp::DigitSum | OptOp::Add | OptOp::AbsSub | OptOp::Select(_)=>
                10,
            OptOp::Mul => 12,
            OptOp::Div | OptOp::CursedDiv | OptOp::LenSum | OptOp::Mod | OptOp::ModEuclid => 14,
            OptOp::Median => 8 * i.inputs.len() as u32,
            OptOp::Gcd | OptOp::Funkcia | OptOp::Tetration => 19,
            _ => continue
        } + match i.effect {
            OpEffect::MayDeopt => 6,
            OpEffect::MayFail => 4,
            OpEffect::None | OpEffect::CtrIncrement => 0,
            _ => continue
        };

        let uniq_args: BTreeSet<_> = i.iter_inputs().filter(|i| i.is_computed()).collect();

        for used_at in &v.used_at {
            let unlive_args = uniq_args.iter().copied().filter(|i| !lr.is_live_at(*i, *used_at)).collect();

            pulls_in.insert((v.id, *used_at), unlive_args);
        }
        // free code motion?
        let rmat_cost = if v.used_at.len() == 1 && i.effect == OpEffect::None { 0 } else { rmat_cost };
        rematerializable.insert(v.id, (rmat_cost, uniq_args.iter().copied().collect()));
    }

    fn cost_fn(at: InstrId, val: ValueId, rematerializable: &HashMap<ValueId, (u32, SmallVec<[ValueId; 4]>)>, lr: &LiveRanges, max_cost: u32) -> Option<u32> {
        let Some(&(mut cost, ref deps)) = rematerializable.get(&val) else {
            return None
        };
        for dependency in deps {
            if lr.is_live_at(*dependency, at) {
                continue;
            }

            let Some(dep_cost) = cost_fn(at, *dependency, rematerializable, lr, max_cost) else {
                return None;
            };
            cost += dep_cost;
            if cost >= max_cost {
                return None;
            }
        }
        Some(cost)
    }

    let mut result: HashMap<ValueId, HashMap<InstrId, u32>> = HashMap::default();
    for val in g.values.values() {
        if !rematerializable.contains_key(&val.id) {
            continue;
        }
        for at in &val.used_at {
            if let Some(cost) = cost_fn(*at, val.id, &rematerializable, lr, max_cost) {
                result.entry(val.id).or_default().insert(*at, cost);
            }
        }
    }
    result
}

#[derive(Clone, Debug)]
struct LiveRanges {
    pub ranges: HashMap<ValueId, HashMap<BlockId, (InstrId, InstrId)>>,
    #[allow(dead_code)]
    pub live_vars: HashMap<BlockId, Vec<(InstrId, InstrId, ValueId)>>,
}

impl LiveRanges {
    fn is_live_at(&self, val: ValueId, i: InstrId) -> bool {
        self.ranges.get(&val).unwrap().get(&i.0)
            .is_some_and(|(from, to)| *from < i && i <= *to)
    }
}

impl fmt::Display for LiveRanges {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Live Ranges:")?;

        let mut values: Vec<_> = self.ranges.keys().collect();
        values.sort();

        for &val in values {
            write!(f, "  {:6}", format!("{}", val))?;

            let mut blocks: Vec<_> = self.ranges[&val].iter().collect();
            blocks.sort_by_key(|(bid, _)| *bid);

            for (block_id, (from, to)) in blocks {
                if from.1 == 0 && to.1 == u32::MAX {
                    write!(f, " | {}: entire", block_id)?;
                } else if to.1 == u32::MAX {
                    write!(f, " | {}: {}..end", block_id, from.1)?;
                } else {
                    write!(f, " | {}: {}..{}", block_id, from.1, to.1)?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

fn get_instr_stack_effect(i: &OptInstr) -> [ValueId; 2] {
    const N: ValueId = ValueId(0);
    match i.op {
        OptOp::Pop => [i.out, N], // pop value
        OptOp::StackSwap => [i.out, i.inputs[0]], // previous value
        OptOp::Push => [N, N], // nothing removed from stack, can be reverted without any additional pinned values
        _ => [N, N],
    }
}

fn get_value_usage_info(g: &GraphBuilder, block: &BasicBlock, error_will_deopt: bool) -> (BTreeMap<ValueId, u32>, BTreeMap<ValueId, u32>) {
    let mut last_checkpoint: Option<Vec<ValueId>> = None;
    let mut defined_at = BTreeMap::new();
    let mut last_use: BTreeMap<ValueId, u32> = BTreeMap::new();

    for p in &block.parameters { defined_at.insert(*p, 0); }

    for (&iid, i) in block.instructions.iter() {
        if matches!(i.op, OptOp::Checkpoint) {
            last_checkpoint = Some(i.inputs.iter().copied().filter(|c| c.is_computed()).collect());
            continue;
        }
        let needs_checkpoint = i.effect != OpEffect::None && i.effect != OpEffect::ControlFlow && i.effect != OpEffect::CtrIncrement && (error_will_deopt || i.effect != OpEffect::MayFail);
        if last_checkpoint.is_none() && needs_checkpoint {
            // find checkpoint in previous blocks or panic
            let mut block_id = block.id;
            let mut additional_values = vec![];
            'search_for_checkpoint: loop {
                if block_id.is_first_block() {
                    last_checkpoint = Some(additional_values.clone()); // starting point is empty stack, no problem
                    break 'search_for_checkpoint;
                }
                let b = g.block_(block_id);
                if g.block_(block_id).incoming_jumps.len() != 1 {
                    panic!("Cannot determine deopt stack of {}, the {} block has multiple incoming jumps:\n\n{g}", i.id, block_id)
                }
                block_id = b.incoming_jumps[0].block_id();
                for i in g.block_(block_id).instructions.values().rev() {
                    if i.op == OptOp::Checkpoint {
                        last_checkpoint = Some(i.inputs.iter().copied().filter(|c| c.is_computed()).collect());
                        last_checkpoint.as_mut().unwrap().extend(additional_values);
                        break 'search_for_checkpoint;
                    }
                    additional_values.extend(get_instr_stack_effect(i).into_iter().filter(|v| v.is_computed()));
                }
            }
        }

        for input in i.iter_inputs() {
            if input.is_computed() {
                last_use.insert(input, iid);
            }
        }
        if needs_checkpoint {
            for &v in last_checkpoint.as_ref().unwrap() {
                last_use.insert(v, iid);
            }
        }
        if i.out.is_computed() { defined_at.insert(i.out, iid); }

        for x in get_instr_stack_effect(i) {
            if x.is_computed() {
                last_checkpoint.as_mut().unwrap().push(x);
            }
        }
    }
    (defined_at, last_use)
}

fn analyze_value_lifetimes(g: &GraphBuilder, error_will_deopt: bool) -> LiveRanges {
    //  defined values -> used values
    let blocks: Vec<(HashSet<ValueId>, HashSet<ValueId>)> =
        g.blocks.iter().map(|b| {
            let (defined, require) = get_value_usage_info(g, b, error_will_deopt);
            (defined.keys().copied().collect(),
             require.keys().copied().filter(|v| !defined.contains_key(v)).collect())
        })
        .collect();

    let perblock_req = dataflow(g, /*reverse:*/ true,
        |b| blocks[b.id.0 as usize].1.clone(),
        |b, state, _inputs, outputs| {
            let mut required = state.clone();
            let defines = &blocks[b.id.0 as usize].0;
            for out in outputs {
                for val in *out {
                    if !defines.contains(val) {
                        required.insert(*val);
                    }
                }
            }
            return required
        });

    let mut ranges = HashMap::default();
    let mut live_vars = HashMap::default();
    for block in &g.blocks {
        let (defined_at, last_use) = get_value_usage_info(g, block, error_will_deopt);

        let mut result = vec![];

        for (_, jump_to) in &block.outgoing_jumps {
            for &next_requires in perblock_req.get(&jump_to).iter().flat_map(|x| *x) {
                let &from = defined_at.get(&next_requires).unwrap_or(&0);
                result.push((InstrId(block.id, from), InstrId(block.id, u32::MAX), next_requires));
                // last_use.remove(&next_requires);
                // defined_at.remove(&next_requires);
            }
        }

        for (&var, &last_use) in last_use.iter() {
            let &from = defined_at.get(&var).unwrap_or(&0);
            result.push((InstrId(block.id, from), InstrId(block.id, last_use), var));
        }

        // (output-only values need to get written somewhere)
        for (&var, &def_at) in defined_at.iter() {
            if !last_use.contains_key(&var) {
                result.push((InstrId(block.id, def_at), InstrId(block.id, def_at), var));
            }
        }

        for (from, to, var) in &result {
            let var_ranges: &mut HashMap<BlockId, (InstrId, InstrId)> = ranges.entry(*var).or_default();
            // assert!(!var_ranges.contains_key(&block.id), "{result:?} has duplicated value {var}");
            // var_ranges.insert(block.id, (from.clone(), to.clone()));
            var_ranges.entry(block.id).or_insert((from.clone(), to.clone()));
        }

        live_vars.insert(block.id, result);
    }

    LiveRanges { ranges, live_vars }
}


#[cfg(test)]
mod lowering_tests {
    use super::*;
    use crate::compiler::{cfg::GraphBuilder, ops::{OptOp, ValueId}};
    use std::ops::RangeInclusive;

    fn graph_with_param(range: RangeInclusive<i64>) -> (GraphBuilder, ValueId) {
        let mut g = GraphBuilder::new(0);

        let param = {
            let info = g.new_value();
            info.range = range;
            info.id
        };

        g.current_block_mut().parameters.push(param);
        (g, param)
    }

    fn compile_binary(op: OptOp<ValueId>, lhs_range: RangeInclusive<i64>, rhs_const: i64) -> Vec<OsmibyteOp<RegId>> {
        let (mut g, lhs) = graph_with_param(lhs_range);

        let rhs = g.store_constant(rhs_const);
        let (out, _instr) = g.push_instr(op, &[lhs, rhs], false, None, None);
        let (_out2, _instr2) = g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);
        println!("CFG: {g}");
        let block = OsmibytecodeBlock::from_cfg(&g);
        println!("{:?}", block);
        block.program.iter().cloned().collect()
    }

    #[test]
    fn mod_bitshift_opt() {
        let program = compile_binary(OptOp::Mod, 0..=100, 8);
        assert!(program.iter().any(|op| matches!(op, OsmibyteOp::AndConst(_, _, 7))));
        assert!(!program.iter().any(|op| matches!(op, OsmibyteOp::ModConst(_, _, _))));
    }

    #[test]
    fn mod_bitshift_opt_no() {
        let program = compile_binary(OptOp::Mod, -5..=5, 8);
        assert!(program.iter().any(|op| matches!(op, OsmibyteOp::ModConst(_, _, 8))));
        assert!(!program.iter().any(|op| matches!(op, OsmibyteOp::AndConst(_, _, _))));
    }

    #[test]
    fn mod_euclid_bitshift_opt() {
        let program = compile_binary(OptOp::ModEuclid, -10..=10, 8);
        assert!(matches!(&program[..], [
            OsmibyteOp::AndConst(_, _, 7),
            OsmibyteOp::AddConst(_, _, 2),
        ]));
    }

    #[test]
    fn fusing_cscs() {
        let (mut g, param) = graph_with_param(0..=99_999);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, second], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DigitSumTwice(_, _), OsmibyteOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_cscslensum() {
        let (mut g, param) = graph_with_param(0..=1_000_000);

        let (first, _) = g.push_instr(OptOp::DigitSum, &[param], false, None, None);
        let (second, _) = g.push_instr(OptOp::DigitSum, &[first], false, None, None);
        let (lensum, _) = g.push_instr(OptOp::LenSum, &[second, first], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, lensum], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DigitSumDigitSumLensum(_, _), OsmibyteOp::AddConst(_, _, 2) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_median2() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::MedianCursed2(_, _) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn fusing_median2_no1() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        g.push_instr(OptOp::DigitSum, &[div_out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DivConst(_, _, 2), OsmibyteOp::AddConst(_, _, 1), OsmibyteOp::DigitSum(_, _) ]), "{block}\n{:?}", block.program);
    }
    #[test]
    fn fusing_median2_no2() {
        let (mut g, param) = graph_with_param(-1_000..=1_000);

        let (div_out, _) = g.push_instr(OptOp::Div, &[param, ValueId::C_TWO], false, None, None);
        let (median_candidate, _) = g.push_instr(OptOp::Add, &[ValueId::C_ONE, div_out], false, None, None);
        let (add2, _) = g.push_instr(OptOp::Add, &[ValueId::C_TWO, median_candidate], false, None, None);
        g.stack.push(add2);
        g.stack.poped_values.push(median_candidate);
        g.clean_poped_values();

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(matches!(&block.program[..], [OsmibyteOp::DivConst(_, _, 2), OsmibyteOp::AddConst(_, _, 3) ]), "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_0_branch() {
        let (mut g, cond) = graph_with_param(-5..=5);

        let true_val = g.store_constant(6);
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(cond, 0)), &[true_val, ValueId::C_ZERO], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConst0(_, _, 6))));
    }

    #[test]
    fn select_consts() {
        let (mut g, cond) = graph_with_param(-3..=3);

        let true_val = g.store_constant(3);
        let false_val = g.store_constant(-2);
        let (out, _) = g.push_instr(OptOp::Select(Condition::NeqConst(cond, 0)), &[true_val, false_val], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_TWO, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConst(_, _, 3, -2))));
    }

    #[test]
    fn select_const_reg() {
        let (mut g, param) = graph_with_param(0..=100);

        // Test: select(param == 0, 42, param * 2)
        let double = g.push_instr(OptOp::Mul, &[ValueId::C_TWO, param], false, None, None).0;
        let const_val = g.store_constant(42);
        let (out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[const_val, double], false, None, None);
        g.push_instr(OptOp::Add, &[ValueId::C_ONE, out], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(block.program.iter().any(|op| matches!(op, OsmibyteOp::SelectConstReg(_, _, 42, _))));
    }

    #[test]
    fn select_to_boolnot_eq() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param == 0, 1, 0) -> BoolNot(param)
        let (_, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], false, None, None);
        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::BoolNot(_, _)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_boolnot_neq() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param != 0, 0, 1) -> BoolNot(param)
        let (_, _) = g.push_instr(OptOp::Select(Condition::NeqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);
        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::BoolNot(_, _)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_sgn_eq_nonneg() {
        let (mut g, param) = graph_with_param(0..=100);

        // select(param == 0, 0, 1) -> Sgn(param) when param >= 0
        let (_out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::Sgn(_, _)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_to_sgn_neq_nonneg() {
        let (mut g, param) = graph_with_param(0..=100);

        // select(param != 0, 1, 0) -> Sgn(param) when param >= 0
        let (_out, _) = g.push_instr(OptOp::Select(Condition::NeqConst(param, 0)), &[ValueId::C_ONE, ValueId::C_ZERO], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::Sgn(_, _)]),
            "{block}\n{:?}", block.program);
    }

    #[test]
    fn select_no_sgn_with_negative_range() {
        let (mut g, param) = graph_with_param(-10..=10);

        // select(param == 0, 0, 1) should NOT become Sgn when param can be negative
        let (_out, _) = g.push_instr(OptOp::Select(Condition::EqConst(param, 0)), &[ValueId::C_ZERO, ValueId::C_ONE], false, None, None);

        let block = OsmibytecodeBlock::from_cfg(&g);
        assert!(
            matches!(&block.program[..], [OsmibyteOp::SelectConst0(_, _, 1) | OsmibyteOp::SelectConst(_, _, 0, 1)]),
            "{block}\n{:?}", block.program);
    }
}

#[cfg(test)]
mod register_alloc_tests {
    use super::*;

    fn build_phi_merge_graph() -> (GraphBuilder, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let entry_id = g.current_block;

        let seed = g.new_value().id;

        let (friend, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);

        let phi = g.new_value().id;
        let block1_id = g.new_block(0, true, vec![phi]).id;

        let jump_id = g.push_instr(OptOp::Jump(Condition::True, block1_id), &[friend], false, None, None).1.unwrap().id;

        let block1 = g.block_mut(block1_id).unwrap();
        block1.incoming_jumps.push(jump_id);
        block1.predecessors.insert(entry_id);

        g.switch_to_block(block1_id, 0, vec![]);
        g.push_instr(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[], false, None, None);

        (g, phi, friend)
    }

    fn build_conflicting_phi_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let entry_id = g.current_block;

        let seed = g.new_value().id;

        let (friend, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);

        let phi = g.new_value().id;
        let block1_id = g.new_block(0, true, vec![phi]).id;

        let jump_id = g.push_instr(OptOp::Jump(Condition::True, block1_id), &[friend], false, None, None).1.unwrap().id;

        let block1 = g.block_mut(block1_id).unwrap();
        block1.incoming_jumps.push(jump_id);
        block1.predecessors.insert(entry_id);

        g.switch_to_block(block1_id, 0, vec![]);

        let (block_local, _) = g.push_instr(OptOp::Add, &[phi, ValueId::C_ONE], false, None, None);
        let (_mixed, _) = g.push_instr(OptOp::Add, &[phi, block_local], false, None, None);
        g.push_instr(OptOp::Add, &[block_local, ValueId::C_ONE], false, None, None);

        (g, phi, friend, block_local)
    }

    #[test]
    fn phi_friends_share_register_when_lifetimes_do_not_conflict() {
        let (g, phi, friend) = build_phi_merge_graph();
        let allocation = allocate_registers(&g, 10, true);

        let phi_location = allocation.location(phi);
        let friend_location = allocation.location(friend);

    assert_eq!(phi_location, Some(ValueLocation::Register(RegId(0))));
        assert_eq!(phi_location, friend_location);
    }

    #[test]
    fn pressure_causes_spilling() {
        let (g, phi, friend, block_local) = build_conflicting_phi_graph();
        println!("{g}");
        let allocation = allocate_registers(&g, 1, true);
        println!("{allocation}");

        // With phi-friend merging, phi and friend share a register
        // So with only 1 register available, block_local must spill
        assert!(allocation.location(phi) == allocation.location(friend) ||
                matches!(allocation.location(phi), Some(ValueLocation::Spill(_))));
        assert!(matches!(allocation.location(block_local), Some(ValueLocation::Spill(_))) ||
                matches!(allocation.location(phi), Some(ValueLocation::Spill(_))), "block_local={block_local} phi={phi}");
    }

    #[test]
    fn register_conflict_across_bb() {
        let (g, phi, friend, block_local) = build_conflicting_phi_graph();
        println!("{g}");
        let allocation = allocate_registers(&g, 2, true);
        println!("{allocation}");

        assert!(matches!(allocation.location(phi), Some(ValueLocation::Register(_))));
        assert!(matches!(allocation.location(friend), Some(ValueLocation::Register(_))));
        assert!(matches!(allocation.location(block_local), Some(ValueLocation::Register(_))));

        // With phi-friend merging, phi and friend SHOULD share a register
        // since they're phi-friends with non-overlapping lifetimes
        assert_eq!(allocation.location(phi), allocation.location(friend));

        // block_local should get a different register since it's live at the same time as phi
        assert_ne!(allocation.location(phi), allocation.location(block_local));
    }

    fn setup_diamond_cfg(g: &mut GraphBuilder, seed: ValueId, val1: ValueId, val2: ValueId) -> (BlockId, BlockId) {
        let entry_id = g.current_block;
        let branch1_id = g.new_block(0, true, vec![]).id;
        let branch2_id = g.new_block(0, true, vec![]).id;

        g.switch_to_block(entry_id, 0, vec![]);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::GtConst(seed, 0), branch1_id), &[val1], false, None, None).1.unwrap().id;
        let jump2_id = g.push_instr(OptOp::Jump(Condition::LeqConst(seed, 0), branch2_id), &[val2], false, None, None).1.unwrap().id;

        g.block_mut(branch1_id).unwrap().predecessors.insert(entry_id);
        g.block_mut(branch1_id).unwrap().incoming_jumps.push(jump1_id);
        g.block_mut(branch2_id).unwrap().predecessors.insert(entry_id);
        g.block_mut(branch2_id).unwrap().incoming_jumps.push(jump2_id);

        (branch1_id, branch2_id)
    }

    fn finalize_diamond_merge(g: &mut GraphBuilder, merge_id: BlockId, branch1_id: BlockId,
                               branch2_id: BlockId, jump1_id: InstrId, jump2_id: InstrId) {
        let merge_block = g.block_mut(merge_id).unwrap();
        merge_block.incoming_jumps.push(jump1_id);
        merge_block.incoming_jumps.push(jump2_id);
        merge_block.predecessors.insert(branch1_id);
        merge_block.predecessors.insert(branch2_id);
    }

    fn build_diamond_phi_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);
        let seed = g.new_value().id;
        g.current_block_mut().parameters.push(seed);

        let phi = g.new_value().id;
        let merge_id = g.new_block(0, true, vec![phi]).id;

        let (branch1_id, branch2_id) = setup_diamond_cfg(&mut g, seed, seed, seed);

        g.switch_to_block(branch1_id, 0, vec![]);
        let (val1, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val1], false, None, None).1.unwrap().id;

        g.switch_to_block(branch2_id, 0, vec![]);
        let (val2, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_TWO], false, None, None);
        let jump2_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val2], false, None, None).1.unwrap().id;

        finalize_diamond_merge(&mut g, merge_id, branch1_id, branch2_id, jump1_id, jump2_id);

        g.switch_to_block(merge_id, 0, vec![]);
        g.push_instr_may_deopt(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[]);

        (g, phi, val1, val2)
    }

    #[test]
    fn phi_with_two_incoming_edges_unified() {
        let (g, phi, val1, val2) = build_diamond_phi_graph();
        let allocation = allocate_registers(&g, 10, true);
        println!("{phi} {val1} {val2}\n{g}\n{allocation}");

        let phi_location = allocation.location(phi);
        let val1_location = allocation.location(val1);
        let val2_location = allocation.location(val2);

        // All three should be allocated to the same register since lifetimes don't overlap
        assert_eq!(phi_location, val1_location);
        assert_eq!(phi_location, val2_location);
    }

    fn build_diamond_conflicting_graph() -> (GraphBuilder, ValueId, ValueId, ValueId) {
        let mut g = GraphBuilder::new(0);

        let seed = g.new_value().id;
        g.current_block_mut().parameters.push(seed);

        // Create val1 and val2 that have overlapping lifetimes in entry block
        let (val1, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_ONE], false, None, None);
        let (val2, _) = g.push_instr(OptOp::Add, &[seed, ValueId::C_TWO], false, None, None);

        let phi = g.new_value().id;
        let merge_id = g.new_block(0, true, vec![phi]).id;

        let (branch1_id, branch2_id) = setup_diamond_cfg(&mut g, seed, val1, val2);

        g.switch_to_block(branch1_id, 0, vec![]);
        let jump1_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val1], false, None, None).1.unwrap().id;

        g.switch_to_block(branch2_id, 0, vec![]);
        let jump2_id = g.push_instr(OptOp::Jump(Condition::True, merge_id), &[val2], false, None, None).1.unwrap().id;

        finalize_diamond_merge(&mut g, merge_id, branch1_id, branch2_id, jump1_id, jump2_id);

        g.switch_to_block(merge_id, 0, vec![]);
        g.push_instr_may_deopt(OptOp::Assert(Condition::EqConst(phi, 0), OperationError::IntegerOverflow), &[]);

        (g, phi, val1, val2)
    }

    #[test]
    fn phi_with_two_incoming_edges_conflicting() {
        let (g, phi, val1, val2) = build_diamond_conflicting_graph();
        let allocation = allocate_registers(&g, 10, true);
        println!("{phi} {val1} {val2}\n{g}\n{allocation}");
        println!("{:?}", g.val_info(val1).unwrap());
        println!("{:?}", g.val_info(val2).unwrap());

        let phi_location = allocation.location(phi);
        let val1_location = allocation.location(val1);
        let val2_location = allocation.location(val2);

        assert!(matches!(phi_location, Some(ValueLocation::Register(_))));
        assert!(matches!(val1_location, Some(ValueLocation::Register(_))));
        assert!(matches!(val2_location, Some(ValueLocation::Register(_))));

        assert_ne!(val2_location, val1_location);
        assert!(val2_location == phi_location || val1_location == phi_location);
    }
}


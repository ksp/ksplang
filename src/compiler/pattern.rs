use std::{borrow::Cow, collections::BTreeMap, fmt, ops::{Range, RangeBounds, RangeInclusive}, sync::Arc};

use smallvec::SmallVec;

use crate::compiler::{cfg::GraphBuilder, ops::{OptInstr, OptOp, ValueId, ValueInfo}, osmibytecode::Condition, range_ops::{IRange, from_rangebounds}};

#[derive(Clone)]
pub struct HackEqDebug<T, TId>(pub T, pub TId);
impl<T, TId: PartialEq> PartialEq for HackEqDebug<T, TId> {
    fn eq(&self, other: &Self) -> bool { self.1 == other.1 }
}
impl<T, TId: Eq> Eq for HackEqDebug<T, TId> {}
impl<T, TId: std::hash::Hash> std::hash::Hash for HackEqDebug<T, TId> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.1.hash(state); }
}
impl<T, TId: fmt::Debug> fmt::Debug for HackEqDebug<T, TId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.1.fmt(f) }
}

#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct OptOptPattern<'a> {
    pub options_values: SmallVec<[ValueId; 4]>,
    pub options_ops: Vec<(OptOp<Box<OptOptPattern<'a>>>, Vec<OptOptPattern<'a>>)>,
    pub anything_in_range: SmallVec<[(i64, i64); 1]>,
    pub constant_in_range: SmallVec<[(i64, i64); 1]>,
    pub custom: Option<HackEqDebug<Arc<dyn Fn(&GraphBuilder, &[ValueId], &mut MatchInfo<'a>) -> Option<ValueId> + Sync + Send + 'a>, String>>,
    pub greedy_backrefs: Vec<Cow<'a, str>>,
    pub name: Option<Cow<'a, str>>,
    pub variadic: bool,
    pub allow_empty: bool,
    pub disable_commutativity: bool,
}

impl From<ValueId> for OptOptPattern<'_> {
    fn from(val: ValueId) -> Self { OptOptPattern::val(val) }
}
impl From<ValueId> for Box<OptOptPattern<'_>> {
    fn from(val: ValueId) -> Self { OptOptPattern::val(val).boxed() }
}
impl From<IRange> for OptOptPattern<'_> {
    fn from(range: IRange) -> Self { OptOptPattern::constant(range) }
}
impl From<IRange> for Box<OptOptPattern<'_>> {
    fn from(range: IRange) -> Self { OptOptPattern::constant(range).boxed() }
}
impl From<i64> for OptOptPattern<'_> {
    fn from(c: i64) -> Self { OptOptPattern::const_(c) }
}
impl From<i64> for Box<OptOptPattern<'_>> {
    fn from(c: i64) -> Self { OptOptPattern::const_(c).boxed() }
}

// impl<'a, T1, T2> From<(T1, T2)> for Vec<OptOptPattern<'a>> where T1: Into<OptOptPattern<'a>>, T2: Into<OptOptPattern<'a>> {
//     fn from((a, b): (T1, T2)) -> Self {
//         vec![a.into(), b.into()]
//     }
// }
// impl<T: Into<OptOptPattern<'_>>> From<T> for Box<OptOptPattern<'_>> {
//     fn from(val: ValueId) -> Self { Box::new(val.into()) }
// }

impl<'a> OptOptPattern<'a> {
    pub fn op(op: OptOp<Box<OptOptPattern<'a>>>, args: impl Into<Vec<OptOptPattern<'a>>>) -> Self {
        Self::default().or_op(op, args.into())
    }

    pub fn op0(op: OptOp<Box<OptOptPattern<'a>>>) -> Self {
        Self::default().or_op(op, vec![])
    }
    pub fn op1(op: OptOp<Box<OptOptPattern<'a>>>, a: impl Into<OptOptPattern<'a>>) -> Self {
        Self::default().or_op(op, vec![a.into()])
    }
    pub fn op2(op: OptOp<Box<OptOptPattern<'a>>>, a: impl Into<OptOptPattern<'a>>, b: impl Into<OptOptPattern<'a>>) -> Self {
        Self::default().or_op(op, vec![a.into(), b.into()])
    }

    pub fn val(val: ValueId) -> Self {
        Self::default().or_value(val)
    }

    pub fn range(range: RangeInclusive<i64>) -> Self {
        Self::default().or_in_range(range)
    }

    pub fn constant(range: impl RangeBounds<i64>) -> Self {
        Self::default().or_constant(from_rangebounds(range))
    }

    pub fn const_(x: i64) -> Self { Self::constant(x..=x) }

    pub fn newbackref(name: impl Into<Cow<'a, str>>) -> Self {
        Self::default().or_backref(name)
    }

    pub fn any() -> Self { Self::range(i64::MIN..=i64::MAX) }

    pub fn or_value(mut self, val: ValueId) -> Self {
        self.options_values.push(val);
        self
    }

    pub fn or_op(mut self, op: OptOp<Box<OptOptPattern<'a>>>, args: impl Into<Vec<OptOptPattern<'a>>>) -> Self {
        self.options_ops.push((op, args.into()));
        self
    }

    pub fn or_in_range(mut self, range: RangeInclusive<i64>) -> Self {
        self.anything_in_range.push(range.into_inner());
        Self::consolidate_ranges(&mut self.anything_in_range);
        self
    }

    pub fn or_constant(mut self, range: RangeInclusive<i64>) -> Self {
        self.constant_in_range.push(range.into_inner());
        Self::consolidate_ranges(&mut self.constant_in_range);
        self
    }

    pub fn or_backref(mut self, name: impl Into<Cow<'a, str>>) -> Self {
        self.greedy_backrefs.push(name.into());
        self
    }

    pub fn variadic(mut self, variadic: bool, allow_empty: bool) -> Self {
        self.variadic = variadic;
        self.allow_empty = allow_empty;
        self
    }

    pub fn optional(mut self, optional: bool) -> Self {
        self.allow_empty = optional;
        self
    }

    pub fn named(mut self, name: impl Into<Cow<'a, str>>) -> Self {
        self.name = Some(name.into());
        self
    }

    pub fn boxed(self) -> Box<Self> { Box::new(self) }

    pub fn try_match(&'_ self, cfg: &GraphBuilder, val: &[ValueId]) -> Result<MatchInfo<'_>, ()> {
        let mut info = MatchInfo::new();
        self.match_internal(cfg, val, &mut info)?;
        Ok(info)
    }

    fn consolidate_ranges(r: &mut SmallVec<[(i64, i64); 1]>) {
        if r.len() <= 1 { return; }
        r.sort_by_key(|r| r.0);
        let mut i = 0;
        while i + 1 < r.len() {
            if r[i].1 + 1 >= r[i + 1].0 {
                r[i].1 = r[i].1.max(r[i + 1].1);
                r.remove(i + 1);
            } else {
                i += 1;
            }
        }
    }

    fn constant_matches(&self, v: i64) -> bool {
        for (start, end) in self.constant_in_range.iter().chain(self.anything_in_range.iter()) {
            if *start <= v && v <= *end {
                return true;
            }
        }
        false
    }

    fn match_internal(&self, cfg: &GraphBuilder, val: &[ValueId], info: &mut MatchInfo<'a>) -> Result<ValueId, ()> {
        // println!("match_internal({val:?}, {self})");
        let v = self.match_core(cfg, val, info)?;
        info.values.push(v);
        if let Some(name) = &self.name {
            info.named.push((name.clone(), v))
        }
        // println!("match_internal({val:?}, {self}) -> Ok({v})");
        return Ok(v)
    }
    fn match_core(&self, cfg: &GraphBuilder, val: &[ValueId], info: &mut MatchInfo<'a>) -> Result<ValueId, ()> {
        for vv in &self.options_values {
            if val.contains(vv) {
                return Ok(*vv);
            }
        }
        if !self.anything_in_range.is_empty() || !self.constant_in_range.is_empty() {
            for v in val.iter().filter(|c| c.is_constant()) {
                if let Some(c) = cfg.get_constant(*v) {
                    if self.constant_matches(c) {
                        info.constants.push(c);
                        return Ok(*v);
                    }
                }
            }
        }
        if !self.options_ops.is_empty() || !self.anything_in_range.is_empty() {
            for v in val {
                let val_info = cfg.val_info(*v).ok_or(())?;
                for (start, end) in self.anything_in_range.iter() {
                    if *start <= *val_info.range.start() && *val_info.range.end() <= *end {
                        return Ok(*v);
                    }
                }

                if !self.options_ops.is_empty() {
                    let Some(instr_id) = val_info.assigned_at else { continue; };
                    let Some(instr) = cfg.get_instruction(instr_id) else { continue; };
                    for (op, args) in &self.options_ops {
                        if Self::matches_instr(info, cfg, *v, &val_info, instr, op, args, !self.disable_commutativity) {
                            return Ok(*v);
                        }
                    }
                }
            }
        }
        if let Some(custom) = &self.custom {
            let f = custom.0.as_ref();
            let sp = info.save_point();
            if let Some(v) = f(cfg, val, info) {
                return Ok(v)
            } else {
                info.revert_to(&sp);
            }
        }
        for backref in &self.greedy_backrefs {
            if let Some((_, found)) = info.named.iter().find(|(name, found)| backref.as_ref() == name.as_ref() && val.contains(found)) {
                return Ok(*found)
            }
        }
        Err(())
    }

    fn matches_instr(info: &mut MatchInfo<'a>, cfg: &GraphBuilder, _val: ValueId, _val_info: &ValueInfo, instr: &OptInstr, pattern: &OptOp<Box<OptOptPattern<'a>>>, args: &[OptOptPattern<'a>], allow_commutativity: bool) -> bool {
        if instr.op.discriminant() != pattern.discriminant() {
            return false;
        }
        let comm = if allow_commutativity { instr.op.is_commutative(instr.inputs.len()) } else { 0..0 };
        match (&instr.op, pattern) {
            (OptOp::Const(c1), OptOp::Const(c2)) => *c1 == *c2,
            (OptOp::Pop, OptOp::Pop) |
            (OptOp::Push, OptOp::Push) |
            (OptOp::Nop, OptOp::Nop) |
            (OptOp::Add, OptOp::Add) |
            (OptOp::Sub, OptOp::Sub) |
            (OptOp::AbsSub, OptOp::AbsSub) |
            (OptOp::Mul, OptOp::Mul) |
            (OptOp::Div, OptOp::Div) |
            (OptOp::CursedDiv, OptOp::CursedDiv) |
            (OptOp::Mod, OptOp::Mod) |
            (OptOp::ModEuclid, OptOp::ModEuclid) |
            (OptOp::Tetration, OptOp::Tetration) |
            (OptOp::Funkcia, OptOp::Funkcia) |
            (OptOp::LenSum, OptOp::LenSum) |
            (OptOp::Max, OptOp::Max) |
            (OptOp::Min, OptOp::Min) |
            (OptOp::Sgn, OptOp::Sgn) |
            (OptOp::AbsFactorial, OptOp::AbsFactorial) |
            (OptOp::Universal, OptOp::Universal) |
            (OptOp::And, OptOp::And) |
            (OptOp::Or, OptOp::Or) |
            (OptOp::Xor, OptOp::Xor) |
            (OptOp::ShiftL, OptOp::ShiftL) |
            (OptOp::ShiftR, OptOp::ShiftR) |
            (OptOp::BinNot, OptOp::BinNot) |
            (OptOp::BoolNot, OptOp::BoolNot) |
            (OptOp::Median, OptOp::Median) |
            (OptOp::MedianCursed, OptOp::MedianCursed) |
            (OptOp::DigitSum, OptOp::DigitSum) |
            (OptOp::StackSwap, OptOp::StackSwap) |
            (OptOp::StackRead, OptOp::StackRead) |
            (OptOp::Gcd, OptOp::Gcd) => {
                Self::match_list(info, cfg, &instr.inputs, args, comm)
            },
            (OptOp::Select(cond), OptOp::Select(pcond)) => {
                let save = info.save_point();
                if Self::match_condition(cfg, info, cond, pcond).is_ok() &&
                    Self::match_list(info, cfg, &instr.inputs, args, 0..0) {
                    true
                } else {
                    info.revert_to(&save);
                    if Self::match_condition(cfg, info, &cond.clone().neg(), pcond).is_ok() &&
                        Self::match_list(info, cfg, &[instr.inputs[1], instr.inputs[0]], args, 0..0) {
                        true
                    } else {
                        info.revert_to(&save);
                        false
                    }
                }
            },
            (OptOp::Assert(cond, err1 ), OptOp::Assert(pcond, err2)) => {
                if err1 != err2 { return false; }
                let save = info.save_point();
                if Self::match_condition(cfg, info, cond, pcond).is_ok() &&
                    Self::match_list(info, cfg, &instr.inputs, args, comm) {
                    true
                } else {
                    info.revert_to(&save);
                    false
                }
            },
            (_, _) => false,
        }
    }

    fn match_list(info: &mut MatchInfo<'a>, cfg: &GraphBuilder, vals: &[ValueId], patterns: &[OptOptPattern<'a>], commutativity: Range<usize>) -> bool {
        if patterns.is_empty() { return vals.is_empty(); }
        if vals.is_empty() { return patterns.iter().all(|p| p.allow_empty); }

        let save1 = info.save_point();

        if commutativity.contains(&0) {
            assert_eq!(commutativity.end, vals.len(), "this is not needed by any op and I'm too lazy to code it");
            // set problem up to parameter commutativity.end()
            let mut matches: BTreeMap<ValueId, Vec<u32>> = BTreeMap::new();
            for (i, p) in patterns.iter().enumerate().filter(|p| !p.1.allow_empty) {
                let Ok(matched) = p.match_internal(cfg, vals, info) else {
                    return false; // mandatory pattern did not match anything
                };
                matches.entry(matched).or_default().push(i as u32);
            }
            // maybe this is already good enough and we don't need to go quadratic?
            if matches.values().all(|v| v.len() == 1) && matches.len() == vals.len() {
                return true;
            }

            info.revert_to(&save1);

            for (i, p) in patterns.iter().enumerate() {
                for v in vals {
                    if matches.get(v).is_some_and(|v| v.contains(&(i as u32))) {
                        continue;
                    }

                    if let Ok(matched) = p.match_internal(&cfg, &[*v], info) {
                        info.revert_to(&save1);
                        matches.entry(matched).or_default().push(i as u32);
                    }
                }
            }
            if matches.len() != vals.len() {
                return false;
            }

            let mut used = vec![0; patterns.len()];
            let mut final_map = vec![];
            for (v, matched) in matches {
                let free_maps = matched.iter().filter(|i| used[**i as usize] == 0 || patterns[**i as usize].variadic).collect::<Vec<_>>();
                if free_maps.is_empty() {
                    return false;
                }
                if free_maps.len() == 1 {
                    used[*free_maps[0] as usize] += 1;
                    final_map.push((v, *free_maps[0]));
                }
            }
            if !final_map.len() != vals.len() { todo!() }
            info.assert_is_at(&save1);
            for (v, p) in final_map {
                assert!(patterns[p as usize].match_internal(cfg, &[v], info).is_ok());
            }
            true

        } else {
            if patterns[0].match_internal(cfg, &vals[0..1], info).is_ok() {
                if patterns[0].variadic {
                    let min_remaining = patterns[1..].iter().filter(|p| !p.allow_empty).count();
                    let mut saves = vec![];
                    for i in 1..vals.len().saturating_sub(min_remaining) {
                        let save = info.save_point();
                        saves.push(save);
                        let m = patterns[0].match_internal(cfg, &[vals[i]], info).is_ok();
                        if !m {
                            break;
                        }
                    }

                    for i in (0..saves.len()).rev() {
                        info.revert_to(&saves[i]);
                        if Self::match_list(info, cfg, &vals[1 + i..], &patterns[1..], commutativity.start.saturating_sub(i+1)..commutativity.end.saturating_sub(i+1)) {
                            return true;
                        }
                    }
                    info.revert_to(&save1);
                    false
                } else if patterns[0].allow_empty {
                    let m = Self::match_list(info, cfg, &vals[1..], &patterns[1..], commutativity.start.saturating_sub(1)..commutativity.end.saturating_sub(1));
                    if m { return true; }
                    info.assert_is_at(&save1);
                    Self::match_list(info, cfg, vals, &patterns[1..], commutativity)
                } else {
                    Self::match_list(info, cfg, &vals[1..], &patterns[1..], commutativity.start.saturating_sub(1)..commutativity.end.saturating_sub(1))
                }
            } else if patterns[0].allow_empty {
                info.assert_is_at(&save1);
                return Self::match_list(info, cfg, vals, &patterns[1..], commutativity)
            } else {
                info.assert_is_at(&save1);
                return false;
            }
        }
    }

    fn match_condition(cfg: &GraphBuilder, info: &mut MatchInfo<'a>, cond: &Condition<ValueId>, pattern: &Condition<Box<OptOptPattern<'a>>>) -> Result<bool, ()> {
        match (cond, pattern) {
            (Condition::True, Condition::True) => Ok(true),
            (Condition::False, Condition::False) => Ok(true),
            (Condition::Eq(a, b), Condition::Eq(pa, pb)) |
            (Condition::Neq(a, b), Condition::Neq(pa, pb)) => {
                // commutative conditions
                let save = info.save_point();
                let Ok(res_a) = pa.match_internal(cfg, &[*a, *b], info) else {
                    info.assert_is_at(&save);
                    return Err(());
                };
                let save2 = info.save_point();
                let Ok(res_b) = pb.match_internal(cfg, &[*a, *b], info) else {
                    info.revert_to(&save);
                    return Err(());
                };
                if res_a != res_b {
                    return Ok(true)
                }
                info.revert_to(&save2);
                if pb.match_internal(cfg, &[if res_a == *a { *b } else { *a }], info).is_ok() {
                    return Ok(true)
                }
                info.revert_to(&save);
                if pa.match_internal(cfg, &[if res_a == *a { *b } else { *a }], info).is_ok() &&
                    pb.match_internal(cfg, &[if res_a == *a { *a } else { *b }], info).is_ok() {
                    return Ok(true)
                }
                info.revert_to(&save);
                Err(())
            }
            (Condition::Lt(a, b), Condition::Lt(pa, pb)) |
            (Condition::Lt(a, b), Condition::Gt(pb, pa)) |
            (Condition::Leq(a, b), Condition::Leq(pa, pb)) |
            (Condition::Leq(a, b), Condition::Geq(pb, pa)) |
            (Condition::Gt(a, b), Condition::Gt(pa, pb)) |
            (Condition::Gt(a, b), Condition::Lt(pb, pa)) |
            (Condition::Geq(a, b), Condition::Geq(pa, pb)) |
            (Condition::Geq(a, b), Condition::Leq(pb, pa)) |
            (Condition::Divides(a, b), Condition::Divides(pa, pb)) |
            (Condition::NotDivides(a, b), Condition::NotDivides(pa, pb)) => {
                let save = info.save_point();
                if pa.match_internal(cfg, &[*a], info).is_ok() && pb.match_internal(cfg, &[*b], info).is_ok() {
                    Ok(true)
                } else {
                    info.revert_to(&save);
                    Err(())
                }
            },
            _ => Err(()),
        }
    }
}

impl fmt::Display for OptOptPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = vec![];
        if !self.options_values.is_empty() {
            parts.push(format!("Values({})", self.options_values.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", ")));
        }
        if !self.options_ops.is_empty() {
            parts.push(format!("Ops({})", self.options_ops.iter().map(|(op, args)| format!("{:?}({})", op, args.iter().map(|a| format!("{}", a)).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(", ")));
        }
        if !self.anything_in_range.is_empty() {
            parts.push(format!("Range({})", self.anything_in_range.iter().map(|r| format!("{:?}", r)).collect::<Vec<_>>().join(", ")));
        }
        if !self.constant_in_range.is_empty() {
            parts.push(format!("Const({})", self.constant_in_range.iter().map(|r| 
                if r.0 == r.1 { format!("{}", r.0) } else { format!("{}..={}", r.0, r.1) }
            ).collect::<Vec<_>>().join(", ")));
        }

        let n = self.name.as_ref().map(|s| format!("\"{}\": ", s)).unwrap_or_default();

        let nocomm = if self.disable_commutativity { "no-comm: " } else { "" };

        write!(f, "P({}{}{})", n, nocomm, parts.join(" | "))
    }
}

impl fmt::Debug for OptOptPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}


#[derive(Clone, Debug)]
pub struct MatchInfo<'a> {
    pub constants: SmallVec<[i64; 3]>,
    pub values: SmallVec<[ValueId; 6]>,
    pub named: Vec<(Cow<'a, str>, ValueId)>,
}

impl<'a> MatchInfo<'a> {
    pub fn new() -> Self {
        Self { constants: SmallVec::new(), values: SmallVec::new(), named: Vec::new(), }
    }

    fn save_point(&self) -> MatchInfoSavePoint {
        MatchInfoSavePoint {
            constants_len: self.constants.len(),
            values_len: self.values.len(),
            named_len: self.named.len(),
        }
    }

    fn revert_to(&mut self, sp: &MatchInfoSavePoint) {
        self.constants.truncate(sp.constants_len);
        self.values.truncate(sp.values_len);
        self.named.truncate(sp.named_len);
    }

    fn assert_is_at(&self, sp: &MatchInfoSavePoint) {
        assert_eq!(self.constants.len(), sp.constants_len);
        assert_eq!(self.values.len(), sp.values_len);
        assert_eq!(self.named.len(), sp.named_len);
    }

    pub fn main_value(&self) -> ValueId {
        *self.values.last().expect("MatchInfo is empty")
    }

    pub fn get_named_iter(&'a self, name: &'a str) -> impl Iterator<Item = ValueId> + 'a {
        self.named.iter().filter(move |(n, _)| name == n.as_ref()).map(|(_, v)| *v)
    }

    pub fn get_named_single(&self, name: &str) -> Option<ValueId> {
        let mut iter = self.get_named_iter(name);
        let a = iter.next();
        let b = iter.next();
        if b.is_some() { None } else { a }
    }
}

struct MatchInfoSavePoint {
    constants_len: usize,
    values_len: usize,
    named_len: usize
}

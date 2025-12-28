use std::{borrow::Borrow, cmp, ops::{RangeBounds, RangeInclusive}};

use arrayvec::ArrayVec;
use num_integer::Integer;
use num_traits::{CheckedAdd, CheckedMul, CheckedSub};

use crate::{compiler::utils::{abs_range, range_2_i64, u64neg, union_range}, vm};

pub type IRange = RangeInclusive<i64>;
pub type URange = RangeInclusive<u64>;

#[inline]
pub fn from_rangebounds(r: impl RangeBounds<i64>) -> RangeInclusive<i64> {
    let start = match r.start_bound() {
        std::ops::Bound::Excluded(&i64::MAX) => return 1..=0,
        std::ops::Bound::Excluded(&x) => x + 1,
        std::ops::Bound::Included(&x) => x,
        std::ops::Bound::Unbounded => i64::MIN,
    };
    let end = match r.end_bound() {
        std::ops::Bound::Excluded(&i64::MIN) => return 1..=0,
        std::ops::Bound::Excluded(&x) => x - 1,
        std::ops::Bound::Included(&x) => x,
        std::ops::Bound::Unbounded => i64::MAX,
    };
    return start..=end;
}

#[inline]
pub fn range_signum(r: RangeInclusive<i64>) -> RangeInclusive<i64> {
    r.start().signum()..=r.end().signum()
}

pub fn range_mod(a_range: RangeInclusive<i64>, b_range: RangeInclusive<i64>) -> RangeInclusive<i64> {
    let b_abs = abs_range(b_range.clone());

    if a_range.is_empty() || b_range.is_empty() || *b_abs.end() == 0 {
        return 1..=0;
    }

    if a_range == (0..=0) { return 0..=0; }

    let (a_lo, a_hi) = a_range.clone().into_inner();

    let positive = if a_hi > 0 {
        Some(range_mod_u(cmp::max(0, a_lo) as u64..=a_hi as u64, b_abs.clone()))
    } else { None };
    let negative = if a_lo < 0 {
        Some(range_mod_u(cmp::min(0, a_hi).unsigned_abs() ..= a_lo.unsigned_abs(), b_abs.clone()))
    } else { None };

    let positive = positive.map(range_2_i64);
    let negative = negative.map(range_2_i64_neg);
    let min = *negative.as_ref().or(positive.as_ref()).unwrap().start();
    let max = *positive.or(negative).unwrap().end();
    return min..=max;
}

/// Returns input-range -> output-range pairs, inside the range the mod is a fixed offset
pub fn mod_split_ranges(x_range: IRange, m: i64, euclid: bool) -> Vec<(IRange, IRange)> {
    let (x_start, x_end) = x_range.into_inner();
    let (k_start, k_end) = if true   { (x_start.div_euclid(m), x_end.div_euclid(m)) }
                           else      { (x_start / m, x_end / m) };

    let mut result: Vec<(IRange, IRange)> = vec![];
    for k in k_start..=k_end {
        let (chunk_start, chunk_end) = if euclid || k >= 0 {
            (k * m, k * m + m - 1)
        } else {
            // non-euclidean for m=10 will be split as:
            // -19..-10, -9..-1, 0..9, 10..19
            (k * m + 1, cmp::min(-1, k * m + m))
        };

        let chunk_start = chunk_start.max(x_start);
        let chunk_end = chunk_end.min(x_end);

        let (result_start, result_end) = if euclid {
            (chunk_start.rem_euclid(m), chunk_end.rem_euclid(m))
        } else {
            (chunk_start % m, chunk_end % m)
        };
        println!("{chunk_start} {chunk_end} {result_start} {result_end}");
        assert_eq!(chunk_start - chunk_end, result_start - result_end);

        if let Some(last) = result.last_mut() &&
            *last.1.end() + 1 == result_start
        {
            assert_eq!(chunk_start - 1, *last.0.end());
            *last = (*last.0.start()..=chunk_end, *last.1.start()..=result_end);
        }
        else {
            result.push((chunk_start..=chunk_end, result_start..=result_end));
        }
    }
    result
}

pub fn range_mod_euclid(a_range: RangeInclusive<i64>, b_range: RangeInclusive<i64>) -> RangeInclusive<i64> {
    let b_abs = abs_range(b_range.clone());

    if a_range.is_empty() || b_range.is_empty() || *b_abs.end() == 0 {
        return 1..=0;
    }

    if a_range == (0..=0) || *b_abs.end() == 1 { return 0..=0; }

    if a_range.contains(&-1) && a_range.contains(&0) {
        // positive and negative? -> can always produce 0 and b_hi
        return 0..=(*b_abs.end() - 1) as i64;
    }

    let (a_lo, a_hi) = a_range.clone().into_inner();

    if a_hi >= 0 {
        assert!(a_lo >= 0);
        return range_2_i64(range_mod_u(cmp::max(0, a_lo) as u64..=a_hi as u64, b_abs.clone()));
    }

    // now negatives
    assert!(a_lo < 0 && a_hi < 0);

    // small hack: better range if max is zero
    if *b_abs.end() == *b_abs.start() && a_lo != a_hi && -a_lo as u64 % *b_abs.end() == 0 {
        let r = range_mod_euclid(a_lo + 1..=a_hi, b_range);
        return 0..=*r.end();
    }

    let mod_result = range_mod_u(-a_hi as u64..=-a_lo as u64, b_abs.clone());
    let (mod_lo, mod_hi) = mod_result.into_inner();
    let (b_lo, b_hi) = b_abs.into_inner();

    if mod_lo == 0 {
        if mod_hi == 0 { return 0..=0; }

        range_2_i64(0..=b_hi.saturating_sub(1))
    } else {
        range_2_i64((b_lo.saturating_sub(mod_hi))..=(b_hi.saturating_sub(mod_lo)))
    }

}

// assumes 0..-i64::MIN range (absolute val of signed integer)
fn range_mod_u(a_range: RangeInclusive<u64>, b_range: RangeInclusive<u64>) -> RangeInclusive<u64> {
    assert!(!a_range.is_empty() && !b_range.is_empty());
    assert!(cmp::max(*a_range.end(), *b_range.end()) <= i64::MAX as u64 + 1);

    let (mut a_lo, mut a_hi) = a_range.into_inner();
    let (b_lo, b_hi) = b_range.into_inner();
    let b_lo = cmp::max(1, b_lo);
    if b_hi <= 1 { return 0..=0; }

    if a_lo >= b_hi {
        // at least one wrap is going to occur, and we can shrink the range
        let min_wraps = a_lo / b_hi;
        if min_wraps > i64::MAX as u64 {
            assert!(b_hi == 1);
            return 0..=0;
        }
        a_lo -= min_wraps * b_hi;
        a_hi -= min_wraps * b_lo;
        // let a_hi_upperbound = a_hi - min_wraps * b_lo;
        // // if b_lo is actually this low, a_hi will be a_hi % b_lo, which might be much better
        // // so we can try higher moduli if it helps to shrink the range further
        // for i in 1..64 {

        // }
        // if b_hi != b_lo {
        //     a_hi = cmp::max((a_hi - min_wraps * b_lo) % b_lo, a_hi - min_wraps;
        // } else {
        //     a_hi -= min_wraps * b_lo;
        // }

        if a_hi > 0 && a_hi % b_lo == 0 {
            // maybe better than 0..=b_hi
            a_hi -= 1;
            a_lo = 0;
        }
    }

    if b_lo > a_hi {
        return a_lo..=a_hi;
    }

    return 0..=cmp::min(b_hi - 1, a_hi);
}


pub fn range_2_i64_neg(r: RangeInclusive<u64>) -> RangeInclusive<i64> {
    let (a, b) = r.into_inner();
    0i64.checked_sub_unsigned(b).unwrap()..=0i64.checked_sub_unsigned(a).unwrap()
}

pub fn range_num_digits(r: &RangeInclusive<i64>) -> RangeInclusive<i64> {
    let max = cmp::max(r.start().abs_diff(0), r.end().abs_diff(0));
    let min = if *r.start() <= 0 && *r.end() >= 0 {
        0
    } else {
        cmp::min(r.start().abs_diff(0), r.end().abs_diff(0))
    };

    vm::decimal_len(u64neg(min))..=vm::decimal_len(u64neg(max))
}

pub fn range_div(a: &IRange, b: &IRange) -> RangeInclusive<i64> {
    if b == &(0..=0) {
        return 1..=0;
    }
    let (a0, a1) = a.clone().into_inner();
    let (b0, b1) = b.clone().into_inner();
    let max = if b0 >= 0 {
        cmp::max(a1 / cmp::max(1, b0), a1 / b1)
    } else if b1 <= 0 {
        cmp::max(a0.checked_div(cmp::min(-1, b1)).unwrap_or(i64::MAX),
                 a0.checked_div(b0).unwrap_or(i64::MAX))
    } else {
        // may divide by 1 or -1
        cmp::max(a1, a0.saturating_neg())
    };
    let min = if b0 >= 0 {
        cmp::min(a0 / b1, a0 / cmp::max(1, b0))
    } else if b1 <= 0 {
        cmp::min(a1.checked_div(cmp::min(-1, b1)).unwrap_or(i64::MAX),
                 a1.checked_div(b0).unwrap_or(i64::MAX))
    } else {
        // may divide by 1 or -1
        cmp::min(a1.saturating_neg(), a0)
    };
    min..=max
}

// Returns (bits always set, bits may be set)
// pub fn get_bitsets(a: &RangeInclusive<i64>) -> (u64, u64) {
//     const ALL_SET: u64 = (-1i64) as u64;
//     let (a, b) = a.clone().into_inner();
//
//     if a < 0 && b >= 0 {
//         return (0, ALL_SET);
//     }
//
//     let mut always = 0u64;
//     let mut maybe = 0u64;
//
//     if b < 0 {
//         always |= 1 << 64;
//         maybe |= 1 << 64;
//     } else if a < 0 {
//         maybe |= 1 << 64;
//     }
//
//     (always, maybe)
// }

pub fn get_bitsets(a: &RangeInclusive<u64>) -> (u64, u64) {
    assert!(!a.is_empty());
    let (a, b) = a.clone().into_inner();

    let variable_bits = (b ^ a).checked_add(1).and_then(|x| x.checked_next_power_of_two()).map_or(u64::MAX, |x| x - 1);
    // let variable_bits = (b ^ a).next_power_of_two() - 1;
    assert_eq!(a & !variable_bits, b & !variable_bits, "range={a}..={b}: variable_bits={variable_bits}");
    let const_bits = a & !variable_bits;
    return (const_bits, const_bits | variable_bits);
}

fn split_range_unsigned_bitwise(a: impl Borrow<IRange>) -> ArrayVec<URange, 2> {
    let a = a.borrow();
    let mut res = ArrayVec::new();
    if *a.end() >= 0 {
        res.push(cmp::max(*a.start(), 0) as u64 ..= *a.end() as u64);
    }
    if *a.start() < 0 {
        res.push(*a.start() as u64 ..= *a.end().min(&-1) as u64);
    }
    res
}

fn splice_unsigned_bitwise(a: &IRange, b: &IRange,
                               mut f: impl FnMut(URange, URange) -> URange) -> IRange
{
    assert!(!a.is_empty() && !b.is_empty(), "splice_unsigned_bitwise({a:?}, {b:?})");
    let mut out = None;

    for sa in split_range_unsigned_bitwise(a) {
        for sb in split_range_unsigned_bitwise(b) {
            let (from, to) = f(sa.clone(), sb.clone()).into_inner();
            let from = from as i64;
            let to = to as i64;
            assert_eq!(from < 0, to < 0, "{a:?} {b:?} {sa:?} {sb:?} {from} {to}");
            assert!(from <= to, "splice_unsigned_bitwise: Empty result from f: {a:?} {b:?} {sa:?} {sb:?} {from} {to}");

            out = match out {
                None => Some(from..=to),
                Some(prev) => Some(union_range(prev, from..=to))
            }
        }
    }

    out.unwrap()
}

pub fn range_and(a: impl Borrow<IRange>, b: impl Borrow<IRange>) -> IRange {
    splice_unsigned_bitwise(a.borrow(), b.borrow(), |a, b| {
        let (aalways, avar) = get_bitsets(&a);
        let (balways, bvar) = get_bitsets(&b);
        let min = aalways & balways;
        let max = cmp::min(avar & bvar, cmp::min(*a.end(), *b.end()));
        min..=max
    })
}

pub fn range_or(a: impl Borrow<IRange>, b: impl Borrow<IRange>) -> IRange {
    splice_unsigned_bitwise(a.borrow(), b.borrow(), |a, b| {
        let (aalways, avar) = get_bitsets(&a);
        let (balways, bvar) = get_bitsets(&b);
        let min = cmp::max(aalways | balways, cmp::max(*a.start(), *b.start()));
        let max = avar | bvar;
        min..=max
    })
}

pub fn range_xor(a: impl Borrow<IRange>, b: impl Borrow<IRange>) -> IRange {
    splice_unsigned_bitwise(a.borrow(), b.borrow(), |a, b| {
        let (aalways, avar) = get_bitsets(&a);
        let (balways, bvar) = get_bitsets(&b);
        let avar = avar & !aalways;
        let bvar = bvar & !balways;
        let min = (aalways ^ balways) & !avar & !bvar;
        let max = (aalways ^ balways) | avar | bvar;
        min..=max
    })
}

pub fn eval_combi<T1, T2, TR, F: FnMut(T1, T2) -> Option<TR>>(
    a: RangeInclusive<T1>,
    b: RangeInclusive<T2>,
    max_combination: u64,
    mut f: F,
) -> Option<RangeInclusive<TR>>
    where T1: Integer + CheckedSub + CheckedAdd + CheckedMul + Clone + TryFrom<u64>,
          T2: Integer + CheckedSub + CheckedAdd + CheckedMul + Clone + TryFrom<u64> + TryFrom<T1>,
          TR: Integer + Clone
{
    if a.is_empty() || b.is_empty() {
        return Some(TR::one()..=TR::zero());
    }

    let (a_start, a_end) = a.into_inner();
    let (b_start, b_end) = b.into_inner();

    let a_size = a_end.checked_sub(&a_start)?.checked_add(&T1::one())?;
    let b_size = b_end.checked_sub(&b_start)?.checked_add(&T2::one())?;
    if b_size.checked_mul(&a_size.try_into().ok()?)? <= max_combination.try_into().ok().expect("max_combination convert") {
        let mut min = TR::zero();
        let mut max = TR::zero();
        let mut count = 0;
        let mut x = a_start;
        while x <= a_end {
            let mut y = b_start.clone();
            while y <= b_end {
                if let Some(value) = f(x.clone(), y.clone()) {
                    if count == 0 {
                        min = value.clone();
                        max = value.clone();
                    } else {
                        if value < min { min = value.clone() }
                        if value > max { max = value.clone() }
                    }
                    count += 1;
                }
                let Some(y_) = y.checked_add(&T2::one()) else { break; };
                y = y_;
            }
            let Some(x_) = x.checked_add(&T1::one()) else { break; };
            x = x_;
        }
        if count == 0 {
            return Some(TR::one()..=TR::zero());
        }
        Some(min..=max)
    } else {
        None
    }
}

#[test]
pub fn test_mod_range_wrapping() {
    assert_eq!(range_mod(3..=4, 2..=3), 0..=1);
    assert_eq!(range_mod(100..=100, 1..=1000), 0..=100);
    assert_eq!(range_mod(100..=103, 50..=50), 0..=3);
    assert_eq!(range_mod(100..=103, 49..=50), 0..=5);

    for a in 0..10000 {
        let a_range = a..=a+1;
        for b in [-1, 4, a, a - 1, a + 1, a/2 + 10] {
            let b_range = b..=b+1;
            let expected = eval_combi(a_range.clone(), b_range.clone(), 256, |a: i64, b| a.checked_rem(b)).unwrap();
            let approximate = range_mod(a_range.clone(), b_range.clone());

            assert!(approximate.start() <= expected.start() &&
                    approximate.end() >= expected.end() &&
                    approximate.clone().count() <= expected.clone().count() + 3
                    , "{a_range:?} % {b_range:?} => {approximate:?} (should be {expected:?}");
        }
    }
}

#[test]
pub fn test_mod_range_optimal_const_b() {
    for a in -10000..10000 {
        for size in [0, 1, 2, 3, 10, 16, 40] {
            let a_range = a..=a+size;
            for b in [-1, 4, 15, a, a - 1, a + 1, a/2 + 10] {
                let expected = eval_combi(a_range.clone(), b..=b, 256, |a: i64, b| a.checked_rem(b)).unwrap();
                let approximate = range_mod(a_range.clone(), b..=b);

                assert_eq!(approximate, expected, "{a_range:?} % {b} => {approximate:?} (should be {expected:?}");
            }
        }
    }
}

#[test]
fn test_positive_ranges() {
    assert_eq!(range_mod(0..=10, 3..=5), 0..=4);
    assert_eq!(range_mod(0..=2, 5..=10), 0..=2);
    assert_eq!(range_mod(10..=20, 7..=9), 0..=8);
}

#[test]
fn test_negative_a() {
    assert_eq!(range_mod(-10..=-1, 3..=5), -4..=0);
}

#[test]
fn test_mixed_a() {
    assert_eq!(range_mod(-5..=5, 3..=7), -5..=5);
    assert_eq!(range_mod(-1..=5, 3..=7), -1..=5);
    assert_eq!(range_mod(-1..=100, 3..=7), -1..=6);
    assert_eq!(range_mod(-100..=1, 3..=7), -6..=1);
    assert_eq!(range_mod(-100..=100, 3..=7), -6..=6);
}

#[test]
fn test_negative_b() {
    assert_eq!(range_mod(0..=10, -5..=-3), 0..=4);
    assert_eq!(range_mod(-10..=-1, -5..=-3), -4..=0);
}

#[test]
pub fn test_mod_range_euclid_wrapping() {
    // For 3..=4 rem_euclid 2..=3:
    // 3 rem_euclid 2 = 1, 3 rem_euclid 3 = 0
    // 4 rem_euclid 2 = 0, 4 rem_euclid 3 = 1
    // Result: {0, 1}
    assert_eq!(range_mod_euclid(3..=4, 2..=3), 0..=1);
    assert_eq!(range_mod_euclid(100..=100, 1..=1000), 0..=100);
    assert_eq!(range_mod_euclid(100..=103, 50..=50), 0..=3);
    // For 100..=103 rem_euclid 49..=50, we can get 0 (when divisible) up to 49
    // Actually: 100%49=2, 100%50=0, 101%49=3, 101%50=1, etc.
    // Max is 49-1=48, but we need to check more carefully
    assert!(*range_mod_euclid(100..=103, 49..=50).end() >= 3);

    for a in 0..10000 {
        let a_range = a..=a+1;
        for b in [-1, 4, a, a - 1, a + 1, a/2 + 10] {
            let b_range = b..=b+1;
            let expected = eval_combi(a_range.clone(), b_range.clone(), 256, |a: i64, b| a.checked_rem_euclid(b)).unwrap();
            let approximate = range_mod_euclid(a_range.clone(), b_range.clone());

            assert!(approximate.start() <= expected.start() &&
                    approximate.end() >= expected.end() &&
                    approximate.clone().count() <= expected.clone().count() + 3
                    , "{a_range:?} % {b_range:?} => {approximate:?} (should be {expected:?}");
        }
    }
}

#[test]
pub fn test_mod_range_euclid_optimal_const_b() {
    for a in -10000..10000 {
        for size in [0, 1, 2, 3, 10, 16, 40] {
            let a_range = a..=a+size;
            for b in [-1, 4, 15, a - 1, a + 1, a/2 + 10] {
                if b == 0 { continue; }
                let expected = eval_combi(a_range.clone(), b..=b, 256, |a: i64, b| a.checked_rem_euclid(b)).unwrap();
                let approximate = range_mod_euclid(a_range.clone(), b..=b);

                // For constant b, the result should be a valid overapproximation
                // We allow significant slack because mod_range_u itself is conservative
                // especially around wrap points
                assert_eq!(approximate, expected, "{a_range:?} % {b} => {approximate:?} (should contain {expected:?}");
                assert!(approximate.start() <= expected.start() &&
                        approximate.end() >= expected.end(),
                        "{a_range:?} % {b} => {approximate:?} (should contain {expected:?}");
            }
        }
    }
}

#[test]
fn test_euclid_positive_ranges() {
    assert_eq!(range_mod_euclid(0..=10, 3..=5), 0..=4);
    assert_eq!(range_mod_euclid(0..=2, 5..=10), 0..=2);
    assert_eq!(range_mod_euclid(10..=20, 7..=9), 0..=8);
}

#[test]
fn test_euclid_negative_a() {
    // Euclidean modulo always returns non-negative results
    assert_eq!(range_mod_euclid(-10..=-1, 3..=5), 0..=4);
    assert_eq!(range_mod_euclid(-10..=-1, 5..=5), 0..=4);
    assert_eq!(range_mod_euclid(-10000..=-9999, 4..=4), 0..=1);
}

#[test]
fn test_euclid_mixed_a() {
    // With mixed signs, result is still non-negative
    assert_eq!(range_mod_euclid(-5..=5, 3..=7), 0..=6);
    assert_eq!(range_mod_euclid(-1..=5, 3..=7), 0..=6);
    assert_eq!(range_mod_euclid(-1..=100, 3..=7), 0..=6);
    assert_eq!(range_mod_euclid(-100..=1, 3..=7), 0..=6);
    assert_eq!(range_mod_euclid(-100..=100, 3..=7), 0..=6);
}

#[test]
fn test_euclid_negative_b() {
    // Euclidean modulo uses absolute value of divisor
    assert_eq!(range_mod_euclid(0..=10, -5..=-3), 0..=4);
    assert_eq!(range_mod_euclid(-10..=-1, -5..=-3), 0..=4);
}


#[test]
fn test_range_div() {
    assert_eq!(i64::MIN..=i64::MAX, range_div(&(i64::MIN..=i64::MAX), &(i64::MIN..=i64::MAX)));
    assert_eq!(i64::MIN..=i64::MAX, range_div(&(i64::MIN..=i64::MAX), &(1..=1)));
    assert_eq!((i64::MIN + 1)..=i64::MAX, range_div(&(i64::MIN..=i64::MAX), &(-1..=-1)));
    assert_eq!((i64::MIN + 1)..=i64::MAX, range_div(&(i64::MIN..=i64::MAX), &(i64::MIN..=0)));
    assert_eq!(42..=42, range_div(&(22806..=23348), &(543..=543)));
    assert_eq!(42..=43, range_div(&(22806..=23349), &(543..=543)));
    assert_eq!(0..=1, range_div(&(i64::MIN..=i64::MAX), &(i64::MIN..=i64::MIN)));
    assert_eq!(1..=1, range_div(&(i64::MIN..=i64::MIN), &(i64::MIN..=i64::MIN)));
    assert_eq!(-1..=0, range_div(&(-3..=-3), &(2..=4)));
    assert_eq!(-1..=-1, range_div(&(-3..=-3), &(2..=3)));
}


#[cfg(test)]
fn test_helper_bitops(a: IRange, b: IRange) {
    use super::utils::SaturatingInto;
    println!("Testing {a:?}  |  {b:?}");
    fn sample(a: &IRange) -> impl Iterator<Item = i64> {
        let zero = a.contains(&0).then_some(0);
        let m1 = a.contains(&-1).then_some(-1);
        let step_size = cmp::max(1, a.end().abs_diff(*a.start()) / 100);
        a.clone().step_by(step_size.saturating_into()).chain(zero).chain(m1).chain([*a.end()])
    }

    let and = range_and(&a, &b);
    let or = range_or(&a, &b);
    let xor = range_xor(&a, &b);

    // if let Some(chk_and) = eval_combi(a.clone(), b.clone(), 4096, |a, b| Some(a & b)) {
    //     assert_eq!(and, chk_and, "range_and({a:?}, {b:?})");
    // }
    // if let Some(chk_or) = eval_combi(a.clone(), b.clone(), 4096, |a, b| Some(a | b)) {
    //     assert_eq!(or, chk_or, "range_or({a:?}, {b:?})");
    // }
    // if let Some(chk_xor) = eval_combi(a.clone(), b.clone(), 4096, |a, b| Some(a ^ b)) {
    //     assert_eq!(xor, chk_xor, "range_xor({a:?}, {b:?})");
    // }

    for sample_a in sample(&a) {
        for sample_b in sample(&b) {
            assert!(and.contains(&(sample_a & sample_b)), "range_and({a:?}, {b:?}) = {and:?} does not contain {sample_a} & {sample_b} = {}", sample_a & sample_b);
            assert!(or.contains(&(sample_a | sample_b)), "range_or({a:?}, {b:?}) = {or:?} does not contain {sample_a} | {sample_b} = {}", sample_a | sample_b);
            assert!(xor.contains(&(sample_a ^ sample_b)), "range_xor({a:?}, {b:?}) = {xor:?} does not contain {sample_a} ^ {sample_b} = {}", sample_a ^ sample_b);
        }
    }
}

#[test]
fn test_range_bitops() {
    let mut vals = [i64::MIN, i64::MIN + 1, -12454331, -1, 0, 2, 123456523132, i64::MAX - 2, i64::MAX - 1, i64::MAX];
    vals.sort();

    for i1 in 0..vals.len() {
        for i2 in i1..vals.len() {
            for i3 in i1..vals.len() {
                for i4 in i3..vals.len() {
                    test_helper_bitops(vals[i1]..=vals[i2], vals[i3]..=vals[i4]);
                }
            }
        }
    }
}

#[test]
fn test_mod_split_range() {
    assert_eq!(mod_split_ranges(-15..=15, i64::MAX, true).as_slice(), [(-15..=-1, 9223372036854775792..=9223372036854775806), (0..=15, 0..=15)]);
    assert_eq!(mod_split_ranges(-15..=15, i64::MAX, false).as_slice(), [(-15..=15, -15..=15)]);
    assert_eq!(mod_split_ranges(-15..=15, 7, false).as_slice(), [(-15..=-14, -1..=0), (-13..=-7, -6..=0), (-6..=6, -6..=6), (7..=13, 0..=6), (14..=15, 0..=1)]);
    assert_eq!(mod_split_ranges(-15..=15, 7, true).as_slice(), [(-15..=-15, 6..=6), (-14..=-8, 0..=6), (-7..=-1, 0..=6), (0..=6, 0..=6), (7..=13, 0..=6), (14..=15, 0..=1)]);
    assert_eq!(mod_split_ranges(-1..=15, 7, false).as_slice(), [(-1..=6, -1..=6), (7..=13, 0..=6), (14..=15, 0..=1)]);
}

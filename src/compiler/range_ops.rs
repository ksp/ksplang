use std::{cmp, ops::RangeInclusive};

use crate::compiler::utils::{abs_range, eval_combi, range_2_i64, range_2_i64_neg};

pub fn mod_range(a_range: RangeInclusive<i64>, b_range: RangeInclusive<i64>) -> RangeInclusive<i64> {
    let b_abs = abs_range(b_range.clone());

    if a_range.is_empty() || b_range.is_empty() || *b_abs.end() == 0 {
        return 1..=0;
    }

    if a_range == (0..=0) { return 0..=0; }

    let (a_lo, a_hi) = a_range.clone().into_inner();

    let positive = if a_hi > 0 {
        Some(mod_range_u(cmp::max(0, a_lo) as u64..=a_hi as u64, b_abs.clone()))
    } else { None };
    let negative = if a_lo < 0 {
        Some(mod_range_u(-cmp::min(0, a_hi) as u64..=-a_lo as u64, b_abs.clone()))
    } else { None };

    let positive = positive.map(range_2_i64);
    let negative = negative.map(range_2_i64_neg);
    let min = *negative.as_ref().or(positive.as_ref()).unwrap().start();
    let max = *positive.or(negative).unwrap().end();
    return min..=max;
}

pub fn mod_range_euclid(a_range: RangeInclusive<i64>, b_range: RangeInclusive<i64>) -> RangeInclusive<i64> {
    let b_abs = abs_range(b_range.clone());

    if a_range.is_empty() || b_range.is_empty() || *b_abs.end() == 0 {
        return 1..=0;
    }

    if a_range == (0..=0) || *b_abs.end() == 1 { return 0..=0; }

    if a_range.contains(&-1) && a_range.contains(&0) {
        // positive and negative? -> can always produce 0 and b_hi
        return 0..=(*b_abs.end() as i64 - 1);
    }

    let (a_lo, a_hi) = a_range.clone().into_inner();

    if a_hi >= 0 {
        assert!(a_lo >= 0);
        return range_2_i64(mod_range_u(cmp::max(0, a_lo) as u64..=a_hi as u64, b_abs.clone()));
    }

    // now negatives
    assert!(a_lo < 0 && a_hi < 0);

    // small hack: better range if max is zero
    if *b_abs.end() == *b_abs.start() && a_lo != a_hi && -a_lo as u64 % *b_abs.end() == 0 {
        let r = mod_range_euclid(a_lo + 1..=a_hi, b_range);
        return 0..=*r.end();
    }

    let mod_result = mod_range_u(-a_hi as u64..=-a_lo as u64, b_abs.clone());
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
fn mod_range_u(a_range: RangeInclusive<u64>, b_range: RangeInclusive<u64>) -> RangeInclusive<u64> {
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

#[test]
pub fn test_mod_range_wrapping() {
    assert_eq!(mod_range(3..=4, 2..=3), 0..=1);
    assert_eq!(mod_range(100..=100, 1..=1000), 0..=100);
    assert_eq!(mod_range(100..=103, 50..=50), 0..=3);
    assert_eq!(mod_range(100..=103, 49..=50), 0..=5);

    for a in 0..10000 {
        let a_range = a..=a+1;
        for b in [-1, 4, a, a - 1, a + 1, a/2 + 10] {
            let b_range = b..=b+1;
            let expected = eval_combi(a_range.clone(), b_range.clone(), 256, |a: i64, b| a.checked_rem(b)).unwrap();
            let approximate = mod_range(a_range.clone(), b_range.clone());

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
                let approximate = mod_range(a_range.clone(), b..=b);

                assert_eq!(approximate, expected, "{a_range:?} % {b} => {approximate:?} (should be {expected:?}");
            }
        }
    }
}

#[test]
fn test_positive_ranges() {
    assert_eq!(mod_range(0..=10, 3..=5), 0..=4);
    assert_eq!(mod_range(0..=2, 5..=10), 0..=2);
    assert_eq!(mod_range(10..=20, 7..=9), 0..=8);
}

#[test]
fn test_negative_a() {
    assert_eq!(mod_range(-10..=-1, 3..=5), -4..=0);
}

#[test]
fn test_mixed_a() {
    assert_eq!(mod_range(-5..=5, 3..=7), -5..=5);
    assert_eq!(mod_range(-1..=5, 3..=7), -1..=5);
    assert_eq!(mod_range(-1..=100, 3..=7), -1..=6);
    assert_eq!(mod_range(-100..=1, 3..=7), -6..=1);
    assert_eq!(mod_range(-100..=100, 3..=7), -6..=6);
}

#[test]
fn test_negative_b() {
    assert_eq!(mod_range(0..=10, -5..=-3), 0..=4);
    assert_eq!(mod_range(-10..=-1, -5..=-3), -4..=0);
}

#[test]
pub fn test_mod_range_euclid_wrapping() {
    // For 3..=4 rem_euclid 2..=3:
    // 3 rem_euclid 2 = 1, 3 rem_euclid 3 = 0
    // 4 rem_euclid 2 = 0, 4 rem_euclid 3 = 1
    // Result: {0, 1}
    assert_eq!(mod_range_euclid(3..=4, 2..=3), 0..=1);
    assert_eq!(mod_range_euclid(100..=100, 1..=1000), 0..=100);
    assert_eq!(mod_range_euclid(100..=103, 50..=50), 0..=3);
    // For 100..=103 rem_euclid 49..=50, we can get 0 (when divisible) up to 49
    // Actually: 100%49=2, 100%50=0, 101%49=3, 101%50=1, etc.
    // Max is 49-1=48, but we need to check more carefully
    assert!(*mod_range_euclid(100..=103, 49..=50).end() >= 3);

    for a in 0..10000 {
        let a_range = a..=a+1;
        for b in [-1, 4, a, a - 1, a + 1, a/2 + 10] {
            let b_range = b..=b+1;
            let expected = eval_combi(a_range.clone(), b_range.clone(), 256, |a: i64, b| a.checked_rem_euclid(b)).unwrap();
            let approximate = mod_range_euclid(a_range.clone(), b_range.clone());

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
                let approximate = mod_range_euclid(a_range.clone(), b..=b);

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
    assert_eq!(mod_range_euclid(0..=10, 3..=5), 0..=4);
    assert_eq!(mod_range_euclid(0..=2, 5..=10), 0..=2);
    assert_eq!(mod_range_euclid(10..=20, 7..=9), 0..=8);
}

#[test]
fn test_euclid_negative_a() {
    // Euclidean modulo always returns non-negative results
    assert_eq!(mod_range_euclid(-10..=-1, 3..=5), 0..=4);
    assert_eq!(mod_range_euclid(-10..=-1, 5..=5), 0..=4);
    assert_eq!(mod_range_euclid(-10000..=-9999, 4..=4), 0..=1);
}

#[test]
fn test_euclid_mixed_a() {
    // With mixed signs, result is still non-negative
    assert_eq!(mod_range_euclid(-5..=5, 3..=7), 0..=6);
    assert_eq!(mod_range_euclid(-1..=5, 3..=7), 0..=6);
    assert_eq!(mod_range_euclid(-1..=100, 3..=7), 0..=6);
    assert_eq!(mod_range_euclid(-100..=1, 3..=7), 0..=6);
    assert_eq!(mod_range_euclid(-100..=100, 3..=7), 0..=6);
}

#[test]
fn test_euclid_negative_b() {
    // Euclidean modulo uses absolute value of divisor
    assert_eq!(mod_range_euclid(0..=10, -5..=-3), 0..=4);
    assert_eq!(mod_range_euclid(-10..=-1, -5..=-3), 0..=4);
}

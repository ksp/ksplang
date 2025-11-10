use std::{cmp::{self, min}, collections::HashSet, fmt::Debug, ops::RangeInclusive};

use num_integer::Integer;
use num_traits::{Bounded, CheckedMul, One, SaturatingAdd, SaturatingMul, SaturatingSub, Zero};

pub const EMPTY_RANGE: RangeInclusive<i64> = 1..=0;
pub const FULL_RANGE: RangeInclusive<i64> = i64::MIN..=i64::MAX;


pub fn most_set_bits_in_range(from: u64, to: u64) -> u64 {
    let difference = from ^ to;
    let highest_diff_bit = 63 - difference.leading_zeros();

    todo!()// TODO
}

pub fn range_size(r: &RangeInclusive<i64>) -> u128 {
    if r.is_empty() {
        0
    } else {
        r.end().abs_diff(*r.start()) as u128 + 1
    }
}

pub fn u64neg(a: u64) -> i64 {
    (a as i64).wrapping_neg()
}

pub fn abs_range(r: RangeInclusive<i64>) -> RangeInclusive<u64> {
    let (a, b) = r.into_inner();
    if (a >= 0) == (b >= 0) {
        let (a, b) = sort_tuple(a.abs_diff(0), b.abs_diff(0));
        a..=b
    } else {
        0..=cmp::max(a.abs_diff(0), b.abs_diff(0))
    }
}

#[inline]
pub fn add_range(a: &RangeInclusive<i64>, b: &RangeInclusive<i64>) -> RangeInclusive<i64> {
    let start = a.start().saturating_add(b.start());
    let end = a.end().saturating_add(b.end());
    start..=end
}

#[inline]
pub fn sub_range(a: &RangeInclusive<i64>, b: &RangeInclusive<i64>) -> RangeInclusive<i64> {
    let start = a.start().saturating_sub(b.end());
    let end = a.end().saturating_sub(b.start());
    start..=end
}

/// Returns true if the range does not include both negative and positive numbers
#[inline]
pub fn range_is_signless(r: &RangeInclusive<i64>) -> bool {
    *r.start() >= 0 || *r.end() <= 0
}

#[inline]
pub fn range_sign(r: &RangeInclusive<i64>) -> i64 {
    if *r.start() >= 0 {
        1
    } else if *r.end() <= 0 {
        -1
    } else {
        0
    }
}

pub fn mul_range(a: &RangeInclusive<i64>, b: &RangeInclusive<i64>) -> (RangeInclusive<i64>, bool) {
    let candidates = [
        a.start().saturating_mul(b.start()),
        a.start().saturating_mul(b.end()),
        a.end().saturating_mul(b.start()),
        a.end().saturating_mul(b.end()),
    ];
    let may_overflow = a.start().checked_mul(b.start()).is_none() ||
                             a.start().checked_mul(b.end()).is_none() ||
                             a.end().checked_mul(b.start()).is_none() ||
                             a.end().checked_mul(b.end()).is_none();
    let min = *candidates.iter().min().unwrap();
    let max = *candidates.iter().max().unwrap();
    (min..=max, may_overflow)
}

pub fn union_range(a: RangeInclusive<i64>, b: RangeInclusive<i64>) -> RangeInclusive<i64> {
    let start = cmp::min(*a.start(), *b.start());
    let end = cmp::max(*a.end(), *b.end());
    start..=end
}

pub fn intersect_range<T: Ord + Zero + One + Clone>(a: &RangeInclusive<T>, b: &RangeInclusive<T>) -> RangeInclusive<T> {
    let start = cmp::max(a.start(), b.start()).clone();
    let end = cmp::min(a.end(), b.end()).clone();
    if start > end {
        T::one()..=T::zero()
    } else {
        start..=end
    }
}

pub fn range_2_i64(r: RangeInclusive<u64>) -> RangeInclusive<i64> {
    let (a, b) = r.into_inner();
    if a > i64::MAX as u64 {
        1..=0
    } else if b > i64::MAX as u64 {
        a as i64..=i64::MAX
    } else {
        a as i64..=b as i64
    }
}

pub fn sort_tuple<T: Ord>(a: T, b: T) -> (T, T) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

pub fn eval_combi_u64<F: Fn(u64, u64) -> Option<u64>>(
    a: RangeInclusive<u64>,
    b: RangeInclusive<u64>,
    max_combination: u64,
    f: F,
) -> Option<RangeInclusive<u64>> {
    if a.is_empty() || b.is_empty() {
        return Some(1..=0);
    }

    let size_a = a.end().abs_diff(*a.start()).saturating_add(1);
    let size_b = b.end().abs_diff(*b.start()).saturating_add(1);
    if size_a.saturating_mul(size_b) <= max_combination {
        let mut values = HashSet::new();
        for x in a.clone() {
            for y in b.clone() {
                if let Some(value) = f(x, y) {
                    values.insert(value);
                }
            }
        }
        if values.is_empty() {
            return Some(1..=0);
        }
        let min = *values.iter().min().unwrap();
        let max = *values.iter().max().unwrap();
        Some(min..=max)
    } else {
        None
    }
}



pub trait SaturatingInto<T> {
    fn saturating_into(self) -> T;
}

impl <T, U> SaturatingInto<U> for T
where T: Clone + TryFrom<U> + Ord,
      U: TryFrom<T> + Bounded + Clone
{
    fn saturating_into(self) -> U {
        if let Some(min) = T::try_from(U::min_value()).ok() {
            if self < min {
                return U::min_value();
            }
        }
        if let Some(max) = T::try_from(U::max_value()).ok() {
            if self > max {
                return U::max_value();
            }
        }
        let Ok(result) = self.try_into() else {
            unreachable!("saturating_into: conversion failed unexpectedly")
        };
        result
    }
}

pub trait AssertInto<T> {
    fn assert_into(self) -> T;
}
impl <T, U> AssertInto<U> for T
where U: TryFrom<T>,
      T: Clone + Debug
{
    #[inline]
    fn assert_into(self) -> U {
        #[cfg(debug_assertions)]
        let Ok(result) = self.clone().try_into() else {
            panic!("assert_into: conversion {} -> {} failed unexpectedly: {:?}", std::any::type_name::<T>(), std::any::type_name::<U>(), self);
        };
        #[cfg(not(debug_assertions))]
        let Ok(result) = self.try_into() else { unreachable!() };
        result
    }
}

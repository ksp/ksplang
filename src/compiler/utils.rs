use std::{cmp, collections::HashSet, ops::RangeInclusive};



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
        a.abs_diff(0)..=b.abs_diff(0)
    } else {
        0..=cmp::max(a.abs_diff(0), b.abs_diff(0))
    }
}

pub fn sort_tuple<T: Ord>(a: T, b: T) -> (T, T) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

pub fn median(vals: &mut [i64]) -> i64 {
    vals.sort();
    if vals.len() % 2 == 1 {
        vals[vals.len() / 2]
    } else {
        let a = vals[vals.len() / 2 - 1];
        let b = vals[vals.len() / 2];
        ((a as i128 + b as i128) / 2) as i64
    }
}


pub fn eval_combi<F: Fn(i64, i64) -> Option<i64>>(
    a: RangeInclusive<i64>,
    b: RangeInclusive<i64>,
    max_combination: u64,
    f: F,
) -> Option<RangeInclusive<i64>> {
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


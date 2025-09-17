use std::collections::HashMap;
use std::cmp::max;

use crate::vm::OperationError;

const MOD: u64 = 1_000_000_007; // must be prime

#[inline]
pub fn funkcia(a: i64, b: i64) -> u64 {
    if a == b || (a <= 1 && b <= 1) {
        return 0;
    }
    if a <= 1 || b <= 1 {
        return (max(a, b) as u64) % MOD;
    }

    let mut a = a as u64;
    let mut b = b as u64;

    // Odoberie 2 čísla zo zásobníka a obe rozloží na prvočísla. Následne z rozkladov zmaže všetky prvočísla, ktoré delia obe dve čísla.
    // Výsledkom je súčin všetkých ostatných prvočísel vrátane exponentov, modulo 1 000 000 007. Pokiaľ je množina prvočísel prázdna, výsledkom je nula.
    
    // Faster approach:
    // * get common set of primes in the form of gcd(a, b)
    //   - we don't have the primes individually, so we must work with that
    //   - we special case 2, it makes the numbers smaller and we get rid of special case checks in the modulo-less GCD


    // extract exponent of 2 and get rid of all factors of 2 (i.e. trailing zeros in binary)
    let prime_2_exp = extract_unique_prime2(a, b);
    a = a >> a.trailing_zeros();
    b = b >> b.trailing_zeros();
    debug_assert!(a % 2 == 1 && b % 2 == 1);

    // find the common factors of a, b
    let g = gcd_nodiv(a, b);
    debug_assert!(g % 2 == 1);

    if g > 1 {
        debug_assert!(a % g == 0);
        debug_assert!(b % g == 0);
        // remove common factors with exponent 1
        a = a / g;
        b = b / g;
        debug_assert!(a % 2 == 1 && b % 2 == 1);

        // if factor in a has higher exponent than in b, we need to divide a again by that factor
        // so we find the remaining common prime factors in a, and divide them out
        loop {
            let a_rem = gcd_nodiv(a, g); // get remaining prime factors of a
            if a_rem == 1 {
                break;
            }
            debug_assert!(a % a_rem == 0);
            a /= a_rem;
        }
        // and the same for b
        loop {
            let b_rem = gcd_nodiv(b, g); // get remaining prime factors of b
            if b_rem == 1 {
                break;
            }
            debug_assert!(b % b_rem == 0);
            b /= b_rem;
        }
    }

    debug_assert!(gcd(a, b) == 1);
    if a == b && prime_2_exp == 0 {
        return 0; // Pokiaľ je množina prvočísel prázdna, výsledkom je nula
    }

    // Result is simply (a * b * 2^prime_2_exp) % MOD
    // We just need to be careful about i64 overflow (and minimizing number of modulos)
    if let Some(result) = a.checked_mul(b) {
        if result < MOD >> prime_2_exp {
            // no overflow
            debug_assert!(result.checked_mul(1 << prime_2_exp).unwrap() < MOD);
            result << prime_2_exp
        } else if prime_2_exp < 30 {
            debug_assert!((result % MOD).checked_mul(1 << prime_2_exp).is_some());
            ((result % MOD) << prime_2_exp) % MOD
        } else {
            (result % MOD).checked_mul((1 << prime_2_exp) % MOD).unwrap() % MOD
        }
    } else {
        let a2 = a % MOD;
        let b2 = b % MOD;
        debug_assert!(a2.checked_mul(b2).is_some());
        (((a2 * b2) % MOD) * ((1 << prime_2_exp) % MOD)) % MOD
    }

}

/// Exponent of the prime 2 in the factorization setdiff of a, b
fn extract_unique_prime2(a: u64, b: u64) -> u32 {
    // there is a reason why we have 4x more lines in test code than this implementation ...
    let a_ = a ^ (a - 1); // -> blsmsk instruction - mask of trailing zeros including the first one
    let b_ = b ^ (b - 1);
    let mask = (a_ ^ b_) >> 1;
    mask.trailing_ones()
}

/// Binary GCD algorithm: https://en.wikipedia.org/wiki/Binary_GCD_algorithm
/// Assumes a and b are odd and positive, as these conditions are already handled by funkcia
#[inline]
fn gcd_nodiv(mut a: u64, mut b: u64) -> u64 {
    debug_assert!(a % 2 == 1 && b % 2 == 1 && a > 0 && b > 0, "a = {a}, b = {b}");
    let a_orig = a;
    let b_orig = b;

    loop {
        b >>= b.trailing_zeros();
        if a > b {
            let temp = a;
            a = b;
            b = temp;
        }

        b -= a;

        if b == 0 { break; }
    }

    debug_assert_eq!(a, gcd(a_orig, b_orig), "a_orig = {a_orig}, b_orig = {b_orig}");

    a
}

/// Classic euclidean algorithm
#[inline]
fn gcd(mut a: u64, mut b: u64) -> u64 {
    debug_assert!(a > 0 && b > 0, "a = {a}, b = {b}");
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// slow reference implementation
pub fn funkcia_reference(a: i64, b: i64) -> Result<i64, OperationError> {
    if a == b || (a < 2 && b < 2) {
        return Ok(0);
    }
    fn factorize(mut a: i64) -> HashMap<i64, usize> {
        let mut counts_by_divisor = HashMap::new();
        let mut i = 2;
        while (i * i) as i128 <= a as i128 {
            while a % i == 0 {
                counts_by_divisor.entry(i).and_modify(|x| *x += 1).or_insert(1);
                a /= i;
            }

            i += 1;
        }
        if a > 1 {
            counts_by_divisor.entry(a).and_modify(|x| *x += 1).or_insert(1);
        }
        counts_by_divisor
    }

    let a_factors = factorize(a);
    let b_factors = factorize(b);

    let mut result = 1i64;
    let mut is_empty = true;
    let mut apply_factors = |factors: &HashMap<i64, usize>,
                                the_other_factors: &HashMap<i64, usize>|
        -> Result<(), OperationError> {
        for (factor, count) in factors {
            if the_other_factors.contains_key(&factor) {
                continue;
            }
            is_empty = false;
            for _ in 0..*count {
                result = (result
                    .checked_mul(factor % (MOD as i64))
                    .ok_or(OperationError::IntegerOverflow)?
                    % (MOD as i64))
                    % (MOD as i64);
            }
        }
        Ok(())
    };

    apply_factors(&a_factors, &b_factors)?;
    apply_factors(&b_factors, &a_factors)?;

    if is_empty {
        result = 0
    };
    Ok(result)
}

#[test]
fn extract_unique_prime2_test() {
    let m = i64::MAX as u64;
    let odd_values = [3, 5, 7, 9, 101, 1001, 10001, 100001, 100000001, 1000000000001, 12345676543, m, m - 2, m - 4, m - 6, m - 8];
    for &a in &odd_values {
        for &b in &odd_values {
            assert_eq!(extract_unique_prime2(a, b), 0, "a = {a}, b = {b}");
            assert_eq!(extract_unique_prime2(a, b - 1), (b - 1).trailing_zeros(), "a = {a}, b = {b}");
            assert_eq!(extract_unique_prime2(a - 1, b - 1), 0, "a = {a}, b = {b}");

            for pow2 in 1..60 {
                if let Some(a_even) = a.checked_mul(1u64 << pow2) {
                    assert_eq!(extract_unique_prime2(a_even, b), pow2, "a = {a}, b = {b}, pow2 = {pow2}");
                    assert_eq!(extract_unique_prime2(a_even, b - 1), 0, "a = {a}, b = {b}, pow2 = {pow2}");
                }
            }
        }
    }
}

#[test]
fn funcia_reference_debuggable_test() {
    let a = 3;
    let b = 90000;
    let result = funkcia(a, b);
    let expected = funkcia_reference(a, b).unwrap();
    assert!(result <= i64::MAX as u64);
    assert_eq!(result as i64, expected);
}

#[test]
fn funcia_reference_test() {
    let values = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32, 24, 614889782588491410, 307444891294245705, 204963260862830470, 1000, 1001, 1000_000_007, 1000_000_006, 1000_000_008, 1000_000_009, 125000001, 500000004, 1000_000_000_007, 1000_000_000_000_007, 1000_000_000_000_000_007, i64::MAX, 1 << 62, 1 << 61, 1 << 61 + 1, 3 << 62, 5 << 62, 7 << 61, i32::MAX as i64];
    for &a in &values {
        for &b in &values {
            let result = funkcia(a, b);
            let expected = funkcia_reference(a, b).unwrap();
            assert!(result <= i64::MAX as u64);

            assert_eq!(result as i64, expected, "a = {a}, b = {b}");
        }
    }
}


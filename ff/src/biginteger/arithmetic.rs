use crate::BitIteratorBE;
use ark_std::{vec, vec::Vec};

/// Calculate a + b + carry, returning the sum and modifying the
/// carry value.
macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);

        $carry = (tmp >> 64) as u64;

        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);

        $carry = (tmp >> 64) as u64;

        tmp as u64
    }};
}

/// Calculate a - b - borrow, returning the result and modifying
/// the borrow value.
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);

        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };

        tmp as u64
    }};
}

#[inline(always)]
pub(crate) fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

#[inline(always)]
pub(crate) fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;
}

pub fn find_wnaf(num: &[u64]) -> Vec<i64> {
    let is_zero = |num: &[u64]| num.iter().all(|x| *x == 0u64);
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    let sub_noborrow = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut borrow = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = sbb!(*a, b, &mut borrow);
        }
    };
    let add_nocarry = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut carry = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = adc!(*a, b, &mut carry);
        }
    };
    let div2 = |num: &mut [u64]| {
        let mut t = 0;
        for i in num.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    };

    let mut num = num.to_vec();
    let mut res = vec![];

    while !is_zero(&num) {
        let z: i64;
        if is_odd(&num) {
            z = 2 - (num[0] % 4) as i64;
            if z >= 0 {
                sub_noborrow(&mut num, z as u64)
            } else {
                add_nocarry(&mut num, (-z) as u64)
            }
        } else {
            z = 0;
        }
        res.push(z);
        div2(&mut num);
    }

    res
}

/// Compute the relaxed NAF of the number, where the top 2 bits can be both non-zero.
pub fn find_relaxed_naf(num: &[u64]) -> Vec<i64> {
    use num_traits::abs;

    // first, find the standard NAF representation
    let naf = find_wnaf(&num);
    let naf_cost = naf.iter().map(|g| abs(*g)).sum::<i64>() + (naf.len() as i64);

    // then, consider the modified NAF representation

    // obtain the bits of the num
    let mut bits = BitIteratorBE::new(num).collect::<Vec<_>>();

    // clear the first true bit
    let mut size = 0;
    for (i, bit) in bits.iter_mut().enumerate() {
        if *bit == true {
            *bit = false;
            size = bits.len() - i;
            break;
        }
    }

    // if naf has the optimal size, then return directly
    if naf.len() == size {
        return naf;
    }

    // reassemble the number
    let tmp = {
        let mut res = vec![0u64; num.len()];
        let mut acc: u64 = 0;
        let mut bits = bits.to_vec();
        bits.reverse();
        for (i, bits64) in bits.chunks(64).enumerate() {
            for bit in bits64.iter().rev() {
                acc <<= 1;
                acc += *bit as u64;
            }
            res[i] = acc;
            acc = 0;
        }
        res
    };

    let mut modified_naf = find_wnaf(&tmp);

    // if `modified_naf` has length `size`, then it cannot be better then the `naf`
    if modified_naf.len() <= size - 1 {
        // restructure the modified NAF
        modified_naf.resize(size - 1, 0);
        modified_naf.push(1);

        // compute the
        let modified_naf_cost =
            modified_naf.iter().map(|g| abs(*g)).sum::<i64>() + (modified_naf.len() as i64);

        if naf_cost <= modified_naf_cost {
            naf
        } else {
            modified_naf
        }
    } else {
        naf
    }
}

#[test]
fn test_find_naf_correctness() {
    use ark_std::{One, UniformRand, Zero};
    use num_bigint::BigInt;

    let mut rng = ark_std::test_rng();

    for _ in 0..10 {
        let num = [
            u64::rand(&mut rng),
            u64::rand(&mut rng),
            u64::rand(&mut rng),
            u64::rand(&mut rng),
        ];
        let relaxed_naf = find_relaxed_naf(&num);

        let test = {
            let mut sum = BigInt::zero();
            let mut cur = BigInt::one();
            for v in relaxed_naf {
                sum += cur.clone() * v;
                cur = cur * 2;
            }
            sum
        };

        let test_expected = {
            let mut sum = BigInt::zero();
            let mut cur = BigInt::one();
            for v in num.iter() {
                sum += cur.clone() * v;
                cur = cur << 64;
            }
            sum
        };

        assert_eq!(test, test_expected);
    }
}

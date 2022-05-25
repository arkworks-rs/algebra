use ark_std::{vec, vec::Vec};

macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Calculate a + b + carry, returning the sum and modifying the
/// carry value.
#[inline(always)]
pub(crate) fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
    adc!(a, b, &mut *carry)
}

macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
#[inline(always)]
pub(crate) fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    mac_with_carry!(a, b, c, &mut *carry)
}

#[macro_export]
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
        tmp as u64
    }};
}

/// Calculate a - b - borrow, returning the result and modifying
/// the borrow value.
#[inline(always)]
pub(crate) fn sbb(a: u64, b: u64, borrow: &mut u64) -> u64 {
    sbb!(a, b, &mut *borrow)
}

/// Calculate a + b * c, returning the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
pub(crate) fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

/// Calculate a + b * c, discarding the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
pub(crate) fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;
}

/// Compute the NAF (non-adjacent form) of num
pub fn find_naf(num: &[u64]) -> Vec<i64> {
    let is_zero = |num: &[u64]| num.iter().all(|x| *x == 0u64);
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    let sub_noborrow = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut borrow = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = sbb(*a, b, &mut borrow);
        }
    };
    let add_nocarry = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut carry = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = adc(*a, b, &mut carry);
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

/// We define relaxed NAF as a variant of NAF with a very small tweak.
///
/// Note that the cost of scalar multiplication grows with the length of the sequence (for doubling)
/// plus the Hamming weight of the sequence (for addition, or subtraction).
///
/// NAF is optimizing for the Hamming weight only and therefore can be suboptimal.
/// For example, NAF may generate a sequence (in little-endian) of the form ...0 -1 0 1.
///
/// This can be rewritten as ...0 1 1 to avoid one doubling, at the cost that we are making an
/// exception of non-adjacence for the most significant bit.
///
/// Since this representation is no longer a strict NAF, we call it ``relaxed NAF''.
///
pub fn find_relaxed_naf(num: &[u64]) -> Vec<i64> {
    let mut res = find_naf(num);

    let len = res.len();
    if res[len - 2] == 0 && res[len - 3] == -1 {
        res[len - 3] = 1;
        res[len - 2] = 1;
        res.resize(len - 1, 0);
    }

    res
}

#[test]
fn test_find_relaxed_naf_usefulness() {
    let vec = find_naf(&[12u64]);
    assert_eq!(vec.len(), 5);

    let vec = find_relaxed_naf(&[12u64]);
    assert_eq!(vec.len(), 4);
}

#[test]
fn test_find_relaxed_naf_correctness() {
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

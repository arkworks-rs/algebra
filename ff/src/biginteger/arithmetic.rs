use ark_std::{vec, vec::*};

macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Sets a = a + b + carry, and returns the new carry.
#[inline(always)]
#[allow(unused_mut)]
#[doc(hidden)]
pub fn adc(a: &mut u64, b: u64, carry: u64) -> u64 {
    let tmp = *a as u128 + b as u128 + carry as u128;
    *a = tmp as u64;
    (tmp >> 64) as u64
}

/// Sets a = a + b + carry, and returns the new carry.
#[inline(always)]
#[allow(unused_mut)]
#[doc(hidden)]
pub fn adc_for_add_with_carry(a: &mut u64, b: u64, carry: u8) -> u8 {
    #[cfg(all(target_arch = "x86_64", feature = "asm"))]
    #[allow(unsafe_code)]
    unsafe {
        use core::arch::x86_64::_addcarry_u64;
        _addcarry_u64(carry, *a, b, a)
    }
    #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
    {
        let tmp = *a as u128 + b as u128 + carry as u128;
        *a = tmp as u64;
        (tmp >> 64) as u8
    }
}

/// Calculate a + b + carry, returning the sum
#[inline(always)]
#[doc(hidden)]
pub fn adc_no_carry(a: u64, b: u64, carry: &u64) -> u64 {
    let tmp = a as u128 + b as u128 + *carry as u128;
    tmp as u64
}

#[macro_export]
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
        tmp as u64
    }};
}

/// Sets a = a - b - borrow, and returns the borrow.
#[inline(always)]
#[allow(unused_mut)]
pub(crate) fn sbb(a: &mut u64, b: u64, borrow: u64) -> u64 {
    let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
    *a = tmp as u64;
    (tmp >> 64 == 0) as u64
}

/// Sets a = a - b - borrow, and returns the borrow.
#[inline(always)]
#[allow(unused_mut)]
#[doc(hidden)]
pub fn sbb_for_sub_with_borrow(a: &mut u64, b: u64, borrow: u8) -> u8 {
    #[cfg(all(target_arch = "x86_64", feature = "asm"))]
    #[allow(unsafe_code)]
    unsafe {
        use core::arch::x86_64::_subborrow_u64;
        _subborrow_u64(borrow, *a, b, a)
    }
    #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
    {
        let tmp = (1u128 << 64) + (*a as u128) - (b as u128) - (borrow as u128);
        *a = tmp as u64;
        u8::from(tmp >> 64 == 0)
    }
}

#[inline(always)]
#[doc(hidden)]
pub const fn widening_mul(a: u64, b: u64) -> u128 {
    #[cfg(not(target_family = "wasm"))]
    {
        a as u128 * b as u128
    }
    #[cfg(target_family = "wasm")]
    {
        let a_lo = a as u32 as u64;
        let a_hi = a >> 32;
        let b_lo = b as u32 as u64;
        let b_hi = b >> 32;

        let lolo = (a_lo * b_lo) as u128;
        let lohi = ((a_lo * b_hi) as u128) << 32;
        let hilo = ((a_hi * b_lo) as u128) << 32;
        let hihi = ((a_hi * b_hi) as u128) << 64;
        (lolo | hihi) + (lohi + hilo)
    }
}

/// Calculate a + b * c, returning the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
#[doc(hidden)]
pub fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + widening_mul(b, c);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

/// Calculate a + b * c, discarding the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
#[doc(hidden)]
pub fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (a as u128) + widening_mul(b, c);
    *carry = (tmp >> 64) as u64;
}

macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp =
            ($a as u128) + $crate::biginteger::arithmetic::widening_mul($b, $c) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

macro_rules! mac {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + $crate::biginteger::arithmetic::widening_mul($b, $c);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
#[inline(always)]
#[doc(hidden)]
pub fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + widening_mul(b, c) + (*carry as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

/// Compute the NAF (non-adjacent form) of num
pub fn find_naf(num: &[u64]) -> Vec<i8> {
    let mut num = num.to_vec();
    let mut res = vec![];

    // Helper functions for arithmetic operations
    // Check if the number is non-zero
    let is_non_zero = |num: &[u64]| num.iter().any(|&x| x != 0);
    // Check if the number is odd
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    // Subtract a value `z` without borrow propagation
    let sub_noborrow = |num: &mut [u64], z: u64| {
        num.iter_mut()
            .zip(ark_std::iter::once(z).chain(ark_std::iter::repeat(0)))
            .fold(0, |borrow, (a, b)| sbb(a, b, borrow));
    };
    // Add a value `z` without carry propagation
    let add_nocarry = |num: &mut [u64], z: u64| {
        num.iter_mut()
            .zip(ark_std::iter::once(z).chain(ark_std::iter::repeat(0)))
            .fold(0, |carry, (a, b)| adc(a, b, carry));
    };
    // Perform an in-place division of the number by 2
    let div2 = |num: &mut [u64]| {
        num.iter_mut().rev().fold(0, |carry, x| {
            let next_carry = *x << 63;
            *x = (*x >> 1) | carry;
            next_carry
        });
    };

    // Main loop for NAF computation
    while is_non_zero(&num) {
        // Determine the current digit of the NAF representation
        let z = if is_odd(&num) {
            let z = 2 - (num[0] % 4) as i8;
            if z >= 0 {
                sub_noborrow(&mut num, z as u64);
            } else {
                add_nocarry(&mut num, (-z) as u64);
            }
            z
        } else {
            0
        };

        // Append the digit to the result
        res.push(z);
        // Divide the number by 2 for the next iteration
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
/// Since this representation is no longer a strict NAF, we call it "relaxed NAF".
pub fn find_relaxed_naf(num: &[u64]) -> Vec<i8> {
    let mut res = find_naf(num);

    let len = res.len();
    if res[len - 2] == 0 && res[len - 3] == -1 {
        res[len - 3] = 1;
        res[len - 2] = 1;
        res.resize(len - 1, 0);
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adc() {
        // Test addition without initial carry
        let mut a = 5u64;
        let carry = adc(&mut a, 10u64, 0);
        assert_eq!(a, 15); // 5 + 10 = 15
        assert_eq!(carry, 0); // No carry should be generated

        // Test addition with carry when overflowing u64
        let mut a = u64::MAX;
        let carry = adc(&mut a, 1u64, 0);
        assert_eq!(a, 0); // Overflow resets `a` to 0
        assert_eq!(carry, 1); // Carry is 1 due to overflow

        // Test addition with a non-zero initial carry
        let mut a = 5u64;
        let carry = adc(&mut a, 10u64, 1);
        assert_eq!(a, 16); // 5 + 10 + 1 = 16
        assert_eq!(carry, 0); // No overflow, so carry remains 0

        // Test addition with carry and a large sum
        let mut a = u64::MAX - 5;
        let carry = adc(&mut a, 10u64, 1);
        assert_eq!(a, 5); // (u64::MAX - 5 + 10 + 1) wraps around to 5
        assert_eq!(carry, 1); // Carry is 1 due to overflow
    }

    #[test]
    fn test_adc_for_add_with_carry() {
        // Test addition without initial carry
        let mut a = 5u64;
        let carry = adc_for_add_with_carry(&mut a, 10u64, 0);
        assert_eq!(a, 15); // Expect a to be 15
        assert_eq!(carry, 0); // No carry should be generated

        // Test addition with carry when overflowing u64
        let mut a = u64::MAX;
        let carry = adc_for_add_with_carry(&mut a, 1u64, 0);
        assert_eq!(a, 0); // Overflow resets `a` to 0
        assert_eq!(carry, 1); // Carry is 1 due to overflow

        // Test addition with a non-zero initial carry
        let mut a = 5u64;
        let carry = adc_for_add_with_carry(&mut a, 10u64, 1);
        assert_eq!(a, 16); // 5 + 10 + 1 = 16
        assert_eq!(carry, 0); // No overflow, so carry remains 0

        // Test addition with carry and a large sum
        let mut a = u64::MAX - 5;
        let carry = adc_for_add_with_carry(&mut a, 10u64, 1);
        assert_eq!(a, 5); // (u64::MAX - 5 + 10 + 1) wraps around to 5
        assert_eq!(carry, 1); // Carry is 1 due to overflow
    }

    #[test]
    fn test_adc_no_carry() {
        // Test addition without initial carry
        let carry = 0;
        let result = adc_no_carry(5u64, 10u64, &carry);
        assert_eq!(result, 15); // 5 + 10 = 15
        assert_eq!(carry, 0); // No carry should be generated

        // Test addition with a non-zero initial carry
        let carry = 1;
        let result = adc_no_carry(5u64, 10u64, &carry);
        assert_eq!(result, 16); // 5 + 10 + 1 = 16
        assert_eq!(carry, 1); // No overflow, so carry remains 1

        // Test addition that causes a carry
        let carry = 1;
        let result = adc_no_carry(u64::MAX, 1u64, &carry);
        assert_eq!(result, 1); // u64::MAX + 1 + 1 -> 1
        assert_eq!(carry, 1); // Carry is 1 due to overflow
    }

    #[test]
    fn test_sbb() {
        // Test subtraction without initial borrow
        let mut a = 15u64;
        let borrow = sbb(&mut a, 5u64, 0);
        assert_eq!(a, 10); // 15 - 5 = 10
        assert_eq!(borrow, 0); // No borrow should be generated

        // Test subtraction that causes a borrow
        let mut a = 5u64;
        let borrow = sbb(&mut a, 10u64, 0);
        assert_eq!(a, u64::MAX - 4); // Underflow, wrapping around
        assert_eq!(borrow, 1); // Borrow should be 1

        // Test subtraction with a non-zero initial borrow
        let mut a = 15u64;
        let borrow = sbb(&mut a, 5u64, 1);
        assert_eq!(a, 9); // 15 - 5 - 1 = 9
        assert_eq!(borrow, 0); // No borrow should be generated

        // Test subtraction with borrow and a large value
        let mut a = 0u64;
        let borrow = sbb(&mut a, u64::MAX, 1);
        assert_eq!(a, 0); // 0 - (u64::MAX + 1) -> 0
        assert_eq!(borrow, 1); // Borrow should be 1
    }

    #[test]
    fn test_sbb_for_sub_with_borrow() {
        // Test subtraction without initial borrow
        let mut a = 15u64;
        let borrow = sbb_for_sub_with_borrow(&mut a, 5u64, 0);
        assert_eq!(a, 10); // Expect a to be 10
        assert_eq!(borrow, 0); // No borrow should be generated

        // Test subtraction that causes a borrow
        let mut a = 5u64;
        let borrow = sbb_for_sub_with_borrow(&mut a, 10u64, 0);
        assert_eq!(a, u64::MAX - 4); // Underflow, wrapping around
        assert_eq!(borrow, 1); // Borrow should be 1

        // Test subtraction with a non-zero initial borrow
        let mut a = 15u64;
        let borrow = sbb_for_sub_with_borrow(&mut a, 5u64, 1);
        assert_eq!(a, 9); // 15 - 5 - 1 = 9
        assert_eq!(borrow, 0); // No borrow should be generated

        // Test subtraction with borrow and a large value
        let mut a = 0u64;
        let borrow = sbb_for_sub_with_borrow(&mut a, u64::MAX, 1);
        assert_eq!(a, 0); // 0 - (u64::MAX + 1) -> 0
        assert_eq!(borrow, 1); // Borrow should be 1
    }

    #[test]
    fn test_mac() {
        // Basic multiply-accumulate without carry
        let mut carry = 0;
        let result = mac(1u64, 2u64, 3u64, &mut carry);
        assert_eq!(result, 7); // 1 + (2 * 3) = 7
        assert_eq!(carry, 0); // No overflow, carry remains 0

        // Multiply-accumulate with large values that generate a carry
        let mut carry = 0;
        let result = mac(u64::MAX, u64::MAX, 1u64, &mut carry);
        assert_eq!(result, u64::MAX - 1); // Result wraps around
        assert_eq!(carry, 1); // Carry is set due to overflow
    }

    #[test]
    fn test_mac_discard() {
        // Discard lower 64 bits and set carry
        let mut carry = 0;
        mac_discard(1u64, 2u64, 3u64, &mut carry);
        assert_eq!(carry, 0); // No overflow, carry remains 0

        // Test with values that generate a carry
        let mut carry = 0;
        mac_discard(u64::MAX, u64::MAX, 1u64, &mut carry);
        assert_eq!(carry, 1); // Carry is set due to overflow
    }

    #[test]
    fn test_mac_with_carry() {
        // Basic multiply-accumulate with carry
        let mut carry = 1;
        let result = mac_with_carry(1u64, 2u64, 3u64, &mut carry);
        assert_eq!(result, 8); // 1 + (2 * 3) + 1 = 8
        assert_eq!(carry, 0); // No overflow, carry remains 0

        // Multiply-accumulate with carry and large values
        let mut carry = 1;
        let result = mac_with_carry(u64::MAX, u64::MAX, 1u64, &mut carry);
        assert_eq!(result, u64::MAX); // Result wraps around
        assert_eq!(carry, 1); // Carry is set due to overflow
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
                    cur *= 2;
                }
                sum
            };

            let test_expected = {
                let mut sum = BigInt::zero();
                let mut cur = BigInt::one();
                for v in num.iter() {
                    sum += cur.clone() * v;
                    cur <<= 64;
                }
                sum
            };

            assert_eq!(test, test_expected);
        }
    }

    #[test]
    fn test_find_naf_zero() {
        // Test for zero input
        let naf = find_naf(&[0]);
        assert!(naf.is_empty());
    }

    #[test]
    fn test_find_naf_single_digit() {
        // Test for small numbers
        assert_eq!(find_naf(&[1]), vec![1]);
        assert_eq!(find_naf(&[2]), vec![0, 1]);
        assert_eq!(find_naf(&[3]), vec![-1, 0, 1]);
        assert_eq!(find_naf(&[4]), vec![0, 0, 1]);
    }

    #[test]
    fn test_find_naf_large_number() {
        // Test for a larger number
        assert_eq!(find_naf(&[13]), vec![1, 0, -1, 0, 1]);
    }

    #[test]
    fn test_find_naf_multiple_blocks() {
        // Test multi-block number (simulate large numbers split across blocks)
        let num = [0, 1];
        assert_eq!(
            find_naf(&num),
            vec![
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 1
            ]
        );
    }

    #[test]
    fn test_find_naf_edge_cases() {
        // Test edge cases
        let naf = find_naf(&[u64::MAX]);
        assert!(naf.len() > 0);
    }
}

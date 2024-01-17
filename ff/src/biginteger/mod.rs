use crate::{
    bits::{BitIteratorBE, BitIteratorLE},
    const_for, UniformRand,
};
#[allow(unused)]
use ark_ff_macros::unroll_for_loops;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::Borrow,
    cmp::Ordering,
    convert::TryFrom,
    fmt::{Debug, Display, UpperHex},
    io::{Read, Write},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Rem, RemAssign, Shl,
        ShlAssign, Shr, ShrAssign,
    },
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
};
use num_bigint::BigUint;
use zeroize::Zeroize;

#[macro_use]
pub mod arithmetic;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, Zeroize)]
pub struct BigInt<const N: usize>(pub [u64; N]);

impl<const N: usize> Default for BigInt<N> {
    fn default() -> Self {
        Self([0u64; N])
    }
}

impl<const N: usize> CanonicalSerialize for BigInt<N> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.0.serialized_size(compress)
    }
}

impl<const N: usize> Valid for BigInt<N> {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<const N: usize> CanonicalDeserialize for BigInt<N> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(BigInt::<N>(<[u64; N]>::deserialize_with_mode(
            reader, compress, validate,
        )?))
    }
}

/// Construct a [`struct@BigInt<N>`] element from a literal string.
///
/// # Panics
///
/// If the integer represented by the string cannot fit in the number
/// of limbs of the `BigInt`, this macro results in a
/// * compile-time error if used in a const context
/// * run-time error otherwise.
///
/// # Usage
/// ```rust
/// # use ark_ff::BigInt;
/// const ONE: BigInt<6> = BigInt!("1");
///
/// fn check_correctness() {
///     assert_eq!(ONE, BigInt::from(1u8));
/// }
/// ```
#[macro_export]
macro_rules! BigInt {
    ($c0:expr) => {{
        let (is_positive, limbs) = $crate::ark_ff_macros::to_sign_and_limbs!($c0);
        assert!(is_positive);
        let mut integer = $crate::BigInt::zero();
        assert!(integer.0.len() >= limbs.len());
        $crate::const_for!((i in 0..(limbs.len())) {
            integer.0[i] = limbs[i];
        });
        integer
    }};
}

#[doc(hidden)]
macro_rules! const_modulo {
    ($a:expr, $divisor:expr) => {{
        // Stupid slow base-2 long division taken from
        // https://en.wikipedia.org/wiki/Division_algorithm
        assert!(!$divisor.const_is_zero());
        let mut remainder = Self::new([0u64; N]);
        let end = $a.num_bits();
        let mut i = (end - 1) as isize;
        let mut carry;
        while i >= 0 {
            (remainder, carry) = remainder.const_mul2_with_carry();
            remainder.0[0] |= $a.get_bit(i as usize) as u64;
            if remainder.const_geq($divisor) || carry {
                let (r, borrow) = remainder.const_sub_with_borrow($divisor);
                remainder = r;
                assert!(borrow == carry);
            }
            i -= 1;
        }
        remainder
    }};
}

impl<const N: usize> BigInt<N> {
    pub const fn new(value: [u64; N]) -> Self {
        Self(value)
    }

    pub const fn zero() -> Self {
        Self([0u64; N])
    }

    pub const fn one() -> Self {
        let mut one = Self::zero();
        one.0[0] = 1;
        one
    }

    #[doc(hidden)]
    pub const fn const_is_even(&self) -> bool {
        self.0[0] % 2 == 0
    }

    #[doc(hidden)]
    pub const fn const_is_odd(&self) -> bool {
        self.0[0] % 2 == 1
    }

    #[doc(hidden)]
    pub const fn mod_4(&self) -> u8 {
        // To compute n % 4, we need to simply look at the
        // 2 least significant bits of n, and check their value mod 4.
        (((self.0[0] << 62) >> 62) % 4) as u8
    }

    /// Compute a right shift of `self`
    /// This is equivalent to a (saturating) division by 2.
    #[doc(hidden)]
    pub const fn const_shr(&self) -> Self {
        let mut result = *self;
        let mut t = 0;
        crate::const_for!((i in 0..N) {
            let a = result.0[N - i - 1];
            let t2 = a << 63;
            result.0[N - i - 1] >>= 1;
            result.0[N - i - 1] |= t;
            t = t2;
        });
        result
    }

    const fn const_geq(&self, other: &Self) -> bool {
        const_for!((i in 0..N) {
            let a = self.0[N - i - 1];
            let b = other.0[N - i - 1];
            if a < b {
                return false;
            } else if a > b {
                return true;
            }
        });
        true
    }

    /// Compute the largest integer `s` such that `self = 2**s * t + 1` for odd `t`.
    #[doc(hidden)]
    pub const fn two_adic_valuation(mut self) -> u32 {
        let mut two_adicity = 0;
        assert!(self.const_is_odd());
        // Since `self` is odd, we can always subtract one
        // without a borrow
        self.0[0] -= 1;
        while self.const_is_even() {
            self = self.const_shr();
            two_adicity += 1;
        }
        two_adicity
    }

    /// Compute the smallest odd integer `t` such that `self = 2**s * t + 1` for some
    /// integer `s = self.two_adic_valuation()`.
    #[doc(hidden)]
    pub const fn two_adic_coefficient(mut self) -> Self {
        assert!(self.const_is_odd());
        // Since `self` is odd, we can always subtract one
        // without a borrow
        self.0[0] -= 1;
        while self.const_is_even() {
            self = self.const_shr();
        }
        assert!(self.const_is_odd());
        self
    }

    /// Divide `self` by 2, rounding down if necessary.
    /// That is, if `self.is_odd()`, compute `(self - 1)/2`.
    /// Else, compute `self/2`.
    #[doc(hidden)]
    pub const fn divide_by_2_round_down(mut self) -> Self {
        if self.const_is_odd() {
            self.0[0] -= 1;
        }
        self.const_shr()
    }

    /// Find the number of bits in the binary decomposition of `self`.
    #[doc(hidden)]
    pub const fn const_num_bits(self) -> u32 {
        ((N - 1) * 64) as u32 + (64 - self.0[N - 1].leading_zeros())
    }

    #[inline]
    pub(crate) const fn const_sub_with_borrow(mut self, other: &Self) -> (Self, bool) {
        let mut borrow = 0;

        const_for!((i in 0..N) {
            self.0[i] = sbb!(self.0[i], other.0[i], &mut borrow);
        });

        (self, borrow != 0)
    }

    #[inline]
    pub(crate) const fn const_add_with_carry(mut self, other: &Self) -> (Self, bool) {
        let mut carry = 0;

        crate::const_for!((i in 0..N) {
            self.0[i] = adc!(self.0[i], other.0[i], &mut carry);
        });

        (self, carry != 0)
    }

    const fn const_mul2_with_carry(mut self) -> (Self, bool) {
        let mut last = 0;
        crate::const_for!((i in 0..N) {
            let a = self.0[i];
            let tmp = a >> 63;
            self.0[i] <<= 1;
            self.0[i] |= last;
            last = tmp;
        });
        (self, last != 0)
    }

    pub(crate) const fn const_is_zero(&self) -> bool {
        let mut is_zero = true;
        crate::const_for!((i in 0..N) {
            is_zero &= self.0[i] == 0;
        });
        is_zero
    }

    /// Computes the Montgomery R constant modulo `self`.
    #[doc(hidden)]
    pub const fn montgomery_r(&self) -> Self {
        let two_pow_n_times_64 = crate::const_helpers::RBuffer::<N>([0u64; N], 1);
        const_modulo!(two_pow_n_times_64, self)
    }

    /// Computes the Montgomery R2 constant modulo `self`.
    #[doc(hidden)]
    pub const fn montgomery_r2(&self) -> Self {
        let two_pow_n_times_64_square =
            crate::const_helpers::R2Buffer::<N>([0u64; N], [0u64; N], 1);
        const_modulo!(two_pow_n_times_64_square, self)
    }
}

impl<const N: usize> BigInteger for BigInt<N> {
    const NUM_LIMBS: usize = N;
    const RADIX: u128 = 1 << 64;

    #[inline]
    fn add_with_carry(&mut self, other: &Self) -> bool {
        {
            use arithmetic::adc_for_add_with_carry as adc;

            let a = &mut self.0;
            let b = &other.0;
            let mut carry = 0;

            if N >= 1 {
                carry = adc(&mut a[0], b[0], carry);
            }
            if N >= 2 {
                carry = adc(&mut a[1], b[1], carry);
            }
            if N >= 3 {
                carry = adc(&mut a[2], b[2], carry);
            }
            if N >= 4 {
                carry = adc(&mut a[3], b[3], carry);
            }
            if N >= 5 {
                carry = adc(&mut a[4], b[4], carry);
            }
            if N >= 6 {
                carry = adc(&mut a[5], b[5], carry);
            }
            for i in 6..N {
                carry = adc(&mut a[i], b[i], carry);
            }
            carry != 0
        }
    }

    #[inline]
    fn sub_with_borrow(&mut self, other: &Self) -> bool {
        use arithmetic::sbb_for_sub_with_borrow as sbb;

        let a = &mut self.0;
        let b = &other.0;
        let mut borrow = 0u8;

        if N >= 1 {
            borrow = sbb(&mut a[0], b[0], borrow);
        }
        if N >= 2 {
            borrow = sbb(&mut a[1], b[1], borrow);
        }
        if N >= 3 {
            borrow = sbb(&mut a[2], b[2], borrow);
        }
        if N >= 4 {
            borrow = sbb(&mut a[3], b[3], borrow);
        }
        if N >= 5 {
            borrow = sbb(&mut a[4], b[4], borrow);
        }
        if N >= 6 {
            borrow = sbb(&mut a[5], b[5], borrow);
        }
        for i in 6..N {
            borrow = sbb(&mut a[i], b[i], borrow);
        }
        borrow != 0
    }

    #[inline]
    #[allow(unused)]
    fn mul2(&mut self) -> bool {
        #[cfg(all(target_arch = "x86_64", feature = "asm"))]
        #[allow(unsafe_code)]
        {
            let mut carry = 0;

            for i in 0..N {
                unsafe {
                    use core::arch::x86_64::_addcarry_u64;
                    carry = _addcarry_u64(carry, self.0[i], self.0[i], &mut self.0[i])
                };
            }

            carry != 0
        }

        #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
        {
            let mut last = 0;
            for i in 0..N {
                let a = &mut self.0[i];
                let tmp = *a >> 63;
                *a <<= 1;
                *a |= last;
                last = tmp;
            }
            last != 0
        }
    }

    #[inline]
    fn muln(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::from(0u64);
            return;
        }

        while n >= 64 {
            let mut t = 0;
            for i in 0..N {
                core::mem::swap(&mut t, &mut self.0[i]);
            }
            n -= 64;
        }

        if n > 0 {
            let mut t = 0;
            #[allow(unused)]
            for i in 0..N {
                let a = &mut self.0[i];
                let t2 = *a >> (64 - n);
                *a <<= n;
                *a |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn div2(&mut self) {
        let mut t = 0;
        for i in 0..N {
            let a = &mut self.0[N - i - 1];
            let t2 = *a << 63;
            *a >>= 1;
            *a |= t;
            t = t2;
        }
    }

    #[inline]
    fn divn(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::from(0u64);
            return;
        }

        while n >= 64 {
            let mut t = 0;
            for i in 0..N {
                core::mem::swap(&mut t, &mut self.0[N - i - 1]);
            }
            n -= 64;
        }

        if n > 0 {
            let mut t = 0;
            #[allow(unused)]
            for i in 0..N {
                let a = &mut self.0[N - i - 1];
                let t2 = *a << (64 - n);
                *a >>= n;
                *a |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.iter().all(|&e| e == 0)
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.iter().skip(1).all(|&e| e == 0) && self.0[0] == 1
    }

    #[inline]
    fn num_bits(&self) -> u32 {
        let mut ret = N as u32 * 64;
        for i in self.0.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
        }

        ret
    }

    #[inline]
    fn get_bit(&self, i: usize) -> bool {
        if i >= 64 * N {
            false
        } else {
            let limb = i / 64;
            let bit = i - (64 * limb);
            (self.0[limb] & (1 << bit)) != 0
        }
    }

    #[inline]
    fn from_bits_be(bits: &[bool]) -> Self {
        let mut res = Self::default();
        let mut acc: u64 = 0;

        let mut bits = bits.to_vec();
        bits.reverse();
        for (i, bits64) in bits.chunks(64).enumerate() {
            for bit in bits64.iter().rev() {
                acc <<= 1;
                acc += *bit as u64;
            }
            res.0[i] = acc;
            acc = 0;
        }
        res
    }

    fn from_bits_le(bits: &[bool]) -> Self {
        let mut res = Self::zero();
        for (bits64, res_i) in bits.chunks(64).zip(&mut res.0) {
            for (i, bit) in bits64.iter().enumerate() {
                *res_i |= (*bit as u64) << i;
            }
        }
        res
    }

    #[inline]
    fn to_bytes_be(&self) -> Vec<u8> {
        let mut le_bytes = self.to_bytes_le();
        le_bytes.reverse();
        le_bytes
    }

    #[inline]
    fn to_bytes_le(&self) -> Vec<u8> {
        let array_map = self.0.iter().map(|limb| limb.to_le_bytes());
        let mut res = Vec::with_capacity(N * 8);
        for limb in array_map {
            res.extend_from_slice(&limb);
        }
        res
    }
}

impl<const N: usize> UpperHex for BigInt<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:016X}", BigUint::from(*self))
    }
}

impl<const N: usize> Display for BigInt<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", BigUint::from(*self))
    }
}

impl<const N: usize> Ord for BigInt<N> {
    #[inline]
    #[cfg_attr(target_arch = "x86_64", unroll_for_loops(12))]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        #[cfg(target_arch = "x86_64")]
        for i in 0..N {
            let a = &self.0[N - i - 1];
            let b = &other.0[N - i - 1];
            match a.cmp(b) {
                Ordering::Equal => {},
                order => return order,
            };
        }
        #[cfg(not(target_arch = "x86_64"))]
        for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
            if a < b {
                return Ordering::Less;
            } else if a > b {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }
}

impl<const N: usize> PartialOrd for BigInt<N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Distribution<BigInt<N>> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BigInt<N> {
        let mut res = [0u64; N];
        for item in res.iter_mut() {
            *item = rng.gen();
        }
        BigInt::<N>(res)
    }
}

impl<const N: usize> AsMut<[u64]> for BigInt<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }
}

impl<const N: usize> AsRef<[u64]> for BigInt<N> {
    #[inline]
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}

impl<const N: usize> From<u64> for BigInt<N> {
    #[inline]
    fn from(val: u64) -> BigInt<N> {
        let mut repr = Self::default();
        repr.0[0] = val;
        repr
    }
}

impl<const N: usize> From<u32> for BigInt<N> {
    #[inline]
    fn from(val: u32) -> BigInt<N> {
        let mut repr = Self::default();
        repr.0[0] = u64::from(val);
        repr
    }
}

impl<const N: usize> From<u16> for BigInt<N> {
    #[inline]
    fn from(val: u16) -> BigInt<N> {
        let mut repr = Self::default();
        repr.0[0] = u64::from(val);
        repr
    }
}

impl<const N: usize> From<u8> for BigInt<N> {
    #[inline]
    fn from(val: u8) -> BigInt<N> {
        let mut repr = Self::default();
        repr.0[0] = u64::from(val);
        repr
    }
}

impl<const N: usize> TryFrom<BigUint> for BigInt<N> {
    type Error = ();

    /// Returns `Err(())` if the bit size of `val` is more than `N * 64`.
    #[inline]
    fn try_from(val: num_bigint::BigUint) -> Result<BigInt<N>, Self::Error> {
        let bytes = val.to_bytes_le();

        if bytes.len() > N * 8 {
            Err(())
        } else {
            let mut limbs = [0u64; N];

            bytes
                .chunks(8)
                .into_iter()
                .enumerate()
                .for_each(|(i, chunk)| {
                    let mut chunk_padded = [0u8; 8];
                    chunk_padded[..chunk.len()].copy_from_slice(chunk);
                    limbs[i] = u64::from_le_bytes(chunk_padded)
                });

            Ok(Self(limbs))
        }
    }
}

impl<const N: usize> From<BigInt<N>> for BigUint {
    #[inline]
    fn from(val: BigInt<N>) -> num_bigint::BigUint {
        BigUint::from_bytes_le(&val.to_bytes_le())
    }
}

impl<B: Borrow<Self>, const N: usize> BitXorAssign<B> for BigInt<N> {
    fn bitxor_assign(&mut self, rhs: B) {
        (0..N).for_each(|i| self.0[i] ^= rhs.borrow().0[i])
    }
}

impl<B: Borrow<Self>, const N: usize> BitXor<B> for BigInt<N> {
    type Output = Self;

    fn bitxor(mut self, rhs: B) -> Self::Output {
        self ^= rhs;
        self
    }
}

impl<B: Borrow<Self>, const N: usize> BitAndAssign<B> for BigInt<N> {
    fn bitand_assign(&mut self, rhs: B) {
        (0..N).for_each(|i| self.0[i] &= rhs.borrow().0[i])
    }
}

impl<B: Borrow<Self>, const N: usize> BitAnd<B> for BigInt<N> {
    type Output = Self;

    fn bitand(mut self, rhs: B) -> Self::Output {
        self &= rhs;
        self
    }
}

impl<B: Borrow<Self>, const N: usize> BitOrAssign<B> for BigInt<N> {
    fn bitor_assign(&mut self, rhs: B) {
        (0..N).for_each(|i| self.0[i] |= rhs.borrow().0[i])
    }
}

impl<B: Borrow<Self>, const N: usize> BitOr<B> for BigInt<N> {
    type Output = Self;

    fn bitor(mut self, rhs: B) -> Self::Output {
        self |= rhs;
        self
    }
}

impl<const N: usize> ShrAssign<u32> for BigInt<N> {
    /// Computes the bitwise shift right operation in place.
    ///
    /// Differently from the built-in numeric types (u8, u32, u64, etc.) this
    /// operation does *not* return an underflow error if the number of bits
    /// shifted is larger than N * 64. Instead the result will be saturated to
    /// zero.
    fn shr_assign(&mut self, mut rhs: u32) {
        if rhs >= (64 * N) as u32 {
            *self = Self::from(0u64);
        }

        while rhs >= 64 {
            let mut t = 0;
            for i in 0..N {
                core::mem::swap(&mut t, &mut self.0[N - i - 1]);
            }
            rhs -= 64;
        }

        if rhs > 0 {
            let mut t = 0;
            for i in 0..N {
                let a = &mut self.0[N - i - 1];
                let t2 = *a << (64 - rhs);
                *a >>= rhs;
                *a |= t;
                t = t2;
            }
        }
    }
}

impl<const N: usize> Shr<u32> for BigInt<N> {
    type Output = Self;

    /// Computes bitwise shift right operation.
    ///
    /// Differently from the built-in numeric types (u8, u32, u64, etc.) this
    /// operation does *not* return an underflow error if the number of bits
    /// shifted is larger than N * 64. Instead the result will be saturated to
    /// zero.
    fn shr(mut self, rhs: u32) -> Self::Output {
        self >>= rhs;
        self
    }
}

impl<const N: usize> ShlAssign<u32> for BigInt<N> {
    /// Computes the bitwise shift left operation in place.
    ///
    /// Differently from the built-in numeric types (u8, u32, u64, etc.) this
    /// operation does *not* return an overflow error if the number of bits
    /// shifted is larger than N * 64. Instead, the overflow will be chopped
    /// off.
    fn shl_assign(&mut self, mut rhs: u32) {
        if rhs >= (64 * N) as u32 {
            *self = Self::from(0u64);
            return;
        }

        while rhs >= 64 {
            let mut t = 0;
            for i in 0..N {
                core::mem::swap(&mut t, &mut self.0[i]);
            }
            rhs -= 64;
        }

        if rhs > 0 {
            let mut t = 0;
            #[allow(unused)]
            for i in 0..N {
                let a = &mut self.0[i];
                let t2 = *a >> (64 - rhs);
                *a <<= rhs;
                *a |= t;
                t = t2;
            }
        }
    }
}

impl<const N: usize> Shl<u32> for BigInt<N> {
    type Output = Self;

    /// Computes the bitwise shift left operation in place.
    ///
    /// Differently from the built-in numeric types (u8, u32, u64, etc.) this
    /// operation does *not* return an overflow error if the number of bits
    /// shifted is larger than N * 64. Instead, the overflow will be chopped
    /// off.
    fn shl(mut self, rhs: u32) -> Self::Output {
        self <<= rhs;
        self
    }
}

impl<const N: usize> Not for BigInt<N> {
    type Output = Self;

    fn not(self) -> Self::Output {
        let mut result = Self::zero();
        for i in 0..N {
            result.0[i] = !self.0[i];
        }
        result
    }
}

/// Computes a division between to BigInt with remainder.
///
/// This algorithm is taken from "The Art of Computer Programming" by Donald
/// Knuth, Third Edition, Section 4.3.2, Algorithm D, with some elements taken
/// from the repository https://github.com/rust-num/num-bigint.
fn div_with_rem<B: Borrow<BigInt<N>>, const N: usize>(
    a: BigInt<N>,
    d: B,
) -> (BigInt<N>, BigInt<N>) {
    // Basic cases
    if d.borrow().is_zero() {
        panic!("trying to divide by zero");
    }
    if d.borrow().is_one() {
        return (a, BigInt::<N>::zero());
    }
    if a.is_zero() {
        return (BigInt::<N>::zero(), BigInt::<N>::zero());
    }

    // Covers the case of N = 1, for which the quotient and remainder are
    // computed as usual.
    if N == 1 {
        let q: u64 = a.0[0] / d.borrow().0[0];
        let r: u64 = a.0[0] % d.borrow().0[0];
        return (BigInt::<N>::from(q), BigInt::<N>::from(r));
    }

    // Covers immediate cases where a <= d.
    match a.cmp(d.borrow()) {
        Ordering::Less => return (BigInt::<N>::zero(), a),
        Ordering::Equal => return (BigInt::<N>::one(), BigInt::<N>::zero()),
        Ordering::Greater => {}, // This case is covered in what follows.
    }

    // Here, we are in the case where a >= d, and it's not a trivial case. We
    // will apply the TAOCP algorithm.

    // Considers the case where N is not 1, but the only non-zero limb of v is
    // the least significant limb. We can apply unwrap here because we know that a
    // is not zero, so there should be at least one limb with a non-zero value.
    let index_non_zero_d = d.borrow().0.iter().rposition(|&e| e != 0).unwrap();
    if index_non_zero_d == 0 {
        // Removes the most significant limbs with value zero from a.
        let index_non_zero_a = a.0.iter().rposition(|&e| e != 0).unwrap();
        let u = a.0[..index_non_zero_a + 1].to_vec();

        // Takes the only non-zero limb of v.
        let v = d.borrow().0[index_non_zero_d];

        return div_with_rem_one_digit(u, v);
    }

    // Computes the normalization factor.
    let shift = d.borrow().0[index_non_zero_d].leading_zeros() as u32;

    if shift == 0 {
        div_with_rem_core(a.0.to_vec(), d.borrow().0.to_vec())
    } else {
        // Here we construct the shifted version of a without chopping the overflow.
        // Instead, we add another limb to store the overflow and putting it as
        // the most significant limb.

        // Captures the most sifnificant limb of a before the shifting. Be careful:
        // this limb can be zero.
        let most_sig_a = *a.0.last().unwrap();

        // Shift a
        let shifted_a_bi = a << shift; // bi stands for BigInteger.
        let mut a_shifted = shifted_a_bi.0.to_vec();

        // Check if we need to add an overflow to a. If the most significant
        // limb of a before the sifting is zero, we don't need to add an
        // additional overflow.
        if most_sig_a != 0 {
            let overflow = most_sig_a >> (64 - shift);
            a_shifted.push(overflow);
        } else {
            // If the most significant limb is zero we chop the most significant
            // limbs that are zero after shifting a.
            let index_non_zero_a_shifted = a_shifted.iter().rposition(|&e| e != 0).unwrap();
            a_shifted = a_shifted[0..index_non_zero_a_shifted + 1].to_vec();
        }

        // Apply the shift to d and chop the most significant limbs with value
        // zero to d before applying the core algorithm.
        let shifted_d_bi = *d.borrow() << shift;
        let d_shifted = shifted_d_bi.0[0..index_non_zero_d + 1].to_vec();

        let (q, r) = div_with_rem_core(a_shifted, d_shifted);
        return (q, r >> shift);
    }
}

/// Computes the division with remainder between u = [u_0, ..., u_(n + 1)] and v, where
/// v has just one non-zero limbs.
fn div_with_rem_one_digit<const N: usize>(mut u: Vec<u64>, v: u64) -> (BigInt<N>, BigInt<N>) {
    if v == 0 {
        panic!("trying to divide by zero.");
    }

    let mut rem = 0;

    for d in u.iter_mut().rev() {
        let (q, r) = div_with_rem_wide(rem, *d, v);
        *d = q;
        rem = r;
    }

    let mut q_result = [0; N];
    let mut r_result = [0; N];
    q_result.copy_from_slice(&u);
    r_result[0] = rem;

    (BigInt::new(q_result), BigInt::new(r_result))
}

/// Divides a two-limb number by a one limb number returning the quotient and the remainder.
///
/// More specifically, this method computes the divission between [lo, hi] / div.
#[inline]
fn div_with_rem_wide(hi: u64, lo: u64, div: u64) -> (u64, u64) {
    let dividend = from_two_u64_to_u128(lo, hi);
    let divisor = div as u128;
    let q = (dividend / divisor) as u64;
    let r = (dividend % divisor) as u64;
    (q, r)
}

/// Core of the algorithm for long division.
///
/// Computes the long division between two BigInt. This function receives two
/// `Vec<u64>` given that it is more easy to manipulate the data this way.
/// In this algorithm, the notation is [less_sig, ..., most_sig] for
/// the radix-b representation.
fn div_with_rem_core<const N: usize>(mut u: Vec<u64>, v: Vec<u64>) -> (BigInt<N>, BigInt<N>) {
    // Length of the resulting quotient
    let q_length = u.len() - v.len() + 1;

    // This vector will store the result of the quotient.
    let mut q = vec![0; q_length];

    let v0 = *v.last().unwrap(); // Most significant bit of v.
    let v1 = v[v.len() - 2];

    let mut u0 = 0; // Additional most significant limb as mentioned in Step D1.

    // We procceed as in the TAOCP algorithm, Steps D2-D7.
    for j in (0..q_length).rev() {
        let u1 = *u.last().unwrap(); // Most significant bit of u.
        let u2 = u[u.len() - 2]; // We can do this given that N > 1.

        // Step D3.
        let (mut q_hat, rem) = div_with_rem_wide(u0, u1, v0);
        let mut r_hat = rem as u128;
        loop {
            if (q_hat as u128) == BigInt::<N>::RADIX
                || from_two_u64_to_u128(u2, r_hat as u64) < (q_hat as u128) * (v1 as u128)
            {
                q_hat -= 1;
                r_hat += v0 as u128; // Promoted to u128 to avoid overflow.
            } else {
                break;
            }

            // Test the previous condition again in the case that r_hat < u64::MAX, as
            // specified in Step D3.
            if r_hat >= BigInt::<N>::RADIX {
                break;
            }
        }

        // Step D4. Step D5 is not explicitly stated given that the result of the
        // division has just one limb.
        let mut borrow = sub_mul_with_borrow(&mut u[j..], &v, q_hat);

        // Step D6.
        if borrow > u0 {
            q_hat -= 1;
            borrow -= add_different_len(&mut u[j..], &v);
        }

        debug_assert!(borrow == u0);

        // Deletes the most significant bit of u. At the end, u will have length N.
        u0 = u.pop().unwrap();

        // Reconstruct BigInt<N>
        q[j] = q_hat; // It moves just one limb given that the quotient needs
                      // just one limb by definition.
    }

    u.push(u0);

    // Collect the remainder and the quotient into arrays.
    let mut remainder = [0; N];
    let mut quotient = [0; N];

    // Append missing limbs to u and q
    let miss_zeros_u = N - u.len();
    for _ in 0..miss_zeros_u {
        u.push(0);
    }

    let miss_zeros_q = N - q.len();
    for _ in 0..miss_zeros_q {
        q.push(0);
    }

    remainder.copy_from_slice(&u);
    quotient.copy_from_slice(&q);

    (BigInt::new(quotient), BigInt::new(remainder))
}

/// Computes `u = u - q * v`, where `u = [u_0, ..., u_(n + 1)]`, `q` has just one limb and
/// `v = [v_0, ..., v_n]`, and returns the borrow. This source code is based in the one presented
/// in https://github.com/rust-num/num-bigint/blob/master/src/bigint/division.rs.
fn sub_mul_with_borrow(u: &mut [u64], v: &Vec<u64>, q: u64) -> u64 {
    // We do this because the borrow is in the interval [-u64::MAX, 0]. Hence, to avoid overflow
    // we compute the carry plus an offset. Then we retrieve the possitive value of the borrow
    // by removing the offset.
    let mut offset_carry = u64::MAX;

    for (x, y) in u.iter_mut().zip(v) {
        // x - y * q + carry
        let offset_sum = from_two_u64_to_u128(*x, u64::MAX) - (u64::MAX as u128)
            + (offset_carry as u128)
            - (*y as u128) * (q as u128);

        let (new_offset_carry, new_x) = get_u64_limbs_from_u128(offset_sum);
        offset_carry = new_offset_carry;

        *x = new_x;
    }

    u64::MAX - offset_carry
}

/// Obtains the 64 most significant bits as an u68 value from a u128 value.
#[inline]
fn get_high_u64_from_u128(n: u128) -> u64 {
    (n >> 64) as u64
}

/// Obtains the 64 least significant bits as an u68 value from a u128 value.
#[inline]
fn get_low_u64_from_u128(n: u128) -> u64 {
    // This is equivalent to the 64 least significant bits set to 1 (0xFFFFFFFFFFFFFFFF)
    const LOW_MASK: u128 = (1_u128 << 64) - 1;
    (n & LOW_MASK) as u64
}

/// Obtains the two limbs of a u128 value as u64 values.
#[inline]
fn get_u64_limbs_from_u128(n: u128) -> (u64, u64) {
    (get_high_u64_from_u128(n), get_low_u64_from_u128(n))
}

/// Computes the sum of `carry + a + b` storing the result in `output` and returning
/// the carry flag as `u8`.
#[inline]
fn add_with_carry(carry_in: u8, a: u64, b: u64, output: &mut u64) -> u8 {
    let (out_a_b, carry_a_b) = a.overflowing_add(b);
    let (out_ab_carry, carry_ab_carry) = out_a_b.overflowing_add(carry_in as u64);
    let carry_sum = (carry_a_b as u8) + (carry_ab_carry as u8);
    let (out_sum_carry, final_carry) = out_ab_carry.overflowing_add(carry_sum as u64);
    *output = out_sum_carry;
    final_carry as u8
}

/// Converts two u64 numbers `low` and `high` into an u128 representation of the number
/// `[low, high]`.
#[inline]
fn from_two_u64_to_u128(low: u64, high: u64) -> u128 {
    (u128::from(high) << 64) | u128::from(low)
}

/// Computes the addition two values in radix u64 and returns the carry. Those
/// two values have not necessarily the same number of limbs. This algorithm is
/// inspired from https://github.com/rust-num/num-bigint/blob/master/src/bigint/addition.rs.
fn add_different_len(u: &mut [u64], v: &Vec<u64>) -> u64 {
    let mut carry = 0;
    let (u_low, u_high) = u.split_at_mut(v.len());

    for (u, v) in u_low.iter_mut().zip(v) {
        carry = add_with_carry(carry, *u, *v, u);
    }

    if carry != 0 {
        for u in u_high {
            carry = add_with_carry(carry, *u, 0, u);
            if carry == 0 {
                break;
            }
        }
    }

    carry as u64
}

impl<B: Borrow<Self>, const N: usize> Rem<B> for BigInt<N> {
    type Output = Self;

    /// Computes the remainder between two `BigInt`.
    fn rem(mut self, rhs: B) -> Self::Output {
        self %= rhs;
        self
    }
}

impl<B: Borrow<Self>, const N: usize> RemAssign<B> for BigInt<N> {
    /// Computes the remainder between `self` and `rhs`, assigning the result to
    /// `self`.
    fn rem_assign(&mut self, rhs: B) {
        let (_, rem) = div_with_rem(*self, rhs);
        (0..N).for_each(|i| self.0[i] = rem.0[i]);
    }
}

/// Compute the signed modulo operation on a u64 representation, returning the result.
/// If n % modulus > modulus / 2, return modulus - n
/// # Example
/// ```
/// use ark_ff::signed_mod_reduction;
/// let res = signed_mod_reduction(6u64, 8u64);
/// assert_eq!(res, -2i64);
/// ```
pub fn signed_mod_reduction(n: u64, modulus: u64) -> i64 {
    let t = (n % modulus) as i64;
    if t as u64 >= (modulus / 2) {
        t - (modulus as i64)
    } else {
        t
    }
}

pub type BigInteger64 = BigInt<1>;
pub type BigInteger128 = BigInt<2>;
pub type BigInteger256 = BigInt<4>;
pub type BigInteger320 = BigInt<5>;
pub type BigInteger384 = BigInt<6>;
pub type BigInteger448 = BigInt<7>;
pub type BigInteger768 = BigInt<12>;
pub type BigInteger832 = BigInt<13>;

#[cfg(test)]
mod tests;

/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant limb first.
// TODO: get rid of this trait once we can use associated constants in const generics.
pub trait BigInteger:
    CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Clone
    + Debug
    + Default
    + Display
    + Eq
    + Ord
    + Send
    + Sized
    + Sync
    + 'static
    + UniformRand
    + Zeroize
    + AsMut<[u64]>
    + AsRef<[u64]>
    + From<u64>
    + From<u32>
    + From<u16>
    + From<u8>
    + TryFrom<BigUint, Error = ()>
    + Into<BigUint>
    + BitXorAssign<Self>
    + for<'a> BitXorAssign<&'a Self>
    + BitXor<Self, Output = Self>
    + for<'a> BitXor<&'a Self, Output = Self>
    + BitAndAssign<Self>
    + for<'a> BitAndAssign<&'a Self>
    + BitAnd<Self, Output = Self>
    + for<'a> BitAnd<&'a Self, Output = Self>
    + BitOrAssign<Self>
    + for<'a> BitOrAssign<&'a Self>
    + BitOr<Self, Output = Self>
    + for<'a> BitOr<&'a Self, Output = Self>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Rem<Self, Output = Self>
    + for<'a> Rem<&'a Self, Output = Self>
    + RemAssign<Self>
    + for<'a> RemAssign<&'a Self>
{
    /// Number of 64-bit limbs representing `Self`.
    const NUM_LIMBS: usize;

    /// Radix of the representation. This is the number of different "digits" that
    /// can be represented by one limb.
    const RADIX: u128;

    /// Add another [`BigInteger`] to `self`. This method stores the result in `self`,
    /// and returns a carry bit.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut x) = (B::from(1u64), B::from(2u64));
    /// let carry = x.add_with_carry(&one);
    /// assert_eq!(x, B::from(3u64));
    /// assert_eq!(carry, false);
    ///
    /// // Edge-Case
    /// let mut x = B::from(u64::MAX);
    /// let carry = x.add_with_carry(&one);
    /// assert_eq!(x, B::from(0u64));
    /// assert_eq!(carry, true)
    /// ```
    fn add_with_carry(&mut self, other: &Self) -> bool;

    /// Subtract another [`BigInteger`] from this one. This method stores the result in
    /// `self`, and returns a borrow.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one_sub, two, mut three_sub) = (B::from(1u64), B::from(2u64), B::from(3u64));
    /// let borrow = three_sub.sub_with_borrow(&two);
    /// assert_eq!(three_sub, one_sub);
    /// assert_eq!(borrow, false);
    ///
    /// // Edge-Case
    /// let borrow = one_sub.sub_with_borrow(&two);
    /// assert_eq!(one_sub, B::from(u64::MAX));
    /// assert_eq!(borrow, true);
    /// ```
    fn sub_with_borrow(&mut self, other: &Self) -> bool;

    /// Performs a leftwise bitshift of this number, effectively multiplying
    /// it by 2. Overflow is ignored.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let mut two_mul = B::from(2u64);
    /// two_mul.mul2();
    /// assert_eq!(two_mul, B::from(4u64));
    ///
    /// // Edge-Cases
    /// let mut zero = B::from(0u64);
    /// zero.mul2();
    /// assert_eq!(zero, B::from(0u64));
    ///
    /// let mut arr: [bool; 64] = [false; 64];
    /// arr[0] = true;
    /// let mut mul = B::from_bits_be(&arr);
    /// mul.mul2();
    /// assert_eq!(mul, B::from(0u64));
    /// ```
    fn mul2(&mut self) -> bool;

    /// Performs a leftwise bitshift of this number by n bits, effectively multiplying
    /// it by 2^n. Overflow is ignored.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let mut one_mul = B::from(1u64);
    /// one_mul.muln(5);
    /// assert_eq!(one_mul, B::from(32u64));
    ///
    /// // Edge-Case
    /// let mut zero = B::from(0u64);
    /// zero.muln(5);
    /// assert_eq!(zero, B::from(0u64));
    ///
    /// let mut arr: [bool; 64] = [false; 64];
    /// arr[4] = true;
    /// let mut mul = B::from_bits_be(&arr);
    /// mul.muln(5);
    /// assert_eq!(mul, B::from(0u64));
    /// ```
    #[deprecated(since = "0.4.2", note = "please use the operator `>>` instead")]
    fn muln(&mut self, amt: u32);

    /// Performs a rightwise bitshift of this number, effectively dividing
    /// it by 2.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut two, mut four_div) = (B::from(2u64), B::from(4u64));
    /// four_div.div2();
    /// assert_eq!(two, four_div);
    ///
    /// // Edge-Case
    /// let mut zero = B::from(0u64);
    /// zero.div2();
    /// assert_eq!(zero, B::from(0u64));
    ///
    /// let mut one = B::from(1u64);
    /// one.div2();
    /// assert_eq!(one, B::from(0u64));
    /// ```
    fn div2(&mut self);

    /// Performs a rightwise bitshift of this number by some amount.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut thirty_two_div) = (B::from(1u64), B::from(32u64));
    /// thirty_two_div.divn(5);
    /// assert_eq!(one, thirty_two_div);
    ///
    /// // Edge-Case
    /// let mut arr: [bool; 64] = [false; 64];
    /// arr[4] = true;
    /// let mut div = B::from_bits_le(&arr);
    /// div.divn(5);
    /// assert_eq!(div, B::from(0u64));
    /// ```
    #[deprecated(since = "0.4.2", note = "please use the operator `>>` instead")]
    fn divn(&mut self, amt: u32);

    /// Returns true iff this number is odd.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut one = B::from(1u64);
    /// assert!(one.is_odd());
    /// ```
    fn is_odd(&self) -> bool;

    /// Returns true iff this number is even.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut two = B::from(2u64);
    /// assert!(two.is_even());
    /// ```
    fn is_even(&self) -> bool;

    /// Returns true iff this number is zero.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut zero = B::from(0u64);
    /// assert!(zero.is_zero());
    /// ```
    fn is_zero(&self) -> bool;

    /// Returns true iff this number is one.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut one = B::from(1u64);
    /// assert!(one.is_one());
    /// ```
    fn is_one(&self) -> bool;

    /// Compute the minimum number of bits needed to encode this number.
    /// # Example
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let zero = B::from(0u64);
    /// assert_eq!(zero.num_bits(), 0);
    /// let one = B::from(1u64);
    /// assert_eq!(one.num_bits(), 1);
    /// let max = B::from(u64::MAX);
    /// assert_eq!(max.num_bits(), 64);
    /// let u32_max = B::from(u32::MAX as u64);
    /// assert_eq!(u32_max.num_bits(), 32);
    /// ```
    fn num_bits(&self) -> u32;

    /// Compute the `i`-th bit of `self`.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut one = B::from(1u64);
    /// assert!(one.get_bit(0));
    /// assert!(!one.get_bit(1));
    /// ```
    fn get_bit(&self, i: usize) -> bool;

    /// Returns the big integer representation of a given big endian boolean
    /// array.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut arr: [bool; 64] = [false; 64];
    /// arr[63] = true;
    /// let mut one = B::from(1u64);
    /// assert_eq!(B::from_bits_be(&arr), one);
    /// ```
    fn from_bits_be(bits: &[bool]) -> Self;

    /// Returns the big integer representation of a given little endian boolean
    /// array.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut arr: [bool; 64] = [false; 64];
    /// arr[0] = true;
    /// let mut one = B::from(1u64);
    /// assert_eq!(B::from_bits_le(&arr), one);
    /// ```
    fn from_bits_le(bits: &[bool]) -> Self;

    /// Returns the bit representation in a big endian boolean array,
    /// with leading zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::from(1u64);
    /// let arr = one.to_bits_be();
    /// let mut vec = vec![false; 64];
    /// vec[63] = true;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bits_be(&self) -> Vec<bool> {
        BitIteratorBE::new(self).collect::<Vec<_>>()
    }

    /// Returns the bit representation in a little endian boolean array,
    /// with trailing zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::from(1u64);
    /// let arr = one.to_bits_le();
    /// let mut vec = vec![false; 64];
    /// vec[0] = true;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bits_le(&self) -> Vec<bool> {
        BitIteratorLE::new(self).collect::<Vec<_>>()
    }

    /// Returns the byte representation in a big endian byte array,
    /// with leading zeros.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::from(1u64);
    /// let arr = one.to_bytes_be();
    /// let mut vec = vec![0; 8];
    /// vec[7] = 1;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bytes_be(&self) -> Vec<u8>;

    /// Returns the byte representation in a little endian byte array,
    /// with trailing zeros.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::from(1u64);
    /// let arr = one.to_bytes_le();
    /// let mut vec = vec![0; 8];
    /// vec[0] = 1;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bytes_le(&self) -> Vec<u8>;

    /// Returns the windowed non-adjacent form of `self`, for a window of size `w`.
    fn find_wnaf(&self, w: usize) -> Option<Vec<i64>> {
        // w > 2 due to definition of wNAF, and w < 64 to make sure that `i64`
        // can fit each signed digit
        if (2..64).contains(&w) {
            let mut res = vec![];
            let mut e = *self;

            while !e.is_zero() {
                let z: i64;
                if e.is_odd() {
                    z = signed_mod_reduction(e.as_ref()[0], 1 << w);
                    if z >= 0 {
                        e.sub_with_borrow(&Self::from(z as u64));
                    } else {
                        e.add_with_carry(&Self::from((-z) as u64));
                    }
                } else {
                    z = 0;
                }
                res.push(z);
                e.div2();
            }

            Some(res)
        } else {
            None
        }
    }
}

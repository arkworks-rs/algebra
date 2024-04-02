use crate::{
    bits::{BitIteratorBE, BitIteratorLE},
    const_for,
};
#[allow(unused)]
use ark_ff_macros::unroll_for_loops;
use super::*;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::Borrow,
    hash::Hash,
    fmt::{Debug, Display, UpperHex},
    io::{Read, Write},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
        ShrAssign,
    },
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    str::FromStr,
};
use num_bigint::BigUint;
use zeroize::Zeroize;


#[derive(Copy, Clone, PartialEq, Eq, Hash, Zeroize)]
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
        let mut i = ($a.num_bits() - 1) as isize;
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

    /// Compute `-self^{-1}` mod 2^64.
    pub const fn montgomery_inv(&self) -> u64 {
        // We compute this as follows.
        // First, MODULUS mod 2^64 is just the lower 64 bits of MODULUS.
        // Hence MODULUS mod 2^64 = MODULUS.0[0] mod 2^64.
        //
        // Next, computing the inverse mod 2^64 involves exponentiating by
        // the multiplicative group order, which is euler_totient(2^64) - 1.
        // Now, euler_totient(2^64) = 1 << 63, and so
        // euler_totient(2^64) - 1 = (1 << 63) - 1 = 1111111... (63 digits).
        // We compute this powering via standard square and multiply.
        let mut inv = 1u64;
        crate::const_for!((_i in 0..63) {
            // Square
            inv = inv.wrapping_mul(inv);
            // Multiply
            inv = inv.wrapping_mul(self.0[0]);
        });
        inv.wrapping_neg()
    }

    pub const fn msb(&self) -> bool {
        self.0[N - 1] >> 63 == 1
    }

    pub const fn plus_one_div_four(&self) -> Option<Self> {
        if self.mod_4() == 3 {
            let (modulus_plus_one, carry) = self.const_add_with_carry(&BigInt::<N>::one());
            let mut result = modulus_plus_one.divide_by_2_round_down();
            // Since modulus_plus_one is even, dividing by 2 results in a MSB of 0.
            // Thus we can set MSB to `carry` to get the correct result of (MODULUS + 1) // 2:
            result.0[N - 1] |= (carry as u64) << 63;
            Some(result.divide_by_2_round_down())
        } else {
            None
        }
    }
}

impl<const N: usize> BigInteger for BigInt<N> {
    const BIT_SIZE: usize = N * 64;

    const ZERO: Self = Self::zero();
    
    const ONE: Self = Self::one();

    #[unroll_for_loops(6)]
    #[inline]
    fn add_with_carry(&mut self, other: &Self) -> bool {
        let mut carry = 0;

        for i in 0..N {
            carry = arithmetic::adc_for_add_with_carry(&mut self.0[i], other.0[i], carry);
        }

        carry != 0
    }

    #[unroll_for_loops(6)]
    #[inline]
    fn sub_with_borrow(&mut self, other: &Self) -> bool {
        let mut borrow = 0;

        for i in 0..N {
            borrow = arithmetic::sbb_for_sub_with_borrow(&mut self.0[i], other.0[i], borrow);
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
    fn mul(&self, other: &Self) -> (Self, Self) {
        if self.is_zero() || other.is_zero() {
            let zero = Self::zero();
            return (zero, zero);
        }

        let mut r = crate::const_helpers::MulBuffer::<N>::zeroed();

        let mut carry = 0;

        for i in 0..N {
            for j in 0..N {
                r[i + j] = mac_with_carry!(r[i + j], self.0[i], other.0[j], &mut carry);
            }
            r.b1[i] = carry;
            carry = 0;
        }

        (Self(r.b0), Self(r.b1))
    }

    #[inline]
    fn mul_low(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }

        let mut res = Self::zero();
        let mut carry = 0;

        for i in 0..N {
            for j in 0..(N - i) {
                res.0[i + j] = mac_with_carry!(res.0[i + j], self.0[i], other.0[j], &mut carry);
            }
            carry = 0;
        }

        res
    }

    #[inline]
    fn mul_high(&self, other: &Self) -> Self {
        self.mul(other).1
    }

    #[inline]
    fn div2(&mut self) {
        let mut t = 0;
        for a in self.0.iter_mut().rev() {
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
        let mut bits = bits.to_vec();
        bits.reverse();
        Self::from_bits_le(&bits)
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
    
    fn bits_le_iter(&self) -> impl Iterator<Item = bool> {
        BitIteratorLE::new(self)
    }
    
    fn bits_be_iter(&self) -> impl Iterator<Item = bool> {
        BitIteratorBE::new(self)
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
    
    #[inline]
    fn bytes_be_iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().flat_map(|limb| limb.to_le_bytes()).rev()
    }

    #[inline]
    fn bytes_le_iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().flat_map(|limb| limb.to_le_bytes())
    }
    
    fn from_bytes_le_iter(bytes: impl Iterator<Item = u8>) -> Self {
        let mut res = Self::zero();
        for (i, byte) in bytes.enumerate() {
            res.0[i / 8] |= (byte as u64) << (8 * (i % 8));
        }
        res
    }

    fn from_bytes_be_iter(bytes: impl Iterator<Item = u8>) -> Self {
        let mut res = Self::zero();
        for (i, byte) in bytes.enumerate() {
            res.0[(N - 1) - (i / 8)] |= (byte as u64) << (8 * (i % 8));
        }
        res
    }
 
    
    fn clear_msbs(&mut self, n: usize) {
        let n_limb = n / 64;
        let n_bit = n % 64;
        if n_limb < N {
            self.0[n_limb] &= u64::MAX >> (64 - n_bit);
            for limb in &mut self.0[(n_limb + 1)..] {
                *limb = 0;
            }
        }
    }
    
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

impl<const N: usize> UpperHex for BigInt<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:016X}", BigUint::from(*self))
    }
}

impl<const N: usize> Debug for BigInt<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", BigUint::from(*self))
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

impl<const N: usize> From<bool> for BigInt<N> {
    #[inline]
    fn from(val: bool) -> BigInt<N> {
        Self::from(val as u8)
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

impl<const N: usize> FromStr for BigInt<N> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let biguint = BigUint::from_str(s).map_err(|_| ())?;
        Self::try_from(biguint)
    }
}

impl<const N: usize> From<BigInt<N>> for BigUint {
    #[inline]
    fn from(val: BigInt<N>) -> num_bigint::BigUint {
        BigUint::from_bytes_le(&val.to_bytes_le())
    }
}

impl<const N: usize> From<BigInt<N>> for num_bigint::BigInt {
    #[inline]
    fn from(val: BigInt<N>) -> num_bigint::BigInt {
        use num_bigint::Sign;
        let sign = if val.is_zero() {
            Sign::NoSign
        } else {
            Sign::Plus
        };
        num_bigint::BigInt::from_bytes_le(sign, &val.to_bytes_le())
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
            return;
        }

        while rhs >= 64 {
            let mut t = 0;
            for limb in self.0.iter_mut().rev() {
                core::mem::swap(&mut t, limb);
            }
            rhs -= 64;
        }

        if rhs > 0 {
            let mut t = 0;
            for a in self.0.iter_mut().rev() {
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

impl<const N: usize> Rem<u64> for BigInt<N> {
    type Output = u64;

    fn rem(self, other: u64) -> Self::Output {
        let other = u128::from(other);
        let mut limb_size_mod_other = (1u128 << 64) % other;
        let mut result = 0;
        let mut multiplier = 1;
        for (i, limb) in self.0.into_iter().map(u128::from).enumerate() {
            result += ((limb * multiplier) % other) as u64;
            multiplier = (multiplier * limb_size_mod_other) % other;
        }
        result
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
mod tests {
    use super::tests::*;
    #[test]
    fn test_biginteger64() {
        use crate::biginteger::BigInteger64 as B;
        test_biginteger(B::new([u64::MAX; 1]), B::new([0u64; 1]));
    }

    #[test]
    fn test_biginteger128() {
        use crate::biginteger::BigInteger128 as B;
        test_biginteger(B::new([u64::MAX; 2]), B::new([0u64; 2]));
    }

    #[test]
    fn test_biginteger256() {
        use crate::biginteger::BigInteger256 as B;
        test_biginteger(B::new([u64::MAX; 4]), B::new([0u64; 4]));
    }

    #[test]
    fn test_biginteger384() {
        use crate::biginteger::BigInteger384 as B;
        test_biginteger(B::new([u64::MAX; 6]), B::new([0u64; 6]));
    }

    #[test]
    fn test_biginteger448() {
        use crate::biginteger::BigInteger448 as B;
        test_biginteger(B::new([u64::MAX; 7]), B::new([0u64; 7]));
    }

    #[test]
    fn test_biginteger768() {
        use crate::biginteger::BigInteger768 as B;
        test_biginteger(B::new([u64::MAX; 12]), B::new([0u64; 12]));
    }

    #[test]
    fn test_biginteger832() {
        use crate::biginteger::BigInteger832 as B;
        test_biginteger(B::new([u64::MAX; 13]), B::new([0u64; 13]));
    }

}
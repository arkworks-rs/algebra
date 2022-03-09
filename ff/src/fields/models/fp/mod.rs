use core::iter;

use ark_serialize::{
    buffer_byte_size, CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, EmptyFlags, Flags, SerializationError,
};
use ark_std::{
    cmp::{Ord, Ordering, PartialOrd},
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
    One, Zero,
};

#[macro_use]
mod montgomery_backend;
pub use montgomery_backend::*;

use crate::{
    BigInt, BigInteger, FftField, Field, FromBytes, LegendreSymbol, PrimeField, SquareRootField,
    ToBytes,
};
/// A trait that specifies the configuration of a prime field.
/// Also specifies how to perform arithmetic on field elements.
pub trait FpConfig<const N: usize>: Send + Sync + 'static + Sized {
    /// The modulus of the field.
    const MODULUS: crate::BigInt<N>;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<Self, N>;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp<Self, N>;

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp<Self, N>;

    /// Let `N` be the size of the multiplicative group defined by the field.
    /// Then `TWO_ADICITY` is the two-adicity of `N`, i.e. the integer `s`
    /// such that `N = 2^s * t` for some odd integer `t`.
    const TWO_ADICITY: u32;

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp<Self, N>;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)) Used for mixed-radix
    /// FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<Self, N>> = None;

    /// Set a += b.
    fn add_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>);

    /// Set a -= b.
    fn sub_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>);

    /// Set a = a + a.
    fn double_in_place(a: &mut Fp<Self, N>);

    /// Set a *= b.
    fn mul_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>);

    /// Set a *= b.
    fn square_in_place(a: &mut Fp<Self, N>);

    /// Compute a^{-1} if `a` is not zero.
    fn inverse(a: &Fp<Self, N>) -> Option<Fp<Self, N>>;

    /// Compute the square root of a, if it exists.
    fn square_root(a: &Fp<Self, N>) -> Option<Fp<Self, N>> {
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        // Actually this is just normal Tonelli-Shanks; since [`Self::GENERATOR`]
        // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
        // is also a quadratic non-residue (since `t` is odd).
        if a.is_zero() {
            return Some(Fp::zero());
        }
        // Try computing the square root (x at the end of the algorithm)
        // Check at the end of the algorithm if x was a square root
        // Begin Tonelli-Shanks
        let mut z = Fp::TWO_ADIC_ROOT_OF_UNITY;
        let mut w = a.pow(Fp::<Self, N>::TRACE_MINUS_ONE_DIV_TWO);
        let mut x = w * a;
        let mut b = x * &w;

        let mut v = Self::TWO_ADICITY as usize;

        while !b.is_one() {
            let mut k = 0usize;

            let mut b2k = b;
            while !b2k.is_one() {
                // invariant: b2k = b^(2^k) after entering this loop
                b2k.square_in_place();
                k += 1;
            }

            if k == (Self::TWO_ADICITY as usize) {
                // We are in the case where self^(T * 2^k) = x^(P::MODULUS - 1) = 1,
                // which means that no square root exists.
                return None;
            }
            let j = v - k;
            w = z;
            for _ in 1..j {
                w.square_in_place();
            }

            z = w.square();
            b *= &z;
            x *= &w;
            v = k;
        }
        // Is x the square root? If so, return it.
        if x.square() == *a {
            return Some(x);
        } else {
            // Consistency check that if no square root is found,
            // it is because none exists.
            #[cfg(debug_assertions)]
            {
                use crate::fields::LegendreSymbol::*;
                if a.legendre() != QuadraticNonResidue {
                    panic!("Input has a square root per its Legendre symbol, but it was not found")
                }
            }
            None
        }
    }

    /// Construct a field element from an integer in the range `0..(Self::MODULUS - 1)`.
    /// Returns `None` if the integer is outside this range.
    fn from_bigint(other: BigInt<N>) -> Option<Fp<Self, N>>;

    /// Convert a field element to an integer in the range `0..(Self::MODULUS - 1)`.
    fn into_bigint(other: Fp<Self, N>) -> BigInt<N>;
}

/// Represents an element of the prime field F_p, where `p == P::MODULUS`.
/// This type can represent elements in any field of size at most N * 64 bits.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Copy(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
pub struct Fp<P, const N: usize>(
    pub BigInt<N>,
    #[derivative(Debug = "ignore")]
    #[doc(hidden)]
    pub PhantomData<P>,
);

pub type Fp64<P> = Fp<P, 1>;
pub type Fp128<P> = Fp<P, 2>;
pub type Fp192<P> = Fp<P, 3>;
pub type Fp256<P> = Fp<P, 4>;
pub type Fp320<P> = Fp<P, 5>;
pub type Fp384<P> = Fp<P, 6>;
pub type Fp448<P> = Fp<P, 7>;
pub type Fp512<P> = Fp<P, 8>;
pub type Fp576<P> = Fp<P, 9>;
pub type Fp640<P> = Fp<P, 10>;
pub type Fp704<P> = Fp<P, 11>;
pub type Fp768<P> = Fp<P, 12>;
pub type Fp832<P> = Fp<P, 13>;

impl<P, const N: usize> Fp<P, N> {
    /// Construct a new prime element directly from its underlying
    /// [`struct@BigInt`] data type.
    #[inline]
    pub const fn new(element: BigInt<N>) -> Self {
        Self(element, PhantomData)
    }
}

impl<P: FpConfig<N>, const N: usize> Fp<P, N> {
    #[inline(always)]
    pub(crate) fn is_less_than_modulus(&self) -> bool {
        self.0 < P::MODULUS
    }

    #[inline]
    fn subtract_modulus(&mut self) {
        if !self.is_less_than_modulus() {
            self.0.sub_with_borrow(&Self::MODULUS);
        }
    }

    fn num_bits_to_shave() -> usize {
        64 * N - (Self::MODULUS_BIT_SIZE as usize)
    }
}

impl<P, const N: usize> ark_std::fmt::Debug for Fp<P, N> {
    fn fmt(&self, f: &mut ark_std::fmt::Formatter<'_>) -> ark_std::fmt::Result {
        ark_std::fmt::Debug::fmt(&self.0, f)
    }
}

impl<P: FpConfig<N>, const N: usize> Zero for Fp<P, N> {
    #[inline]
    fn zero() -> Self {
        P::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == P::ZERO
    }
}

impl<P: FpConfig<N>, const N: usize> One for Fp<P, N> {
    #[inline]
    fn one() -> Self {
        P::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == P::ONE
    }
}

impl<P: FpConfig<N>, const N: usize> Field for Fp<P, N> {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    fn extension_degree() -> u64 {
        1
    }

    fn to_base_prime_field_elements(&self) -> Self::BasePrimeFieldIter {
        iter::once(*self)
    }

    fn from_base_prime_field_elems(elems: &[Self::BasePrimeField]) -> Option<Self> {
        if elems.len() != (Self::extension_degree() as usize) {
            return None;
        }
        Some(elems[0])
    }

    #[inline]
    fn double(&self) -> Self {
        let mut temp = *self;
        temp.double_in_place();
        temp
    }

    #[inline]
    fn double_in_place(&mut self) -> &mut Self {
        P::double_in_place(self);
        self
    }

    #[inline]
    fn characteristic() -> &'static [u64] {
        P::MODULUS.as_ref()
    }

    #[inline]
    fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        if F::BIT_SIZE > 8 {
            return None;
        } else {
            let shave_bits = Self::num_bits_to_shave();
            let mut result_bytes = crate::const_helpers::SerBuffer::<N>::zeroed();
            // Copy the input into a temporary buffer.
            result_bytes.copy_from_u8_slice(bytes);
            // This mask retains everything in the last limb
            // that is below `P::MODULUS_BIT_SIZE`.
            let last_limb_mask = (u64::MAX >> shave_bits).to_le_bytes();
            let mut last_bytes_mask = [0u8; 9];
            last_bytes_mask[..8].copy_from_slice(&last_limb_mask);

            // Length of the buffer containing the field element and the flag.
            let output_byte_size = buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE);
            // Location of the flag is the last byte of the serialized
            // form of the field element.
            let flag_location = output_byte_size - 1;

            // At which byte is the flag located in the last limb?
            let flag_location_in_last_limb = flag_location - (8 * (N - 1));

            // Take all but the last 9 bytes.
            let last_bytes = result_bytes.last_n_plus_1_bytes_mut();

            // The mask only has the last `F::BIT_SIZE` bits set
            let flags_mask = u8::MAX.checked_shl(8 - (F::BIT_SIZE as u32)).unwrap_or(0);

            // Mask away the remaining bytes, and try to reconstruct the
            // flag
            let mut flags: u8 = 0;
            for (i, (b, m)) in last_bytes.zip(&last_bytes_mask).enumerate() {
                if i == flag_location_in_last_limb {
                    flags = *b & flags_mask
                }
                *b &= m;
            }
            Self::deserialize(&result_bytes.as_slice()[..(N * 8)])
                .ok()
                .and_then(|f| F::from_u8(flags).map(|flag| (f, flag)))
        }
    }

    #[inline]
    fn square(&self) -> Self {
        let mut temp = self.clone();
        temp.square_in_place();
        temp
    }

    fn square_in_place(&mut self) -> &mut Self {
        P::square_in_place(self);
        self
    }

    #[inline]
    fn inverse(&self) -> Option<Self> {
        P::inverse(&self)
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        if let Some(inverse) = self.inverse() {
            *self = inverse;
            Some(self)
        } else {
            None
        }
    }

    /// The Frobenius map has no effect in a prime field.
    #[inline]
    fn frobenius_map(&mut self, _: usize) {}
}

impl<P: FpConfig<N>, const N: usize> PrimeField for Fp<P, N> {
    type BigInt = BigInt<N>;
    const MODULUS: Self::BigInt = P::MODULUS;
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = P::MODULUS.divide_by_2_round_down();
    const MODULUS_BIT_SIZE: u32 = P::MODULUS.const_num_bits();
    const TRACE: Self::BigInt = P::MODULUS.two_adic_coefficient();
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = Self::TRACE.divide_by_2_round_down();

    #[inline]
    fn from_bigint(r: BigInt<N>) -> Option<Self> {
        P::from_bigint(r)
    }

    fn into_bigint(&self) -> BigInt<N> {
        P::into_bigint(*self)
    }
}

impl<P: FpConfig<N>, const N: usize> FftField for Fp<P, N> {
    const GENERATOR: Self = P::GENERATOR;
    const TWO_ADICITY: u32 = P::TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self = P::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = P::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = P::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = P::LARGE_SUBGROUP_ROOT_OF_UNITY;
}

impl<P: FpConfig<N>, const N: usize> SquareRootField for Fp<P, N> {
    #[inline]
    fn legendre(&self) -> LegendreSymbol {
        use crate::fields::LegendreSymbol::*;

        // s = self^((MODULUS - 1) // 2)
        let s = self.pow(Self::MODULUS_MINUS_ONE_DIV_TWO);
        if s.is_zero() {
            Zero
        } else if s.is_one() {
            QuadraticResidue
        } else {
            QuadraticNonResidue
        }
    }

    #[inline]
    fn sqrt(&self) -> Option<Self> {
        P::square_root(self)
    }

    fn sqrt_in_place(&mut self) -> Option<&mut Self> {
        (*self).sqrt().map(|sqrt| {
            *self = sqrt;
            self
        })
    }
}

/// Note that this implementation of `Ord` compares field elements viewing
/// them as integers in the range 0, 1, ..., P::MODULUS - 1. However, other
/// implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `Ord` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: FpConfig<N>, const N: usize> Ord for Fp<P, N> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }
}

/// Note that this implementation of `PartialOrd` compares field elements viewing
/// them as integers in the range 0, 1, ..., `P::MODULUS` - 1. However, other
/// implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `PartialOrd` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: FpConfig<N>, const N: usize> PartialOrd for Fp<P, N> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: FpConfig<N>, const N: usize> From<u128> for Fp<P, N> {
    fn from(other: u128) -> Self {
        let mut default_int = BigInt::default();
        if N == 1 {
            default_int.0[0] = (other % u128::from(P::MODULUS.0[0])) as u64;
        } else {
            let upper = (other >> 64) as u64;
            let lower = ((other << 64) >> 64) as u64;
            default_int.0[0] = lower;
            default_int.0[1] = upper;
        }
        Self::from_bigint(default_int).unwrap()
    }
}

impl<P: FpConfig<N>, const N: usize> From<i128> for Fp<P, N> {
    fn from(other: i128) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<bool> for Fp<P, N> {
    fn from(other: bool) -> Self {
        if N == 1 {
            Self::from_bigint(BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
        } else {
            Self::from_bigint(BigInt::from(u64::from(other))).unwrap()
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<u64> for Fp<P, N> {
    fn from(other: u64) -> Self {
        if N == 1 {
            Self::from_bigint(BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
        } else {
            Self::from_bigint(BigInt::from(u64::from(other))).unwrap()
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<i64> for Fp<P, N> {
    fn from(other: i64) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<u32> for Fp<P, N> {
    fn from(other: u32) -> Self {
        if N == 1 {
            Self::from_bigint(BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
        } else {
            Self::from_bigint(BigInt::from(u32::from(other))).unwrap()
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<i32> for Fp<P, N> {
    fn from(other: i32) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<u16> for Fp<P, N> {
    fn from(other: u16) -> Self {
        if N == 1 {
            Self::from_bigint(BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
        } else {
            Self::from_bigint(BigInt::from(u16::from(other))).unwrap()
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<i16> for Fp<P, N> {
    fn from(other: i16) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<u8> for Fp<P, N> {
    fn from(other: u8) -> Self {
        if N == 1 {
            Self::from_bigint(BigInt::from(u64::from(other) % P::MODULUS.0[0])).unwrap()
        } else {
            Self::from_bigint(BigInt::from(u8::from(other))).unwrap()
        }
    }
}

impl<P: FpConfig<N>, const N: usize> From<i8> for Fp<P, N> {
    fn from(other: i8) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig<N>, const N: usize> ark_std::rand::distributions::Distribution<Fp<P, N>>
    for ark_std::rand::distributions::Standard
{
    #[inline]
    fn sample<R: ark_std::rand::Rng + ?Sized>(&self, rng: &mut R) -> Fp<P, N> {
        loop {
            let mut tmp = Fp::new(rng.sample(ark_std::rand::distributions::Standard));
            let shave_bits = Fp::<P, N>::num_bits_to_shave();
            // Mask away the unused bits at the beginning.
            assert!(shave_bits <= 64);
            let mask = if shave_bits == 64 {
                0
            } else {
                core::u64::MAX >> shave_bits
            };
            tmp.0 .0.last_mut().map(|val| *val &= mask);

            if tmp.is_less_than_modulus() {
                return tmp;
            }
        }
    }
}

impl<P: FpConfig<N>, const N: usize> CanonicalSerializeWithFlags for Fp<P, N> {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }

        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`. If `F::BIT_SIZE < 8`,
        // this is at most `N * 8 + 1`
        let output_byte_size = buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE);

        // Write out `self` to a temporary buffer.
        // The size of the buffer is $byte_size + 1 because `F::BIT_SIZE`
        // is at most 8 bits.
        let mut bytes = crate::const_helpers::SerBuffer::zeroed();
        bytes.copy_from_u64_slice(&self.into_bigint().0);
        // Mask out the bits of the last byte that correspond to the flag.
        bytes[output_byte_size - 1] |= flags.u8_bitmask();

        bytes.write_up_to(writer, output_byte_size)?;
        Ok(())
    }

    // Let `m = 8 * n` for some `n` be the smallest multiple of 8 greater
    // than `P::MODULUS_BIT_SIZE`.
    // If `(m - P::MODULUS_BIT_SIZE) >= F::BIT_SIZE` , then this method returns `n`;
    // otherwise, it returns `n + 1`.
    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE)
    }
}

impl<P: FpConfig<N>, const N: usize> CanonicalSerialize for Fp<P, N> {
    #[inline]
    fn serialize<W: ark_std::io::Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.serialized_size_with_flags::<EmptyFlags>()
    }
}

impl<P: FpConfig<N>, const N: usize> CanonicalDeserializeWithFlags for Fp<P, N> {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }
        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`.
        let output_byte_size = Self::zero().serialized_size_with_flags::<F>();

        let mut masked_bytes = crate::const_helpers::SerBuffer::zeroed();
        masked_bytes.read_exact_up_to(reader, output_byte_size)?;
        let flags = F::from_u8_remove_flags(&mut masked_bytes[output_byte_size - 1])
            .ok_or(SerializationError::UnexpectedFlags)?;

        let self_integer = masked_bytes.to_bigint();
        Self::from_bigint(self_integer)
            .map(|v| (v, flags))
            .ok_or(SerializationError::InvalidData)
    }
}

impl<P: FpConfig<N>, const N: usize> CanonicalDeserialize for Fp<P, N> {
    fn deserialize<R: ark_std::io::Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_flags::<R, EmptyFlags>(reader).map(|(r, _)| r)
    }
}

impl<P: FpConfig<N>, const N: usize> ToBytes for Fp<P, N> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> IoResult<()> {
        self.into_bigint().write(writer)
    }
}

impl<P: FpConfig<N>, const N: usize> FromBytes for Fp<P, N> {
    #[inline]
    fn read<R: Read>(r: R) -> IoResult<Self> {
        BigInt::read(r)
            .and_then(|b| Fp::from_bigint(b).ok_or(crate::error("FromBytes::read failed")))
    }
}

impl<P: FpConfig<N>, const N: usize> FromStr for Fp<P, N> {
    type Err = ();

    /// Interpret a string of numbers as a (congruent) prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err(());
        }

        if s == "0" {
            return Ok(Self::zero());
        }

        let mut res = Self::zero();

        let ten = Self::from(BigInt::from(10u8));

        let mut first_digit = true;

        for c in s.chars() {
            match c.to_digit(10) {
                Some(c) => {
                    if first_digit {
                        if c == 0 {
                            return Err(());
                        }

                        first_digit = false;
                    }

                    res.mul_assign(&ten);
                    let digit = Self::from(u64::from(c));
                    res.add_assign(&digit);
                },
                None => {
                    return Err(());
                },
            }
        }
        if !res.is_less_than_modulus() {
            Err(())
        } else {
            Ok(res)
        }
    }
}

/// Outputs a string containing the value of `self`, chunked up into
/// 64-bit limbs.
impl<P: FpConfig<N>, const N: usize> Display for Fp<P, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, stringify!(Fp "({})"), self.into_bigint())
    }
}

impl<P: FpConfig<N>, const N: usize> Neg for Fp<P, N> {
    type Output = Self;
    #[inline]
    #[must_use]
    fn neg(self) -> Self {
        if !self.is_zero() {
            let mut tmp = P::MODULUS;
            tmp.sub_with_borrow(&self.0);
            Fp::new(tmp)
        } else {
            self
        }
    }
}

impl<'a, P: FpConfig<N>, const N: usize> Add<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self.add_assign(other);
        self
    }
}

impl<'a, P: FpConfig<N>, const N: usize> Sub<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self.sub_assign(other);
        self
    }
}

impl<'a, P: FpConfig<N>, const N: usize> Mul<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self.mul_assign(other);
        self
    }
}

impl<'a, P: FpConfig<N>, const N: usize> Div<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    /// Returns `self * other.inverse()` if `other.inverse()` is `Some`, and
    /// panics otherwise.
    #[inline]
    fn div(mut self, other: &Self) -> Self {
        self.mul_assign(&other.inverse().unwrap());
        self
    }
}

impl<'a, P: FpConfig<N>, const N: usize> AddAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        P::add_assign(self, other)
    }
}

impl<'a, P: FpConfig<N>, const N: usize> SubAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        P::sub_assign(self, other);
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::Add<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self.add_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::Add<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self.add_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::Sub<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self.sub_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::Sub<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self.sub_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::iter::Sum<Self> for Fp<P, N> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::iter::Sum<&'a Self> for Fp<P, N> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::AddAssign<Self> for Fp<P, N> {
    fn add_assign(&mut self, other: Self) {
        self.add_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::SubAssign<Self> for Fp<P, N> {
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::AddAssign<&'a mut Self> for Fp<P, N> {
    fn add_assign(&mut self, other: &'a mut Self) {
        self.add_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::SubAssign<&'a mut Self> for Fp<P, N> {
    fn sub_assign(&mut self, other: &'a mut Self) {
        self.sub_assign(&*other)
    }
}

impl<'a, P: FpConfig<N>, const N: usize> MulAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn mul_assign(&mut self, other: &Self) {
        P::mul_assign(self, other)
    }
}

/// Computes `self *= other.inverse()` if `other.inverse()` is `Some`, and
/// panics otherwise.
impl<'a, P: FpConfig<N>, const N: usize> DivAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::Mul<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: Self) -> Self {
        self.mul_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::Div<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::Mul<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self.mul_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::Div<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::iter::Product<Self> for Fp<P, N> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::iter::Product<&'a Self> for Fp<P, N> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::MulAssign<Self> for Fp<P, N> {
    fn mul_assign(&mut self, other: Self) {
        self.mul_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::DivAssign<&'a mut Self> for Fp<P, N> {
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig<N>, const N: usize> core::ops::MulAssign<&'a mut Self> for Fp<P, N> {
    fn mul_assign(&mut self, other: &'a mut Self) {
        self.mul_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig<N>, const N: usize> core::ops::DivAssign<Self> for Fp<P, N> {
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<P: FpConfig<N>, const N: usize> zeroize::Zeroize for Fp<P, N> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<P: FpConfig<N>, const N: usize> From<num_bigint::BigUint> for Fp<P, N> {
    #[inline]
    fn from(val: num_bigint::BigUint) -> Fp<P, N> {
        Fp::<P, N>::from_le_bytes_mod_order(&val.to_bytes_le())
    }
}

impl<P: FpConfig<N>, const N: usize> From<Fp<P, N>> for num_bigint::BigUint {
    #[inline]
    fn from(other: Fp<P, N>) -> Self {
        other.into_bigint().into()
    }
}

impl<P: FpConfig<N>, const N: usize> Into<BigInt<N>> for Fp<P, N> {
    fn into(self) -> BigInt<N> {
        self.into_bigint()
    }
}

impl<P: FpConfig<N>, const N: usize> From<BigInt<N>> for Fp<P, N> {
    /// Converts `Self::BigInteger` into `Self`
    fn from(int: BigInt<N>) -> Self {
        Self::from_bigint(int).unwrap()
    }
}

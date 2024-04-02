use crate::{
    AdditiveGroup, BigInteger, FftField, Field, LegendreSymbol, One, PrimeField,
    SqrtPrecomputation, Zero,
};
use ark_serialize::{
    buffer_byte_size, CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, EmptyFlags, Flags, SerializationError, Valid, Validate,
};
use ark_std::{
    cmp::*,
    fmt::{Display, Formatter, Result as FmtResult},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
    string::*,
    UniformRand,
};
use core::iter;

#[macro_use]
mod montgomery;
pub use montgomery::*;

/// A trait that specifies the configuration of a prime field.
/// Also specifies how to perform arithmetic on field elements.
pub trait FpConfig: Send + Sync + 'static + Sized {
    type BigInt: BigInteger;

    /// The modulus of the field.
    const MODULUS: Self::BigInt;

    /// The value `(MODULUS - 1) / 2`.
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt;

    /// The size of the modulus in bits.
    const MODULUS_BIT_SIZE: u32;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<Self>;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp<Self>;

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp<Self>;

    /// Let `N` be the size of the multiplicative group defined by the field.
    /// Then `TWO_ADICITY` is the two-adicity of `N`, i.e. the integer `s`
    /// such that `N = 2^s * t` for some odd integer `t`.
    const TWO_ADICITY: u32;

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp<Self>;
    
    
    /// The trace of the field is defined as the smallest odd integer `t` such that
    /// `2^s * t = p - 1`. That is, `t = (p - 1) / 2^SELF::TWO_ADICITY`.
    const TRACE: Self::BigInt;
    
    /// The value `(t - 1)/ 2`.
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)) Used for mixed-radix
    /// FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<Self>> = None;

    /// Precomputed material for use when computing square roots.
    /// Currently uses the generic Tonelli-Shanks,
    /// which works for every modulus.
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Fp<Self>>>;

    /// Set a += b.
    fn add_assign(a: &mut Fp<Self>, b: &Fp<Self>);

    /// Set a -= b.
    fn sub_assign(a: &mut Fp<Self>, b: &Fp<Self>);

    /// Set a = a + a.
    fn double_in_place(a: &mut Fp<Self>);

    /// Set a = -a;
    fn neg_in_place(a: &mut Fp<Self>);

    /// Set a *= b.
    fn mul_assign(a: &mut Fp<Self>, b: &Fp<Self>);

    /// Compute the inner product `<a, b>`.
    fn sum_of_products<const T: usize>(a: &[Fp<Self>; T], b: &[Fp<Self>; T]) -> Fp<Self>;

    /// Set a *= b.
    fn square_in_place(a: &mut Fp<Self>);

    /// Compute a^{-1} if `a` is not zero.
    fn inverse(a: &Fp<Self>) -> Option<Fp<Self>>;

    /// Construct a field element from an integer in the range
    /// `0..(Self::MODULUS - 1)`. Returns `None` if the integer is outside
    /// this range.
    fn from_bigint(other: Self::BigInt) -> Option<Fp<Self>>;

    /// Convert a field element to an integer in the range `0..(Self::MODULUS -
    /// 1)`.
    fn into_bigint(other: Fp<Self>) -> Self::BigInt;
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
pub struct Fp<P: FpConfig>(
    /// Contains the element in Montgomery form for efficient multiplication.
    /// To convert an element to a [`BigInt`](struct@BigInt), use `into_bigint` or `into`.
    #[doc(hidden)]
    pub P::BigInt,
);

impl<P: FpConfig> Fp<P> {
    #[doc(hidden)]
    #[inline]
    pub fn is_geq_modulus(&self) -> bool {
        self.0 >= P::MODULUS
    }

    #[inline]
    fn subtract_modulus(&mut self) {
        if self.is_geq_modulus() {
            self.0.sub_with_borrow(&Self::MODULUS);
        }
    }

    #[inline]
    fn subtract_modulus_with_carry(&mut self, carry: bool) {
        if carry || self.is_geq_modulus() {
            self.0.sub_with_borrow(&Self::MODULUS);
        }
    }

    fn num_bits_to_shave() -> usize {
        P::BigInt::BIT_SIZE - (Self::MODULUS_BIT_SIZE as usize)
    }
}

impl<P: FpConfig> ark_std::fmt::Debug for Fp<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> ark_std::fmt::Result {
        ark_std::fmt::Debug::fmt(&self.into_bigint(), f)
    }
}

impl<P: FpConfig> Zero for Fp<P> {
    #[inline]
    fn zero() -> Self {
        P::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == P::ZERO
    }
}

impl<P: FpConfig> One for Fp<P> {
    #[inline]
    fn one() -> Self {
        P::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == P::ONE
    }
}

impl<P: FpConfig> AdditiveGroup for Fp<P> {
    type Scalar = Self;
    const ZERO: Self = P::ZERO;

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
    fn neg_in_place(&mut self) -> &mut Self {
        P::neg_in_place(self);
        self
    }
}

impl<P: FpConfig> Field for Fp<P> {
    type BasePrimeField = Self;
    type BasePrimeFieldIter = iter::Once<Self::BasePrimeField>;

    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> = P::SQRT_PRECOMP;
    const ONE: Self = P::ONE;

    fn extension_degree() -> u64 {
        1
    }

    fn from_base_prime_field(elem: Self::BasePrimeField) -> Self {
        elem
    }

    fn to_base_prime_field_elements(&self) -> Self::BasePrimeFieldIter {
        iter::once(*self)
    }

    fn from_base_prime_field_elems(
        elems: impl IntoIterator<Item = Self::BasePrimeField>,
    ) -> Option<Self> {
        let mut elems = elems.into_iter();
        let elem = elems.next()?;
        if elems.next().is_some() {
            return None;
        }
        Some(elem)
    }

    #[inline]
    fn characteristic() -> impl BigInteger {
        P::MODULUS
    }

    #[inline]
    fn sum_of_products<const T: usize>(a: &[Self; T], b: &[Self; T]) -> Self {
        P::sum_of_products(a, b)
    }

    #[inline]
    fn square(&self) -> Self {
        let mut temp = *self;
        temp.square_in_place();
        temp
    }

    fn square_in_place(&mut self) -> &mut Self {
        P::square_in_place(self);
        self
    }

    #[inline]
    fn inverse(&self) -> Option<Self> {
        P::inverse(self)
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
    fn frobenius_map_in_place(&mut self, _: usize) {}

    #[inline]
    fn legendre(&self) -> LegendreSymbol {
        use crate::fields::LegendreSymbol::*;

        // s = self^((MODULUS - 1) // 2)
        let s = self.pow(Self::MODULUS_MINUS_ONE_DIV_TWO.bits_le_iter());
        if s.is_zero() {
            Zero
        } else if s.is_one() {
            QuadraticResidue
        } else {
            QuadraticNonResidue
        }
    }
}

impl<P: FpConfig> PrimeField for Fp<P> {
    type BigInt = P::BigInt;
    const MODULUS: Self::BigInt = P::MODULUS;
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = P::MODULUS_MINUS_ONE_DIV_TWO;
    const MODULUS_BIT_SIZE: u32 = P::MODULUS_BIT_SIZE;
    const TRACE: Self::BigInt = P::TRACE;
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = P::TRACE_MINUS_ONE_DIV_TWO;

    #[inline]
    fn from_bigint(r: Self::BigInt) -> Option<Self> {
        P::from_bigint(r)
    }

    fn into_bigint(self) -> Self::BigInt {
        P::into_bigint(self)
    }
}

impl<P: FpConfig> FftField for Fp<P> {
    const GENERATOR: Self = P::GENERATOR;
    const TWO_ADICITY: u32 = P::TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self = P::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = P::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = P::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = P::LARGE_SUBGROUP_ROOT_OF_UNITY;
}

/// Note that this implementation of `Ord` compares field elements viewing
/// them as integers in the range 0, 1, ..., P::MODULUS - 1. However, other
/// implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `Ord` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: FpConfig> Ord for Fp<P> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }
}

/// Note that this implementation of `PartialOrd` compares field elements
/// viewing them as integers in the range 0, 1, ..., `P::MODULUS` - 1. However,
/// other implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `PartialOrd` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: FpConfig> PartialOrd for Fp<P> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: FpConfig> From<u128> for Fp<P> {
    fn from(mut other: u128) -> Self {
        todo!();
        // P::BigInt::from(other).and_then(Self::from_bigint).unwrap()
    }
}

impl<P: FpConfig> From<i128> for Fp<P> {
    fn from(other: i128) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig> From<bool> for Fp<P> {
    fn from(other: bool) -> Self {
        if other {
            Self::ONE
        } else {
            Self::ZERO
        }
    }
}

impl<P: FpConfig> From<u64> for Fp<P> {
    fn from(other: u64) -> Self {
        if Self::MODULUS_BIT_SIZE > 64 {
            Self::from_bigint(P::BigInt::from(other)).unwrap()
        } else {
            todo!()
        }
    }
}

impl<P: FpConfig> From<i64> for Fp<P> {
    fn from(other: i64) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig> From<u32> for Fp<P> {
    fn from(other: u32) -> Self {
        if Self::MODULUS_BIT_SIZE > 32 {
            Self::from_bigint(P::BigInt::from(other)).unwrap()
        } else {
            todo!()
        }
    }
}

impl<P: FpConfig> From<i32> for Fp<P> {
    fn from(other: i32) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig> From<u16> for Fp<P> {
    fn from(other: u16) -> Self {
        if Self::MODULUS_BIT_SIZE > 16 {
            Self::from_bigint(P::BigInt::from(other)).unwrap()
        } else {
            todo!()
        }
    }
}

impl<P: FpConfig> From<i16> for Fp<P> {
    fn from(other: i16) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig> From<u8> for Fp<P> {
    fn from(other: u8) -> Self {
        if Self::MODULUS_BIT_SIZE > 8 {
            Self::from_bigint(P::BigInt::from(other)).unwrap()
        } else {
            todo!()
        }
    }
}

impl<P: FpConfig> From<i8> for Fp<P> {
    fn from(other: i8) -> Self {
        let abs = Self::from(other.unsigned_abs());
        if other.is_positive() {
            abs
        } else {
            -abs
        }
    }
}

impl<P: FpConfig> ark_std::rand::distributions::Distribution<Fp<P>>
    for ark_std::rand::distributions::Standard
{
    #[inline]
    fn sample<R: ark_std::rand::Rng + ?Sized>(&self, rng: &mut R) -> Fp<P> {
        loop {
            let mut tmp: P::BigInt = P::BigInt::rand(rng);
            tmp.clear_msbs(Fp::<P>::num_bits_to_shave());
            let tmp = Fp(tmp);
            if !tmp.is_geq_modulus() {
                return tmp;
            }
        }
    }
}

impl<P: FpConfig> CanonicalSerializeWithFlags for Fp<P> {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        mut writer: W,
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
        
        // If `output_byte_size` equals `N * 8 + 1`, then the flag is stored in an extra byte.
        // Otherwise, the `take` call truncates to `output_byte_size`, which is the optimal amount.
        let bytes = self.into_bigint().bytes_le_iter().chain([0u8]).take(output_byte_size);
        
        for (i, byte) in bytes.enumerate() {
            if i == output_byte_size - 1 {
                writer.write_all(&[flags.u8_bitmask() | byte])?;
            } else {
                writer.write_all(&[byte])?;
            }
        }
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

impl<P: FpConfig> CanonicalSerialize for Fp<P> {
    #[inline]
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        self.serialized_size_with_flags::<EmptyFlags>()
    }
}

impl<P: FpConfig> CanonicalDeserializeWithFlags for Fp<P> {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        mut reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }
        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`.
        let output_byte_size = buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE);
        
        let mut flags = F::default();
        let bytes = iter::repeat(())
            .take(output_byte_size)
            .enumerate()
            .map(|(i, _)| {
                let mut byte = u8::deserialize_uncompressed_unchecked(&mut reader).unwrap();
                // If we are at the last byte, we need to extract the flags
                if i == output_byte_size - 1 {
                    flags = F::from_u8_remove_flags(&mut byte).unwrap();
                } 
                byte
            });


        Self::from_bigint(P::BigInt::from_bytes_le_iter(bytes))
            .map(|v| (v, flags))
            .ok_or(SerializationError::InvalidData)
    }
}

impl<P: FpConfig> Valid for Fp<P> {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl<P: FpConfig> CanonicalDeserialize for Fp<P> {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::deserialize_with_flags::<R, EmptyFlags>(reader).map(|(r, _)| r)
    }
}

impl<P: FpConfig> FromStr for Fp<P> {
    type Err = ();

    /// Interpret a string of numbers as a (congruent) prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use num_bigint::{BigInt, BigUint};
        use num_traits::Signed;

        let modulus: BigInt = P::MODULUS.into();
        let mut a = BigInt::from_str(s).map_err(|_| ())? % &modulus;
        if a.is_negative() {
            a += modulus
        }
        BigUint::try_from(a)
            .map_err(|_| ())
            .and_then(TryFrom::try_from)
            .ok()
            .and_then(Self::from_bigint)
            .ok_or(())
    }
}

/// Outputs a string containing the value of `self`,
/// represented as a decimal without leading zeroes.
impl<P: FpConfig> Display for Fp<P> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let string = self.into_bigint().to_string();
        write!(f, "{}", string.trim_start_matches('0'))
    }
}

impl<P: FpConfig> Neg for Fp<P> {
    type Output = Self;
    #[inline]
    #[must_use]
    fn neg(mut self) -> Self {
        P::neg_in_place(&mut self);
        self
    }
}

impl<'a, P: FpConfig> Add<&'a Fp<P>> for Fp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &Self) -> Self {
        self.add_assign(other);
        self
    }
}

impl<'a, P: FpConfig> Sub<&'a Fp<P>> for Fp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &Self) -> Self {
        self.sub_assign(other);
        self
    }
}

impl<'a, P: FpConfig> Mul<&'a Fp<P>> for Fp<P> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: &Self) -> Self {
        self.mul_assign(other);
        self
    }
}

impl<'a, P: FpConfig> Div<&'a Fp<P>> for Fp<P> {
    type Output = Self;

    /// Returns `self * other.inverse()` if `other.inverse()` is `Some`, and
    /// panics otherwise.
    #[inline]
    fn div(mut self, other: &Self) -> Self {
        self.mul_assign(&other.inverse().unwrap());
        self
    }
}

impl<'a, 'b, P: FpConfig> Add<&'b Fp<P>> for &'a Fp<P> {
    type Output = Fp<P>;

    #[inline]
    fn add(self, other: &'b Fp<P>) -> Fp<P> {
        let mut result = *self;
        result.add_assign(other);
        result
    }
}

impl<'a, 'b, P: FpConfig> Sub<&'b Fp<P>> for &'a Fp<P> {
    type Output = Fp<P>;

    #[inline]
    fn sub(self, other: &Fp<P>) -> Fp<P> {
        let mut result = *self;
        result.sub_assign(other);
        result
    }
}

impl<'a, 'b, P: FpConfig> Mul<&'b Fp<P>> for &'a Fp<P> {
    type Output = Fp<P>;

    #[inline]
    fn mul(self, other: &Fp<P>) -> Fp<P> {
        let mut result = *self;
        result.mul_assign(other);
        result
    }
}

impl<'a, 'b, P: FpConfig> Div<&'b Fp<P>> for &'a Fp<P> {
    type Output = Fp<P>;

    #[inline]
    fn div(self, other: &Fp<P>) -> Fp<P> {
        let mut result = *self;
        result.div_assign(other);
        result
    }
}

impl<'a, P: FpConfig> AddAssign<&'a Self> for Fp<P> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        P::add_assign(self, other)
    }
}

impl<'a, P: FpConfig> SubAssign<&'a Self> for Fp<P> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        P::sub_assign(self, other);
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::Add<Self> for Fp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: Self) -> Self {
        self.add_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::Add<&'a mut Self> for Fp<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a mut Self) -> Self {
        self.add_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::Sub<Self> for Fp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: Self) -> Self {
        self.sub_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::Sub<&'a mut Self> for Fp<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a mut Self) -> Self {
        self.sub_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::iter::Sum<Self> for Fp<P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::iter::Sum<&'a Self> for Fp<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::AddAssign<Self> for Fp<P> {
    #[inline(always)]
    fn add_assign(&mut self, other: Self) {
        self.add_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::SubAssign<Self> for Fp<P> {
    #[inline(always)]
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::AddAssign<&'a mut Self> for Fp<P> {
    #[inline(always)]
    fn add_assign(&mut self, other: &'a mut Self) {
        self.add_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::SubAssign<&'a mut Self> for Fp<P> {
    #[inline(always)]
    fn sub_assign(&mut self, other: &'a mut Self) {
        self.sub_assign(&*other)
    }
}

impl<'a, P: FpConfig> MulAssign<&'a Self> for Fp<P> {
    fn mul_assign(&mut self, other: &Self) {
        P::mul_assign(self, other)
    }
}

/// Computes `self *= other.inverse()` if `other.inverse()` is `Some`, and
/// panics otherwise.
impl<'a, P: FpConfig> DivAssign<&'a Self> for Fp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::Mul<Self> for Fp<P> {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: Self) -> Self {
        self.mul_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::Div<Self> for Fp<P> {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: Self) -> Self {
        self.div_assign(&other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::Mul<&'a mut Self> for Fp<P> {
    type Output = Self;

    #[inline(always)]
    fn mul(mut self, other: &'a mut Self) -> Self {
        self.mul_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::Div<&'a mut Self> for Fp<P> {
    type Output = Self;

    #[inline(always)]
    fn div(mut self, other: &'a mut Self) -> Self {
        self.div_assign(&*other);
        self
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::iter::Product<Self> for Fp<P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::iter::Product<&'a Self> for Fp<P> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::MulAssign<Self> for Fp<P> {
    #[inline(always)]
    fn mul_assign(&mut self, other: Self) {
        self.mul_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::DivAssign<&'a mut Self> for Fp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpConfig> core::ops::MulAssign<&'a mut Self> for Fp<P> {
    #[inline(always)]
    fn mul_assign(&mut self, other: &'a mut Self) {
        self.mul_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpConfig> core::ops::DivAssign<Self> for Fp<P> {
    #[inline(always)]
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<P: FpConfig> zeroize::Zeroize for Fp<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<P: FpConfig> From<num_bigint::BigUint> for Fp<P> {
    #[inline]
    fn from(val: num_bigint::BigUint) -> Fp<P> {
        Fp::<P>::from_le_bytes_mod_order(&val.to_bytes_le())
    }
}

impl<P: FpConfig> From<Fp<P>> for num_bigint::BigUint {
    #[inline(always)]
    fn from(other: Fp<P>) -> Self {
        other.into_bigint().into()
    }
}

/* impl<P: FpConfig> From<P::BigInt> for Fp<P> {
    /// Converts `Self::BigInteger` into `Self`
    #[inline(always)]
    fn from(int: P::BigInt) -> Self {
        Self::from_bigint(int).unwrap()
    }
} */

use ark_std::{
    cmp::{Ord, Ordering, PartialOrd},
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
};
use num_traits::{One, Zero};

use crate::{
    biginteger::{arithmetic as fa, BigInt, BigInteger as _BigInteger},
    bytes::{FromBytes, ToBytes},
    fields::{FftField, Field, FpParameters, LegendreSymbol, PrimeField, SquareRootField},
};
use ark_serialize::*;

invoke_16!(impl_field_square_in_place);
invoke_16!(impl_field_mul_assign);

pub trait FpParams<const N: usize>: FpParameters<N, BigInt = BigInt<N>> {
    // Checking the modulus at compile time
    const NO_CARRY: bool = {
        let first_bit_set = Self::MODULUS.0[N - 1] >> 63 != 0;
        // $limbs can be 1, hence we can run into a case with an unused mut.
        #[allow(unused_mut)]
        let mut all_bits_set = Self::MODULUS.0[N - 1] == !0 - (1 << 63);
        let mut i = 1;
        while i < N {
            all_bits_set &= Self::MODULUS.0[N - i - 1] == !0u64;
            i += 1;
        }
        !(first_bit_set || all_bits_set)
    };
}

#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Copy(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
pub struct Fp<P, const N: usize>(
    pub BigInt<N>,
    #[derivative(Debug = "ignore")]
    #[doc(hidden)]
    pub PhantomData<P>,
);

impl<P, const N: usize> Fp<P, N> {
    #[inline]
    pub const fn new(element: BigInt<N>) -> Self {
        Self(element, PhantomData)
    }

    const fn const_is_zero(&self) -> bool {
        let mut is_zero = true;
        let mut i = 0;
        while i < N {
            is_zero &= (self.0).0[i] == 0;
            i += 1;
        }
        is_zero
    }

    const fn const_neg(self, modulus: BigInt<N>) -> Self {
        if !self.const_is_zero() {
            Self::new(Self::sub_noborrow(&modulus, &self.0))
        } else {
            self
        }
    }

    /// Interpret a string of decimal numbers as a prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    /// For *internal* use only; please use the `field_new` macro instead
    /// of this method
    #[doc(hidden)]
    pub const fn const_from_str(
        limbs: &[u64],
        is_positive: bool,
        r2: BigInt<N>,
        modulus: BigInt<N>,
        inv: u64,
    ) -> Self {
        let mut repr = P::BigInt([0; N]);
        let mut i = 0;
        while i < limbs.len() {
            repr.0[i] = limbs[i];
            i += 1;
        }
        let res = Self::const_from_repr(repr, r2, modulus, inv);
        if is_positive {
            res
        } else {
            res.const_neg(modulus)
        }
    }

    #[inline]
    pub(crate) const fn const_from_repr(
        repr: BigInt<N>,
        r2: BigInt<N>,
        modulus: BigInt<N>,
        inv: u64,
    ) -> Self {
        let mut r = Self::new(repr);
        if r.const_is_zero() {
            r
        } else {
            r = r.const_mul(&Fp::<P, N>(r2, PhantomData), modulus, inv);
            r
        }
    }

    const fn mul_without_reduce(mut self, other: &Self, modulus: BigInt<N>, inv: u64) -> Self {
        let mut r1 = [0u64; N];
        let mut r2 = [0u64; N];
        let mut i = 0;
        while i < N {
            let mut carry = 0;
            let mut j = 0;
            while j < N {
                if j + i < N {
                    r1[j + i] =
                        mac_with_carry!(r1[j + i], (self.0).0[i], (other.0).0[j], &mut carry);
                } else {
                    r2[j + i - N] =
                        mac_with_carry!(r2[j + i - N], (self.0).0[i], (other.0).0[j], &mut carry);
                }
                j += 1;
            }
            r2[i] = carry;
            i += 1;
        }
        // Montgomery reduction
        let mut _carry2 = 0;
        let mut i = 0;
        while i < N {
            let k = r1[i].wrapping_mul(inv);
            let mut carry = 0;
            mac_with_carry!(r1[i], k, modulus.0[0], &mut carry);
            let mut j = 0;
            while j < N {
                if j + i < N {
                    r1[j + i] = mac_with_carry!(r1[j + i], k, modulus.0[j], &mut carry);
                } else {
                    r2[j + i - N] = mac_with_carry!(r2[j + i - N], k, modulus.0[j], &mut carry);
                }
                j += 1;
            }
            r2[i] = adc!(r2[i], _carry2, &mut carry);
            _carry2 = carry;
            i += 1;
        }

        let mut i = 0;
        while i < N {
            (self.0).0[i] = r2[i];
            i += 1;
        }
        self
    }

    const fn const_mul(mut self, other: &Self, modulus: BigInt<N>, inv: u64) -> Self {
        self = self.mul_without_reduce(other, modulus, inv);
        self.const_reduce(modulus)
    }

    const fn const_is_valid(&self, modulus: BigInt<N>) -> bool {
        let mut i = 0;
        while i < N {
            if (self.0).0[(N - i - 1)] < modulus.0[(N - i - 1)] {
                return true;
            } else if (self.0).0[(N - i - 1)] > modulus.0[(N - i - 1)] {
                return false;
            }
            i += 1;
        }
        false
    }

    #[inline]
    const fn const_reduce(mut self, modulus: BigInt<N>) -> Self {
        if !self.const_is_valid(modulus) {
            self.0 = Self::sub_noborrow(&self.0, &modulus);
        }
        self
    }

    // need unused assignment because the last iteration of the loop produces an assignment
    // to `borrow` that is unused.
    #[allow(unused_assignments)]
    const fn sub_noborrow(a: &BigInt<N>, b: &BigInt<N>) -> BigInt<N> {
        let mut a = *a;
        let mut borrow = 0;
        let mut i = 0;
        while i < N {
            a.0[i] = sbb!(a.0[i], b.0[i], &mut borrow);
            i += 1;
        }
        a
    }
}

impl<P: FpParams<N>, const N: usize> Fp<P, N> {
    #[inline]
    pub(crate) fn is_valid(&self) -> bool {
        self.0 < P::MODULUS
    }

    #[inline]
    fn reduce(&mut self) {
        if !self.is_valid() {
            self.0.sub_noborrow(&P::MODULUS);
        }
    }
}

impl<P: FpParams<N>, const N: usize> Zero for Fp<P, N> {
    #[inline]
    fn zero() -> Self {
        Fp::<P, N>(BigInt::<N>::from(0), PhantomData)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: FpParams<N>, const N: usize> One for Fp<P, N> {
    #[inline]
    fn one() -> Self {
        Fp::<P, N>(P::R, PhantomData)
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == P::R
    }
}

impl<P: FpParams<N>, const N: usize> Field for Fp<P, N> {
    type BasePrimeField = Self;

    fn extension_degree() -> u64 {
        1
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
        // This cannot exceed the backing capacity.
        self.0.mul2();
        // However, it may need to be reduced.
        self.reduce();
        self
    }

    #[inline]
    fn characteristic<'a>() -> &'a [u64] {
        P::MODULUS.as_ref()
    }

    #[inline]
    fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        if F::BIT_SIZE > 8 {
            return None;
        } else {
            let mut result_bytes = vec![0u8; N * 8 + 1];
            // Copy the input into a temporary buffer.
            result_bytes
                .iter_mut()
                .zip(bytes)
                .for_each(|(result, input)| {
                    *result = *input;
                });
            // This mask retains everything in the last limb
            // that is below `P::MODULUS_BITS`.
            let last_limb_mask = (u64::MAX >> P::REPR_SHAVE_BITS).to_le_bytes();
            let mut last_bytes_mask = [0u8; 9];
            last_bytes_mask[..8].copy_from_slice(&last_limb_mask);

            // Length of the buffer containing the field element and the flag.
            let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);
            // Location of the flag is the last byte of the serialized
            // form of the field element.
            let flag_location = output_byte_size - 1;

            // At which byte is the flag located in the last limb?
            let flag_location_in_last_limb = flag_location - (8 * (N - 1));

            // Take all but the last 9 bytes.
            let last_bytes = &mut result_bytes[8 * (N - 1)..];

            // The mask only has the last `F::BIT_SIZE` bits set
            let flags_mask = u8::MAX.checked_shl(8 - (F::BIT_SIZE as u32)).unwrap_or(0);

            // Mask away the remaining bytes, and try to reconstruct the
            // flag
            let mut flags: u8 = 0;
            for (i, (b, m)) in last_bytes.iter_mut().zip(&last_bytes_mask).enumerate() {
                if i == flag_location_in_last_limb {
                    flags = *b & flags_mask
                }
                *b &= m;
            }
            Self::deserialize(&result_bytes[..(N * 8)])
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

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
    fn square_in_place(&mut self) -> &mut Self {
        if N == 1 {
            *self = *self * *self;
            return self;
        }
        #[cfg(use_asm)]
        #[allow(unsafe_code, unused_mut)]
        {
            if N <= 6 && P::NO_CARRY {
                ark_ff_asm::x86_64_asm_square!($limbs, (self.0).0);
                self.reduce();
                return self;
            }
        }

        let input = &mut (self.0).0;
        match_const!(square_in_place, N, input);
        self.reduce();
        self
    }

    #[inline]
    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            // Guajardo Kumar Paar Pelzl
            // Efficient Software-Implementation of Finite Fields with Applications to
            // Cryptography
            // Algorithm 16 (BEA for Inversion in Fp)

            let one = BigInt::<N>::from(1);

            let mut u = self.0;
            let mut v = P::MODULUS;
            let mut b = Fp::<P, N>(P::R2, PhantomData); // Avoids unnecessary reduction step.
            let mut c = Self::zero();

            while u != one && v != one {
                while u.is_even() {
                    u.div2();

                    if b.0.is_even() {
                        b.0.div2();
                    } else {
                        b.0.add_nocarry(&P::MODULUS);
                        b.0.div2();
                    }
                }

                while v.is_even() {
                    v.div2();

                    if c.0.is_even() {
                        c.0.div2();
                    } else {
                        c.0.add_nocarry(&P::MODULUS);
                        c.0.div2();
                    }
                }

                if v < u {
                    u.sub_noborrow(&v);
                    b.sub_assign(&c);
                } else {
                    v.sub_noborrow(&u);
                    c.sub_assign(&b);
                }
            }

            if u == one {
                Some(b)
            } else {
                Some(c)
            }
        }
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        if let Some(inverse) = self.inverse() {
            *self = inverse;
            Some(self)
        } else {
            None
        }
    }

    #[inline]
    fn frobenius_map(&mut self, _: usize) {
        // No-op: No effect in a prime field.
    }
}

impl<P: FpParams<N>, const N: usize> PrimeField for Fp<P, N> {
    type Params = P;
    type BigInt = BigInt<N>;

    #[inline]
    fn from_repr(r: BigInt<N>) -> Option<Self> {
        let mut r = Fp::<P, N>(r, PhantomData);
        if r.is_zero() {
            Some(r)
        } else if r.is_valid() {
            r *= &Fp::<P, N>(P::R2, PhantomData);
            Some(r)
        } else {
            None
        }
    }

    impl_field_into_repr!({ N });
}

impl<P: FpParams<N>, const N: usize> FftField for Fp<P, N> {
    type FftParams = P;

    #[inline]
    fn two_adic_root_of_unity() -> Self {
        Fp::<P, N>(P::TWO_ADIC_ROOT_OF_UNITY, PhantomData)
    }

    #[inline]
    fn large_subgroup_root_of_unity() -> Option<Self> {
        Some(Fp::<P, N>(P::LARGE_SUBGROUP_ROOT_OF_UNITY?, PhantomData))
    }

    #[inline]
    fn multiplicative_generator() -> Self {
        Fp::<P, N>(P::GENERATOR, PhantomData)
    }
}

impl<P: FpParams<N>, const N: usize> SquareRootField for Fp<P, N> {
    #[inline]
    fn legendre(&self) -> LegendreSymbol {
        use crate::fields::LegendreSymbol::*;

        // s = self^((MODULUS - 1) // 2)
        let s = self.pow(P::MODULUS_MINUS_ONE_DIV_TWO);
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
        sqrt_impl!(Self, P, self)
    }

    fn sqrt_in_place(&mut self) -> Option<&mut Self> {
        (*self).sqrt().map(|sqrt| {
            *self = sqrt;
            self
        })
    }
}

impl<P: FpParams<N>, const N: usize> Ord for Fp<P, N> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_repr().cmp(&other.into_repr())
    }
}

impl<P: FpParams<N>, const N: usize> PartialOrd for Fp<P, N> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: FpParams<N>, const N: usize> From<u128> for Fp<P, N> {
    fn from(other: u128) -> Self {
        let mut default_int = P::BigInt::default();
        if N == 1 {
            default_int.0[0] = (other % u128::from(P::MODULUS.0[0])) as u64;
        } else {
            let upper = (other >> 64) as u64;
            let lower = ((other << 64) >> 64) as u64;
            // This is equivalent to the following, but satisfying the compiler:
            // default_int.0[0] = lower;
            // default_int.0[1] = upper;
            let limbs = [lower, upper];
            for (cur, other) in default_int.0.iter_mut().zip(&limbs) {
                *cur = *other;
            }
        }
        Self::from_repr(default_int).unwrap()
    }
}

impl_prime_field_from_int!(u64);
impl_prime_field_from_int!(u32);
impl_prime_field_from_int!(u16);
impl_prime_field_from_int!(u8);
impl_prime_field_from_int!(bool);

impl<P: FpParams<N>, const N: usize> rand::distributions::Distribution<Fp<P, N>>
    for rand::distributions::Standard
{
    #[inline]
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Fp<P, N> {
        loop {
            let mut tmp = Fp::<P, N>(rng.sample(rand::distributions::Standard), PhantomData);
            // Mask away the unused bits at the beginning.
            tmp.0
                .as_mut()
                .last_mut()
                .map(|val| *val &= core::u64::MAX >> P::REPR_SHAVE_BITS);

            if tmp.is_valid() {
                return tmp;
            }
        }
    }
}
impl<P: FpParams<N>, const N: usize> CanonicalSerializeWithFlags for Fp<P, N> {
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
        // this is at most `$byte_size + 1`
        let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);

        // Write out `self` to a temporary buffer.
        // The size of the buffer is $byte_size + 1 because `F::BIT_SIZE`
        // is at most 8 bits.
        let mut bytes = vec![0u8; N * 8 + 1];
        self.write(&mut bytes[..N * 8])?;

        // Mask out the bits of the last byte that correspond to the flag.
        bytes[output_byte_size - 1] |= flags.u8_bitmask();

        writer.write_all(&bytes[..output_byte_size])?;
        Ok(())
    }

    // Let `m = 8 * n` for some `n` be the smallest multiple of 8 greater
    // than `P::MODULUS_BITS`.
    // If `(m - P::MODULUS_BITS) >= F::BIT_SIZE` , then this method returns `n`;
    // otherwise, it returns `n + 1`.
    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE)
    }
}

impl<P: FpParams<N>, const N: usize> CanonicalSerialize for Fp<P, N> {
    #[inline]
    fn serialize<W: ark_std::io::Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.serialized_size_with_flags::<EmptyFlags>()
    }
}

impl<P: FpParams<N>, const N: usize> CanonicalDeserializeWithFlags for Fp<P, N> {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        mut reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }
        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`. If `F::BIT_SIZE < 8`,
        // this is at most `$byte_size + 1`
        let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);

        let mut masked_bytes = vec![0; N * 8 + 1];
        reader.read_exact(&mut masked_bytes[..output_byte_size])?;

        let flags = F::from_u8_remove_flags(&mut masked_bytes[output_byte_size - 1])
            .ok_or(SerializationError::UnexpectedFlags)?;

        Ok((Self::read(&masked_bytes[..])?, flags))
    }
}

impl<P: FpParams<N>, const N: usize> CanonicalDeserialize for Fp<P, N> {
    fn deserialize<R: ark_std::io::Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_flags::<R, EmptyFlags>(reader).map(|(r, _)| r)
    }
}

impl<P: FpParams<N>, const N: usize> ToBytes for Fp<P, N> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> IoResult<()> {
        self.into_repr().write(writer)
    }
}

impl<P: FpParams<N>, const N: usize> FromBytes for Fp<P, N> {
    #[inline]
    fn read<R: Read>(reader: R) -> IoResult<Self> {
        P::BigInt::read(reader).and_then(|b| match Fp::<P, N>::from_repr(b) {
            Some(f) => Ok(f),
            None => Err(crate::error("FromBytes::read failed")),
        })
    }
}

impl<P: FpParams<N>, const N: usize> FromStr for Fp<P, N> {
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

        let ten = Self::from(<Self as PrimeField>::BigInt::from(10));

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
                }
                None => {
                    return Err(());
                }
            }
        }
        if !res.is_valid() {
            Err(())
        } else {
            Ok(res)
        }
    }
}

impl<P: FpParams<N>, const N: usize> Display for Fp<P, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, stringify!($Fp"({})"), self.into_repr())
    }
}

impl<P: FpParams<N>, const N: usize> Neg for Fp<P, N> {
    type Output = Self;
    #[inline]
    #[must_use]
    fn neg(self) -> Self {
        if !self.is_zero() {
            let mut tmp = P::MODULUS.clone();
            tmp.sub_noborrow(&self.0);
            Fp::<P, N>(tmp, PhantomData)
        } else {
            self
        }
    }
}

impl<'a, P: FpParams<N>, const N: usize> Add<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(self, other: &Self) -> Self {
        let mut result = self.clone();
        result.add_assign(other);
        result
    }
}

impl<'a, P: FpParams<N>, const N: usize> Sub<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &Self) -> Self {
        let mut result = self.clone();
        result.sub_assign(other);
        result
    }
}

impl<'a, P: FpParams<N>, const N: usize> Mul<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &Self) -> Self {
        let mut result = self.clone();
        result.mul_assign(other);
        result
    }
}

impl<'a, P: FpParams<N>, const N: usize> Div<&'a Fp<P, N>> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn div(self, other: &Self) -> Self {
        let mut result = self.clone();
        result.mul_assign(&other.inverse().unwrap());
        result
    }
}
#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::Add<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        let mut result = self;
        result.add_assign(&other);
        result
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::Add<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a mut Self) -> Self {
        let mut result = self;
        result.add_assign(&*other);
        result
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::Sub<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        let mut result = self;
        result.sub_assign(&other);
        result
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::Sub<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a mut Self) -> Self {
        let mut result = self;
        result.sub_assign(&*other);
        result
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::iter::Sum<Self> for Fp<P, N> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::iter::Sum<&'a Self> for Fp<P, N> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), core::ops::Add::add)
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::AddAssign<Self> for Fp<P, N> {
    fn add_assign(&mut self, other: Self) {
        self.add_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::SubAssign<Self> for Fp<P, N> {
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::AddAssign<&'a mut Self> for Fp<P, N> {
    fn add_assign(&mut self, other: &'a mut Self) {
        self.add_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::SubAssign<&'a mut Self> for Fp<P, N> {
    fn sub_assign(&mut self, other: &'a mut Self) {
        self.sub_assign(&*other)
    }
}
#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::Mul<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        let mut result = self;
        result.mul_assign(&other);
        result
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::Div<Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self {
        let mut result = self;
        result.div_assign(&other);
        result
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::Mul<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &'a mut Self) -> Self {
        let mut result = self;
        result.mul_assign(&*other);
        result
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::Div<&'a mut Self> for Fp<P, N> {
    type Output = Self;

    #[inline]
    fn div(self, other: &'a mut Self) -> Self {
        let mut result = self;
        result.div_assign(&*other);
        result
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::iter::Product<Self> for Fp<P, N> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), core::ops::Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::iter::Product<&'a Self> for Fp<P, N> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::MulAssign<Self> for Fp<P, N> {
    fn mul_assign(&mut self, other: Self) {
        self.mul_assign(&other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::DivAssign<&'a mut Self> for Fp<P, N> {
    fn div_assign(&mut self, other: &'a mut Self) {
        self.div_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<'a, P: FpParams<N>, const N: usize> core::ops::MulAssign<&'a mut Self> for Fp<P, N> {
    fn mul_assign(&mut self, other: &'a mut Self) {
        self.mul_assign(&*other)
    }
}

#[allow(unused_qualifications)]
impl<P: FpParams<N>, const N: usize> core::ops::DivAssign<Self> for Fp<P, N> {
    fn div_assign(&mut self, other: Self) {
        self.div_assign(&other)
    }
}

impl<'a, P: FpParams<N>, const N: usize> AddAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        // This cannot exceed the backing capacity.
        self.0.add_nocarry(&other.0);
        // However, it may need to be reduced
        self.reduce();
    }
}

impl<'a, P: FpParams<N>, const N: usize> SubAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        // If `other` is larger than `self`, add the modulus to self first.
        if other.0 > self.0 {
            self.0.add_nocarry(&P::MODULUS);
        }
        self.0.sub_noborrow(&other.0);
    }
}

impl<'a, P: FpParams<N>, const N: usize> MulAssign<&'a Self> for Fp<P, N> {
    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn mul_assign(&mut self, other: &Self) {
        // No-carry optimisation applied to CIOS
        if P::NO_CARRY {
            #[cfg(use_asm)]
            #[allow(unsafe_code, unused_mut)]
            {
                // Tentatively avoid using assembly for `$limbs == 1`.
                if N <= 6 && N > 1 {
                    ark_ff_asm::x86_64_asm_mul!($limbs, input, other);
                    self.reduce();
                    return;
                }
            }
            let input = &mut (self.0).0;
            let other_ = (other.0).0;
            match_const!(mul_assign, N, input, other_);
            self.reduce();
        } else {
            *self = self.mul_without_reduce(other, P::MODULUS, P::INV);
            self.reduce();
        }
    }
}

impl<'a, P: FpParams<N>, const N: usize> DivAssign<&'a Self> for Fp<P, N> {
    #[inline]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl<P: FpParams<N>, const N: usize> zeroize::Zeroize for Fp<P, N> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<P: FpParams<N>, const N: usize> Into<BigInt<N>> for Fp<P, N> {
    fn into(self) -> BigInt<N> {
        self.into_repr()
    }
}

impl<P: FpParams<N>, const N: usize> From<BigInt<N>> for Fp<P, N> {
    /// Converts `Self::BigInteger` into `Self`
    ///
    /// # Panics
    /// This method panics if `int` is larger than `P::MODULUS`.
    fn from(int: BigInt<N>) -> Self {
        Self::from_repr(int).unwrap()
    }
}

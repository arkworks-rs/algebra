use crate::{
    bytes::{FromBytes, ToBytes},
    fields::{BitIteratorBE, BitIteratorLE},
    UniformRand,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{
    fmt::{Debug, Display},
    io::{Read, Result as IoResult, Write},
    vec::Vec,
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
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

impl<const N: usize> BigInt<N> {
    pub const fn new(value: [u64; N]) -> Self {
        Self(value)
    }
}

impl<const N: usize> BigInteger for BigInt<N> {
    const NUM_LIMBS: usize = N;

    #[inline]
    fn add_nocarry(&mut self, other: &Self) -> bool {
        let mut carry = 0;

        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = adc!(*a, *b, &mut carry);
        }

        carry != 0
    }

    #[inline]
    fn sub_noborrow(&mut self, other: &Self) -> bool {
        let mut borrow = 0;

        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = sbb!(*a, *b, &mut borrow);
        }

        borrow != 0
    }

    #[inline]
    fn mul2(&mut self) {
        let mut last = 0;
        for i in &mut self.0 {
            let tmp = *i >> 63;
            *i <<= 1;
            *i |= last;
            last = tmp;
        }
    }

    #[inline]
    fn muln(&mut self, mut n: u32) {
        if n >= 64 * N as u32 {
            *self = Self::from(0);
            return;
        }

        while n >= 64 {
            let mut t = 0;
            for i in &mut self.0 {
                core::mem::swap(&mut t, i);
            }
            n -= 64;
        }

        if n > 0 {
            let mut t = 0;
            for i in &mut self.0 {
                let t2 = *i >> (64 - n);
                *i <<= n;
                *i |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn div2(&mut self) {
        let mut t = 0;
        for i in self.0.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    }

    #[inline]
    fn divn(&mut self, mut n: u32) {
        if n >= 64 * N as u32 {
            *self = Self::from(0);
            return;
        }

        while n >= 64 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                core::mem::swap(&mut t, i);
            }
            n -= 64;
        }

        if n > 0 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                let t2 = *i << (64 - n);
                *i >>= n;
                *i |= t;
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
        let mut res = Self::default();
        let mut acc: u64 = 0;

        let bits = bits.to_vec();
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

    #[inline]
    fn to_bytes_be(&self) -> Vec<u8> {
        let mut le_bytes = self.to_bytes_le();
        le_bytes.reverse();
        le_bytes
    }

    #[inline]
    fn to_bytes_le(&self) -> Vec<u8> {
        let array_map = self.0.iter().map(|limb| limb.to_le_bytes());
        let mut res = Vec::<u8>::with_capacity(N * 8);
        for limb in array_map {
            res.extend_from_slice(&limb);
        }
        res
    }

    #[inline]
    fn find_wnaf(&self) -> Vec<i64> {
        let mut res = vec![];

        let mut e = self.clone();
        while !e.is_zero() {
            let z: i64;
            if e.is_odd() {
                z = 2 - (e.0[0] % 4) as i64;
                if z >= 0 {
                    e.sub_noborrow(&Self::from(z as u64));
                } else {
                    e.add_nocarry(&Self::from((-z) as u64));
                }
            } else {
                z = 0;
            }
            res.push(z);
            e.div2();
        }

        res
    }
}

impl<const N: usize> CanonicalSerialize for BigInt<N> {
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.write(writer)?;
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        Self::NUM_LIMBS * 8
    }
}

impl<const N: usize> CanonicalDeserialize for BigInt<N> {
    #[inline]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let value = Self::read(reader)?;
        Ok(value)
    }
}

impl<const N: usize> ToBytes for BigInt<N> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> IoResult<()> {
        self.0.as_ref().write(writer)
    }
}

impl<const N: usize> FromBytes for BigInt<N> {
    #[inline]
    fn read<R: Read>(reader: R) -> IoResult<Self> {
        <[u64; N]>::read(reader).map(Self::new)
    }
}

impl<const N: usize> Display for BigInt<N> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        for i in self.0.iter().rev() {
            write!(f, "{:016X}", *i)?;
        }
        Ok(())
    }
}

impl<const N: usize> Ord for BigInt<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
        for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
            if a < b {
                return core::cmp::Ordering::Less;
            } else if a > b {
                return core::cmp::Ordering::Greater;
            }
        }

        core::cmp::Ordering::Equal
    }
}

impl<const N: usize> PartialOrd for BigInt<N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Distribution<BigInt<N>> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BigInt<N> {
        let mut res = [0u64; N];
        for i in 0..N {
            res[i] = rng.gen();
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

pub type BigInteger64 = BigInt<1>;
pub type BigInteger128 = BigInt<2>;
pub type BigInteger256 = BigInt<4>;
pub type BigInteger320 = BigInt<5>;
pub type BigInteger384 = BigInt<6>;
pub type BigInteger768 = BigInt<12>;
pub type BigInteger832 = BigInt<13>;

#[cfg(test)]
mod tests;

/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant limb first.
pub trait BigInteger:
    ToBytes
    + FromBytes
    + CanonicalSerialize
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
{
    /// Number of limbs.
    const NUM_LIMBS: usize;

    /// Add another representation to this one, returning the carry bit.
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    fn sub_noborrow(&mut self, other: &Self) -> bool;

    /// Performs a leftwise bitshift of this number, effectively multiplying
    /// it by 2. Overflow is ignored.
    fn mul2(&mut self);

    /// Performs a leftwise bitshift of this number by some amount.
    fn muln(&mut self, amt: u32);

    /// Performs a rightwise bitshift of this number, effectively dividing
    /// it by 2.
    fn div2(&mut self);

    /// Performs a rightwise bitshift of this number by some amount.
    fn divn(&mut self, amt: u32);

    /// Returns true iff this number is odd.
    fn is_odd(&self) -> bool;

    /// Returns true iff this number is even.
    fn is_even(&self) -> bool;

    /// Returns true iff this number is zero.
    fn is_zero(&self) -> bool;

    /// Compute the number of bits needed to encode this number. Always a
    /// multiple of 64.
    fn num_bits(&self) -> u32;

    /// Compute the `i`-th bit of `self`.
    fn get_bit(&self, i: usize) -> bool;

    /// Returns the big integer representation of a given big endian boolean
    /// array.
    fn from_bits_be(bits: &[bool]) -> Self;

    /// Returns the big integer representation of a given little endian boolean
    /// array.
    fn from_bits_le(bits: &[bool]) -> Self;

    /// Returns the bit representation in a big endian boolean array,
    /// with leading zeroes.
    fn to_bits_be(&self) -> Vec<bool> {
        BitIteratorBE::new(self).collect::<Vec<_>>()
    }

    /// Returns the bit representation in a little endian boolean array,
    /// with trailing zeroes.
    fn to_bits_le(&self) -> Vec<bool> {
        BitIteratorLE::new(self).collect::<Vec<_>>()
    }

    /// Returns the byte representation in a big endian byte array,
    /// with leading zeros.
    fn to_bytes_be(&self) -> Vec<u8>;

    /// Returns the byte representation in a little endian byte array,
    /// with trailing zeros.
    fn to_bytes_le(&self) -> Vec<u8>;

    /// Returns a vector for wnaf.
    fn find_wnaf(&self) -> Vec<i64>;

    /// Writes this `BigInteger` as a big endian integer. Always writes
    /// `(num_bits` / 8) bytes.
    fn write_le<W: Write>(&self, writer: &mut W) -> IoResult<()> {
        self.write(writer)
    }

    /// Reads a big endian integer occupying (`num_bits` / 8) bytes into this
    /// representation.
    fn read_le<R: Read>(&mut self, reader: &mut R) -> IoResult<()> {
        *self = Self::read(reader)?;
        Ok(())
    }
}

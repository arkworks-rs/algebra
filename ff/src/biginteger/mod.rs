use crate::{
    bytes::{FromBytes, ToBytes},
    fields::BitIteratorBE,
    UniformRand,
};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, ConstantSerializedSize, SerializationError,
};
use ark_std::{
    fmt::{Debug, Display},
    io::{Read, Result as IoResult, Write},
    ops::{Shl, ShlAssign, Shr, ShrAssign},
    vec::Vec,
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use zeroize::Zeroize;

#[macro_use]
pub mod arithmetic;
#[macro_use]
mod macros;

bigint_impl!(BigInteger64, 1);
bigint_impl!(BigInteger128, 2);
bigint_impl!(BigInteger256, 4);
bigint_impl!(BigInteger320, 5);
bigint_impl!(BigInteger384, 6);
bigint_impl!(BigInteger768, 12);
bigint_impl!(BigInteger832, 13);

#[cfg(test)]
mod tests;

/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant limb first.
pub trait BigInteger:
    ToBytes
    + FromBytes
    + CanonicalSerialize
    + ConstantSerializedSize
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
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
{
    /// Number of limbs.
    const NUM_LIMBS: usize;

    /// Add another representation to this one, returning the carry bit.
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    fn sub_noborrow(&mut self, other: &Self) -> bool;

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
    fn from_bits(bits: &[bool]) -> Self;

    /// Returns the bit representation in a big endian boolean array, without
    /// leading zeros.
    fn to_bits(&self) -> Vec<bool>;

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

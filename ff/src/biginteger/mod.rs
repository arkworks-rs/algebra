use crate::{
    bytes::{FromBytes, ToBytes},
    fields::{BitIteratorBE, BitIteratorLE},
    UniformRand,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{
    convert::TryFrom,
    fmt::{Debug, Display},
    io::{Read, Result as IoResult, Write},
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
#[macro_use]
mod macros;

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

bigint_impl!(BigInteger64, 1);
bigint_impl!(BigInteger128, 2);
bigint_impl!(BigInteger256, 4);
bigint_impl!(BigInteger320, 5);
bigint_impl!(BigInteger384, 6);
bigint_impl!(BigInteger448, 7);
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
    + TryFrom<BigUint>
    + Into<BigUint>
{
    /// Number of 64-bit limbs representing `Self`.
    const NUM_LIMBS: usize;

    /// Add another representation to this one, returning the carry bit.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut two_add) = (B::from(1u64), B::from(2u64));
    /// two_add.add_nocarry(&one);
    /// assert_eq!(two_add, B::from(3u64));
    ///
    /// // Edge-Case
    /// let mut max_one = B::from(u64::MAX);
    /// let carry = max_one.add_nocarry(&one);
    /// assert_eq!(max_one, B::from(0u64));
    /// assert_eq!(carry, true)
    /// ```
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut two, mut three_sub) = (B::from(1u64), B::from(2u64), B::from(3u64));
    /// three_sub.sub_noborrow(&two);
    /// assert_eq!(three_sub, one);
    ///
    /// // Edge-Case
    /// let borrow = one.sub_noborrow(&two);
    /// assert_eq!(borrow, true);
    /// assert_eq!(one, B::from(u64::MAX));
    /// ```
    fn sub_noborrow(&mut self, other: &Self) -> bool;

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
    /// let mut arr : [bool; 64] = [false; 64];
    /// arr[0] = true;
    /// let mut mul = B::from_bits_be(&arr);
    /// mul.mul2();
    /// assert_eq!(mul, B::from(0u64));
    /// ```
    fn mul2(&mut self);

    /// Performs a leftwise bitshift of this number by some amount.
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
    /// let mut arr : [bool; 64] = [false; 64];
    /// arr[4] = true;
    /// let mut mul = B::from_bits_be(&arr);
    /// mul.muln(5);
    /// assert_eq!(mul, B::from(0u64));
    /// ```
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
    /// let mut arr : [bool; 64] = [false; 64];
    /// arr[4] = true;
    /// let mut div = B::from_bits_le(&arr);
    /// div.divn(5);
    /// assert_eq!(div, B::from(0u64));
    /// ```
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
    /// let mut arr : [bool; 64] = [false; 64];
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
    /// let mut arr : [bool; 64] = [false; 64];
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
        if w >= 2 && w < 64 {
            let mut res = vec![];
            let mut e = *self;

            while !e.is_zero() {
                let z: i64;
                if e.is_odd() {
                    z = signed_mod_reduction(e.as_ref()[0], 1 << w);
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

            Some(res)
        } else {
            None
        }
    }

    /// Writes this `BigInteger` as a big endian integer. Always writes
    /// `NUM_LIMBS * 8` bytes.
    fn write_le<W: Write>(&self, writer: &mut W) -> IoResult<()> {
        self.write(writer)
    }

    /// Reads a big endian integer occupying
    /// `NUM_LIMBS * 8` bytes into this representation.
    fn read_le<R: Read>(&mut self, reader: &mut R) -> IoResult<()> {
        *self = Self::read(reader)?;
        Ok(())
    }
}

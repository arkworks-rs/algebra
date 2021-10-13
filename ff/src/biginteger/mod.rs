use crate::{
    bytes::{FromBytes, ToBytes},
    fields::{BitIteratorBE, BitIteratorLE},
    UniformRand,
    biginteger::BigInteger
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
    /// Number of limbs representing BigInteger.
    const NUM_LIMBS: usize;

    /// Add another representation to this one, returning the carry bit.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut one, mut two_add, mut three) = (B::from(1u64), B::from(2u64), B::from(3u64));
    /// two_add.add_nocarry(&one);
    /// assert_eq!(two_add, three);
    /// ```
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut one, mut two, mut three_sub) = (B::from(1u64), B::from(2u64), B::from(3u64));
    /// three_sub.sub_noborrow(&two);
    /// assert_eq!(three_sub, one);
    /// ```
    fn sub_noborrow(&mut self, other: &Self) -> bool;

    /// Performs a leftwise bitshift of this number, effectively multiplying
    /// it by 2. Overflow is ignored.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut two_mul, mut four) = (B::from(2u64), B::from(4u64));
    /// two_mul.mul2();
    /// assert_eq!(two_mul, four);
    /// ```
    fn mul2(&mut self);

    /// Performs a leftwise bitshift of this number by some amount.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut one_mul, mut thirty_two) = (B::from(1u64), B::from(32u64));
    /// one_mul.muln(5);
    /// assert_eq!(one_mul, thirty_two);
    /// ```
    fn muln(&mut self, amt: u32);

    /// Performs a rightwise bitshift of this number, effectively dividing
    /// it by 2.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut two, mut four_div) = (B::from(2u64), B::from(4u64));
    /// four_div.div2();
    /// assert_eq!(two, four_div);
    /// ```
    fn div2(&mut self);

    /// Performs a rightwise bitshift of this number by some amount.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let (mut one, mut thirty_two_div) = (B::from(1u64), B::from(32u64));
    /// thirty_two_div.divn(5);
    /// assert_eq!(one, thirty_two_div);
    /// ```
    fn divn(&mut self, amt: u32);

    /// Returns true iff this number is odd.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut one = B::from(1u64);
    /// assert!(one.is_odd());
    /// ```
    fn is_odd(&self) -> bool;

    /// Returns true iff this number is even.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut two = B::from(2u64);
    /// assert!(one.is_even());
    /// ```
    fn is_even(&self) -> bool;

    /// Returns true iff this number is zero.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut zero = B::from(0u64);
    /// assert!(zero.is_zero());
    /// ```
    fn is_zero(&self) -> bool;

    /// Compute the number of bits needed to encode this number. Always a
    /// multiple of 64.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut zero = B::from(0u64);
    /// assert_equal!(zero.num_bits(), 64u32);
    /// ```
    fn num_bits(&self) -> u32;

    /// Compute the `i`-th bit of `self`.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
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
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut arr : [bool; 64] = [false; 64];
    /// arr[63] = true;
    /// let mut one = B::from(1u64);
    /// assert_equal!(B::from_bits_be(&arr), one);
    /// ```   
    fn from_bits_be(bits: &[bool]) -> Self;

    /// Returns the big integer representation of a given little endian boolean
    /// array.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut arr : [bool; 64] = [false; 64];
    /// arr[0] = true;
    /// let mut one = B::from(1u64);
    /// assert_equal!(B::from_bits_le(&arr), one);
    /// ```   
    fn from_bits_le(bits: &[bool]) -> Self;

    /// Returns the bit representation in a big endian boolean array,
    /// with leading zeroes.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut one = B::from(1u64);
    /// let arr : Vec<bool> = one.to_bits_be();
    /// let vec = vec![false; 64];
    /// vec[63] = true;
    /// assert_equal!(arr, vec);
    /// ```  
    fn to_bits_be(&self) -> Vec<bool> {
        BitIteratorBE::new(self).collect::<Vec<_>>()
    }

    /// Returns the bit representation in a little endian boolean array,
    /// with trailing zeroes.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut one = B::from(1u64);
    /// let arr : Vec<bool> = one.to_bits_le();
    /// let vec = vec![false; 64];
    /// vec[0] = true;
    /// assert_equal!(arr, vec);
    /// ```
    fn to_bits_le(&self) -> Vec<bool> {
        BitIteratorLE::new(self).collect::<Vec<_>>()
    }

    /// Returns the byte representation in a big endian byte array,
    /// with leading zeros.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut one = B::from(1u64);
    /// let arr : Vec<u8> = one.to_bits_be();
    /// let vec = vec![0; 64];
    /// vec[63] = 1;
    /// assert_equal!(arr, vec);
    /// ```
    fn to_bytes_be(&self) -> Vec<u8>;

    /// Returns the byte representation in a little endian byte array,
    /// with trailing zeros.
    /// # Example
    ///
    /// ```
    /// use crate::biginteger::BigInteger64 as B;
    ///
    /// let mut one = B::from(1u64);
    /// let arr : Vec<u8> = one.to_bits_le();
    /// let vec = vec![0; 64];
    /// vec[0] = 1;
    /// assert_equal!(arr, vec);
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

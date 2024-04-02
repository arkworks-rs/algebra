use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    UniformRand,
    hash::Hash,
    fmt::{Debug, Display},
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Shl, ShlAssign, Shr,
        ShrAssign, Not, Rem,
    },
    str::FromStr,
    vec::*,
};
use num_bigint::BigUint;
use zeroize::Zeroize;

#[macro_use]
pub mod arithmetic;

pub mod bigint_64;

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
    + Hash
    + Send
    + Sized
    + Sync
    + 'static
    + UniformRand
    + Zeroize
    + From<u64>
    + From<u32>
    + From<u16>
    + From<u8>
    + From<bool>
    + TryFrom<BigUint, Error = ()>
    + FromStr
    + Into<BigUint>
    + Into<num_bigint::BigInt>
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
    + Not<Output = Self>
    + Rem<u64, Output = u64>
{
    /// The number of bits represented by this [`BigInteger`].
    const BIT_SIZE: usize;
    
    /// The zero value of this [`BigInteger`].
    const ZERO: Self;
    
    /// The one value of this [`BigInteger`].
    const ONE: Self;

    /// Add another [`BigInteger`] to `self`. This method stores the result in `self`,
    /// and returns a carry bit.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (mut one, mut x) = (B::ONE, B::from(2u64));
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
    /// let (mut one_sub, two, mut three_sub) = (B::ONE, B::from(2u64), B::from(3u64));
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
    /// let mut one_mul = B::ONE;
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
    #[deprecated(since = "0.4.2", note = "please use the operator `<<` instead")]
    fn muln(&mut self, amt: u32);

    /// Multiplies this [`BigInteger`] by another [`BigInteger`], storing the result in `self`.
    /// Overflow is ignored.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let mut a = B::from(42u64);
    /// let b = B::from(3u64);
    /// assert_eq!(a.mul_low(&b), B::from(126u64));
    ///
    /// // Edge-Case
    /// let mut zero = B::from(0u64);
    /// assert_eq!(zero.mul_low(&B::from(5u64)), B::from(0u64));
    /// ```
    fn mul_low(&self, other: &Self) -> Self;

    /// Multiplies this [`BigInteger`] by another [`BigInteger`], returning the high bits of the result.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let (one, x) = (B::ONE, B::from(2u64));
    /// let r = x.mul_high(&one);
    /// assert_eq!(r, B::from(0u64));
    ///
    /// // Edge-Case
    /// let mut x = B::from(u64::MAX);
    /// let r = x.mul_high(&B::from(2u64));
    /// assert_eq!(r, B::ONE)
    /// ```
    fn mul_high(&self, other: &Self) -> Self;

    /// Multiplies this [`BigInteger`] by another `BigInteger`, returning both low and high bits of the result.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// // Basic
    /// let mut a = B::from(42u64);
    /// let b = B::from(3u64);
    /// let (low_bits, high_bits) = a.mul(&b);
    /// assert_eq!(low_bits, B::from(126u64));
    /// assert_eq!(high_bits, B::from(0u64));
    ///
    /// // Edge-Case
    /// let mut x = B::from(u64::MAX);
    /// let mut max_plus_max = x;
    /// max_plus_max.add_with_carry(&x);
    /// let (low_bits, high_bits) = x.mul(&B::from(2u64));
    /// assert_eq!(low_bits, max_plus_max);
    /// assert_eq!(high_bits, B::ONE);
    /// ```
    fn mul(&self, other: &Self) -> (Self, Self);

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
    /// let mut one = B::ONE;
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
    /// let (mut one, mut thirty_two_div) = (B::ONE, B::from(32u64));
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
    /// let mut one = B::ONE;
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
    /// assert!(B::ZERO.is_zero());
    /// assert!(!B::ONE.is_zero());
    /// ```
    fn is_zero(&self) -> bool;

    /// Compute the minimum number of bits needed to encode this number.
    /// # Example
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let zero = B::from(0u64);
    /// assert_eq!(zero.num_bits(), 0);
    /// let one = B::ONE;
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
    /// let mut one = B::ONE;
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
    /// let mut one = B::ONE;
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
    /// let mut one = B::ONE;
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
    /// let one = B::ONE;
    /// let arr = one.to_bits_be();
    /// let mut vec = vec![false; 64];
    /// vec[63] = true;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bits_be(&self) -> Vec<bool> {
        self.bits_le_iter().collect()
    }

    /// Returns the bit representation in a little endian boolean array,
    /// with trailing zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// let arr = one.to_bits_le();
    /// let mut vec = vec![false; 64];
    /// vec[0] = true;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bits_le(&self) -> Vec<bool> {
        self.bits_be_iter().collect()
    }
    
    /// Returns an iterator over the little-endian bit representation of `self` 
    /// with trailing zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// let arr = one.bits_le_iter().collect::<Vec<bool>>();
    /// assert_eq!(arr, one.to_bits_le());
    /// ```
    fn bits_le_iter(&self) -> impl Iterator<Item = bool>;

    /// Returns an iterator over the big-endian bit representation of `self` 
    /// with leading zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// let arr = one.bits_be_iter().collect::<Vec<bool>>();
    /// assert_eq!(arr, one.to_bits_be());
    /// ```
    fn bits_be_iter(&self) -> impl Iterator<Item = bool>;

    /// Returns the byte representation in a big endian byte array,
    /// with leading zeros.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
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
    /// let one = B::ONE;
    /// let arr = one.to_bytes_le();
    /// let mut vec = vec![0; 8];
    /// vec[0] = 1;
    /// assert_eq!(arr, vec);
    /// ```
    fn to_bytes_le(&self) -> Vec<u8>;
    
    /// Returns an iterator over the little-endian bytes representation of `self` 
    /// with trailing zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// let arr = one.bytes_le_iter().collect::<Vec<u8>>();
    /// assert_eq!(arr, one.to_bytes_le());
    /// ```
    fn bytes_le_iter(&self) -> impl Iterator<Item = u8>;

    /// Returns an iterator over the big-endian byte representation of `self` 
    /// with leading zeroes.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// let arr = one.bytes_be_iter().collect::<Vec<u8>>();
    /// assert_eq!(arr, one.to_bytes_be());
    /// ```
    fn bytes_be_iter(&self) -> impl Iterator<Item = u8>;
    
    /// Constructs a [`BigInteger`] from an iterator over little-endian bytes.
    /// Extra bytes are ignored.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// assert_eq!(B::ONE, B::from_bytes_le_iter(one.bytes_le_iter()));
    /// ```
    fn from_bytes_le_iter(bytes: impl Iterator<Item = u8>) -> Self;

    /// Constructs a [`BigInteger`] from an iterator over big-endian bytes.
    /// Extra bytes are ignored.
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let one = B::ONE;
    /// assert_eq!(B::ONE, B::from_bytes_be_iter(one.bytes_be_iter()));
    /// ```
    fn from_bytes_be_iter(bytes: impl Iterator<Item = u8>) -> Self;
    
    /// Clears the most significant `n` bits of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use ark_ff::{biginteger::BigInteger64 as B, BigInteger as _};
    ///
    /// let mut a = B::from(u64::MAX);
    /// a.clear_msbs(3);
    /// assert_eq!(a, B::from(u64::MAX >> 3));
    /// ```
    fn clear_msbs(&mut self, n: usize);

    /// Returns the windowed non-adjacent form of `self`, for a window of size `w`.
    fn find_wnaf(&self, w: usize) -> Option<Vec<i64>>; 
}

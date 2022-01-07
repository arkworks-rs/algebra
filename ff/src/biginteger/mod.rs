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
    #[ark_ff_asm::unroll_for_loops]
    fn add_nocarry(&mut self, other: &Self) -> bool {
        let mut carry = 0;

        for i in 0..N {
            #[cfg(all(target_arch = "x86_64", feature = "asm"))]
            #[allow(unsafe_code)]
            unsafe {
                use core::arch::x86_64::_addcarry_u64;
                carry = _addcarry_u64(carry, self.0[i], other.0[i], &mut self.0[i])
            };

            #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
            {
                self.0[i] = adc!(self.0[i], other.0[i], &mut carry);
            }
        }

        carry != 0
    }
    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn sub_noborrow(&mut self, other: &Self) -> bool {
        let mut borrow = 0;

        for i in 0..N {
            #[cfg(all(target_arch = "x86_64", feature = "asm"))]
            #[allow(unsafe_code)]
            unsafe {
                use core::arch::x86_64::_subborrow_u64;
                borrow = _subborrow_u64(borrow, self.0[i], other.0[i], &mut self.0[i])
            };

            #[cfg(not(all(target_arch = "x86_64", feature = "asm")))]
            {
                self.0[i] = sbb!(self.0[i], other.0[i], &mut borrow);
            }
        }

        borrow != 0
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused)]
    fn mul2(&mut self) {
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
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn muln(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::from(0);
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
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused)]
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
    #[ark_ff_asm::unroll_for_loops]
    fn divn(&mut self, mut n: u32) {
        if n >= (64 * N) as u32 {
            *self = Self::from(0);
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
        for i in 0..N {
            if self.0[i] != 0 {
                return false;
            }
        }
        true
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
        self.0.write(writer)
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
    #[ark_ff_asm::unroll_for_loops]
    fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
        use core::cmp::Ordering;
        for i in 0..N {
            let a = &self.0[N - i - 1];
            let b = &other.0[N - i - 1];
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
impl<const N: usize> TryFrom<BigUint> for BigInt<N> {
    type Error = ark_std::string::String;

    #[inline]
    fn try_from(val: num_bigint::BigUint) -> Result<BigInt<N>, Self::Error> {
        let bytes = val.to_bytes_le();

        if bytes.len() > N * 8 {
            Err(format!(
                "A BigUint of {} bytes cannot fit into {} limbs.",
                bytes.len(),
                N
            ))
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

use crate::{BigInteger, FftField, Field};

use ark_std::{cmp::min, str::FromStr};
use num_bigint::BigUint;

/// The interface for a prime field, i.e. the field of integers modulo a prime $p$.
/// In the following example we'll use the prime field underlying the BLS12-381 G1 curve.
/// ```rust
/// use ark_ff::{BigInteger, Field, PrimeField, Zero};
/// use ark_std::{test_rng, One, UniformRand};
/// use ark_test_curves::bls12_381::Fq as F;
///
/// let mut rng = test_rng();
/// let a = F::rand(&mut rng);
/// // We can access the prime modulus associated with `F`:
/// let modulus = <F as PrimeField>::MODULUS;
/// assert_eq!(a.pow(&modulus), a); // the Euler-Fermat theorem tells us: a^{p-1} = 1 mod p
///
/// // We can convert field elements to integers in the range [0, MODULUS - 1]:
/// let one: num_bigint::BigUint = F::one().into();
/// assert_eq!(one, num_bigint::BigUint::one());
///
/// // We can construct field elements from an arbitrary sequence of bytes:
/// let n = F::from_le_bytes_mod_order(&modulus.to_bytes_le());
/// assert_eq!(n, F::zero());
/// ```
pub trait PrimeField:
    Field<BasePrimeField = Self>
    + FftField
    + FromStr
    + From<<Self as PrimeField>::BigInt>
    + Into<<Self as PrimeField>::BigInt>
    + From<BigUint>
    + Into<BigUint>
{
    /// A `BigInteger` type that can represent elements of this field.
    type BigInt: BigInteger;

    /// The modulus `p`.
    const MODULUS: Self::BigInt;

    /// The value `(p - 1)/ 2`.
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt;

    /// The size of the modulus in bits.
    const MODULUS_BIT_SIZE: u32;

    /// The trace of the field is defined as the smallest integer `t` such that by
    /// `2^s * t = p - 1`, and `t` is coprime to 2.
    const TRACE: Self::BigInt;
    /// The value `(t - 1)/ 2`.
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt;

    /// Construct a prime field element from an integer in the range 0..(p - 1).
    fn from_bigint(repr: Self::BigInt) -> Option<Self>;

    /// Converts an element of the prime field into an integer in the range 0..(p - 1).
    fn into_bigint(self) -> Self::BigInt;

    /// Reads bytes in big-endian, and converts them to a field element.
    /// If the integer represented by `bytes` is larger than the modulus `p`, this method
    /// performs the appropriate reduction.
    fn from_be_bytes_mod_order(bytes: &[u8]) -> Self {
        // Process big-endian input without allocating by accumulating in base 2^64.
        let pow256 = Self::from(256u64);
        let window64 = pow256.pow(&[8]);

        let mut res = Self::from(0u64);

        // Handle a possible leading partial chunk (most-significant bytes).
        let rem_len = bytes.len() % 8;
        if rem_len != 0 {
            let mut acc: u64 = 0;
            for &b in &bytes[..rem_len] {
                acc = (acc << 8) | (b as u64);
            }
            // Multiply by 256^rem_len and add the partial limb.
            let window_small = pow256.pow(&[rem_len as u64]);
            res *= window_small;
            res += Self::from(acc);
        }

        // Process remaining bytes in 8-byte big-endian chunks.
        for chunk in bytes[rem_len..].chunks(8) {
            let limb = u64::from_be_bytes(chunk.try_into().expect("chunk size is 8"));
            res *= window64;
            res += Self::from(limb);
        }
        res
    }

    /// Reads bytes in little-endian, and converts them to a field element.
    /// If the integer represented by `bytes` is larger than the modulus `p`, this method
    /// performs the appropriate reduction.
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        let num_modulus_bytes = Self::MODULUS_BIT_SIZE.div_ceil(8) as usize;
        let num_bytes_to_directly_convert = min(num_modulus_bytes - 1, bytes.len());
        // Copy the leading little-endian bytes directly into a field element.
        // The number of bytes directly converted must be less than the
        // number of bytes needed to represent the modulus, as we must begin
        // modular reduction once the data is of the same number of bytes as the
        // modulus.
        let (bytes, bytes_to_directly_convert) =
            bytes.split_at(bytes.len() - num_bytes_to_directly_convert);
        // Guaranteed to not be None, as the input is less than the modulus size.
        let mut res = Self::from_random_bytes(bytes_to_directly_convert).unwrap();

        // Update the result using 8-byte chunks for better performance.
        // We go through existing field arithmetic, which handles the reduction.
        // TODO: Already parsing in 8-byte chunks; consider specialized mul-by-u64
        // or even wider chunk sizes if profiling shows further benefit.
        let pow256 = Self::from(256u64);
        let window64 = pow256.pow(&[8]);

        let mut iter = bytes.rchunks_exact(8);
        for chunk in &mut iter {
            let limb = u64::from_le_bytes(chunk.try_into().expect("chunk size is 8"));
            res *= window64;
            res += Self::from(limb);
        }
        let rem = iter.remainder();
        if !rem.is_empty() {
            let window_small = pow256.pow(&[rem.len() as u64]);
            res *= window_small;
            let mut acc: u64 = 0;
            for (i, b) in rem.iter().enumerate() {
                acc |= (*b as u64) << (8 * i);
            }
            res += Self::from(acc);
        }
        res
    }
}

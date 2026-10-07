//! Prime field `Fp` where `p = 2^127 - 1`.
use ark_ff::fields::{Fp128, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "170141183460469231731687303715884105727"]
#[generator = "43"]
pub struct FqConfig;
pub type Fq = Fp128<MontBackend<FqConfig, 2>>;

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    test_field!(fq; Fq; mont_prime_field);

    mod raw_layout {
        //! `Fp<P, N>` is `#[repr(transparent)]` around `BigInt<N>(pub [u64; N])`
        //! and derives `zerocopy::IntoBytes` / `Immutable` / `KnownLayout`.
        //! These tests pin the size/alignment contract down.

        use super::*;
        use ark_std::vec::Vec;
        use core::mem::{align_of, size_of};
        use zerocopy::{FromBytes, IntoBytes};

        #[test]
        fn layout_matches_u64_array() {
            assert_eq!(size_of::<Fq>(), size_of::<[u64; 2]>());
            assert_eq!(align_of::<Fq>(), align_of::<[u64; 2]>());
        }

        #[test]
        fn as_bytes_is_le_montgomery_limbs() {
            let elems: Vec<Fq> = (0..4u64).map(Fq::from).collect();
            let bytes = elems.as_bytes();
            assert_eq!(bytes.len(), elems.len() * 16);

            for (i, elem) in elems.iter().enumerate() {
                let limbs: [u64; 2] = elem.0 .0;
                let lo: [u8; 8] = bytes[i * 16..i * 16 + 8].try_into().unwrap();
                let hi: [u8; 8] = bytes[i * 16 + 8..(i + 1) * 16].try_into().unwrap();
                assert_eq!(u64::from_le_bytes(lo), limbs[0]);
                assert_eq!(u64::from_le_bytes(hi), limbs[1]);
            }
        }

        /// `FromBytes` lets a `&mut [Fq]` be reinterpreted as a `&mut [u64]`
        /// without any `unsafe` at the call site — enabling safe in-place
        /// SIMD-style writes to the underlying Montgomery limbs.
        #[test]
        fn mut_from_bytes_gives_safe_u64_view() {
            let mut elems: Vec<Fq> = (0..4u64).map(Fq::from).collect();
            let expected: Vec<[u64; 2]> = elems.iter().map(|e| e.0 .0).collect();

            let bytes = elems.as_mut_bytes();
            let raw: &mut [u64] = <[u64]>::mut_from_bytes(bytes).unwrap();

            // 2 limbs per Fq element, so `raw.len() == elems.len() * 2`.
            assert_eq!(raw.len(), 4 * 2);
            for (i, chunk) in expected.iter().enumerate() {
                assert_eq!(raw[2 * i], chunk[0]);
                assert_eq!(raw[2 * i + 1], chunk[1]);
            }
        }
    }
}

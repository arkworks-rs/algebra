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
        //! `Fp<P, N>` is `#[repr(transparent)]` around `BigInt<N>`, which is
        //! `#[repr(transparent)]` around `[u64; N]`. These tests pin that down.

        use super::*;
        use ark_std::vec::Vec;
        use core::mem::{align_of, size_of};

        #[test]
        fn layout_matches_u64_array() {
            assert_eq!(size_of::<Fq>(), size_of::<[u64; 2]>());
            assert_eq!(align_of::<Fq>(), align_of::<[u64; 2]>());
        }

        #[test]
        fn as_u64_slice_roundtrips() {
            let elems: Vec<Fq> = (0..4u64).map(Fq::from).collect();
            let raw = Fq::as_u64_slice(&elems);
            assert_eq!(raw.len(), elems.len() * 2);

            // Each element's BigInt limbs must appear at the expected offset.
            for (i, elem) in elems.iter().enumerate() {
                let limbs: [u64; 2] = Fq::to_raw_u64_array(*elem);
                assert_eq!(raw[2 * i], limbs[0]);
                assert_eq!(raw[2 * i + 1], limbs[1]);
            }
        }

        #[test]
        fn from_raw_u64_array_roundtrip() {
            let original = Fq::from(12345u64);
            let limbs: [u64; 2] = Fq::to_raw_u64_array(original);
            let rebuilt: Fq = Fq::from_raw_u64_array(limbs);
            assert_eq!(original, rebuilt);
        }
    }
}

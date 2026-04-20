use ark_ff::define_field;

define_field!(modulus = "251", generator = "6", name = SmallFp8,);

define_field!(modulus = "65521", generator = "17", name = SmallFp16,);

// Mersenne13 prime 2^13 - 1
define_field!(modulus = "8191", generator = "17", name = SmallFp16M13,);

// Mersenne31 prime 2^31 - 1
define_field!(modulus = "2147483647", generator = "7", name = SmallFp32M31,);

// Babybear prime 2^31 - 2^27 + 1
define_field!(
    modulus = "2013265921",
    generator = "31",
    name = SmallFp32Babybear,
);

// KoalaBear prime 2^31 - 2^24 + 1
define_field!(
    modulus = "2130706433",
    generator = "3",
    name = SmallFp32Koalabear,
);

// Goldilocks prime 2^64 - 2^32 + 1
define_field!(
    modulus = "18446744069414584321",
    generator = "7",
    name = SmallFp64Goldilock,
);

#[cfg(test)]
mod tests {
    use super::*;
    use ark_algebra_test_templates::*;
    use ark_std::vec;

    test_small_field!(f8; SmallFp8);
    test_small_field!(f16; SmallFp16);
    test_small_field!(f16_mont_m13; SmallFp16M13);
    test_small_field!(f32; SmallFp32M31);
    test_small_field!(f32_mont_babybear; SmallFp32Babybear);
    test_small_field!(f32_mont_koalabear; SmallFp32Koalabear);
    test_small_field!(f64; SmallFp64Goldilock);

    mod const_constructors {
        use super::*;
        use ark_ff::{One, Zero};

        #[test]
        fn test_from_u128_zero() {
            let a: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(0);
            assert!(a.is_zero(), "from_u128(0) should be zero");
        }

        #[test]
        fn test_from_u128_one() {
            let a: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(1);
            assert!(a.is_one(), "from_u128(1) should be one");
        }

        #[test]
        fn test_from_u128_matches_runtime() {
            for val in [
                0u128,
                1,
                2,
                7,
                42,
                255,
                65521,
                2013265921,
                18446744069414584320,
            ] {
                let const_elem: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(val);
                let runtime_elem = SmallFp64Goldilock::from(val);
                assert_eq!(const_elem, runtime_elem, "from_u128({val}) mismatch");
            }
        }

        #[test]
        fn test_from_u128_all_backing_types() {
            // u8 field
            for val in [0u128, 1, 7, 42, 250] {
                assert_eq!(SmallFp8Config::from_u128(val), SmallFp8::from(val));
            }
            // u32 field (M31)
            for val in [0u128, 1, 7, 1000000, 2147483646] {
                assert_eq!(SmallFp32M31Config::from_u128(val), SmallFp32M31::from(val));
            }
        }

        #[test]
        fn test_from_u128_reduction() {
            let modulus = 18446744069414584321u128; // Goldilocks
            let val = modulus + 7;
            let const_elem: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(val);
            let seven: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(7);
            assert_eq!(
                const_elem, seven,
                "from_u128(P+7) should equal from_u128(7)"
            );
        }

        #[test]
        fn test_const_context() {
            const SEVEN: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(7);

            assert_eq!(SEVEN, SmallFp64Goldilock::from(7u128));
        }
    }

    mod raw_layout {
        //! `SmallFp<P>` is `#[repr(transparent)]` around `P::T` and derives
        //! `zerocopy::IntoBytes` / `Immutable` / `KnownLayout`. These tests
        //! pin the size/alignment contract and confirm `as_bytes()` works.

        use super::*;
        use ark_std::vec::Vec;
        use core::mem::{align_of, size_of};
        use zerocopy::IntoBytes;

        #[test]
        fn layout_matches_backing_integer() {
            assert_eq!(size_of::<SmallFp8>(), size_of::<u8>());
            assert_eq!(align_of::<SmallFp8>(), align_of::<u8>());

            assert_eq!(size_of::<SmallFp16>(), size_of::<u16>());
            assert_eq!(align_of::<SmallFp16>(), align_of::<u16>());

            assert_eq!(size_of::<SmallFp32M31>(), size_of::<u32>());
            assert_eq!(align_of::<SmallFp32M31>(), align_of::<u32>());

            assert_eq!(size_of::<SmallFp64Goldilock>(), size_of::<u64>());
            assert_eq!(align_of::<SmallFp64Goldilock>(), align_of::<u64>());
        }

        #[test]
        fn as_bytes_exposes_montgomery_limb_goldilocks() {
            let elems: Vec<SmallFp64Goldilock> =
                (0..8u64).map(SmallFp64Goldilock::from).collect();
            let bytes = elems.as_bytes();
            assert_eq!(bytes.len(), elems.len() * 8);
            for (i, elem) in elems.iter().enumerate() {
                let chunk: [u8; 8] = bytes[i * 8..(i + 1) * 8].try_into().unwrap();
                assert_eq!(u64::from_le_bytes(chunk), elem.value);
            }
        }
    }
}

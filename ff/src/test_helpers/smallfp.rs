use crate::define_field;

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

// NOTE: the property-based `test_small_field!` invocations live in
// `ff/tests/test_helpers_fixtures.rs` — see the comment in `fp128.rs` for why.

#[cfg(test)]
mod tests {
    use super::*;

    mod const_constructors {
        use super::*;
        use crate::{One, Zero};

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
}

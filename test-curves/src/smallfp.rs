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

// Goldilocks prime 2^64 - 2^32 + 1
define_field!(
    modulus = "18446744069414584321",
    generator = "7",
    name = SmallFp64Goldilock,
);

define_field!(
    modulus = "143244528689204659050391023439224324689",
    generator = "3",
    name = SmallFp128,
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
    test_small_field!(f64; SmallFp64Goldilock);
    test_small_field!(f128; SmallFp128);

    mod const_constructors {
        use super::*;
        use ark_ff::{PrimeField, Zero, One};

        // ---------- from_u128 ----------

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
            for val in [0u128, 1, 2, 7, 42, 255, 65521, 2013265921, 18446744069414584320] {
                let const_elem: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(val);
                let runtime_elem = SmallFp64Goldilock::from(val);
                assert_eq!(const_elem, runtime_elem, "from_u128({val}) mismatch");
            }
        }

        #[test]
        fn test_from_u128_u8_field() {
            for val in [0u128, 1, 7, 42, 250] {
                let const_elem: SmallFp8 = SmallFp8Config::from_u128(val);
                let runtime_elem = SmallFp8::from(val);
                assert_eq!(const_elem, runtime_elem, "u8 field from_u128({val}) mismatch");
            }
        }

        #[test]
        fn test_from_u128_u32_field() {
            for val in [0u128, 1, 7, 1000000, 2147483646] {
                let const_elem: SmallFp32M31 = SmallFp32M31Config::from_u128(val);
                let runtime_elem = SmallFp32M31::from(val);
                assert_eq!(const_elem, runtime_elem, "u32 M31 field from_u128({val}) mismatch");
            }
        }

        #[test]
        fn test_from_u128_u128_field() {
            for val in [0u128, 1, 7, u64::MAX as u128, 143244528689204659050391023439224324688] {
                let const_elem: SmallFp128 = SmallFp128Config::from_u128(val);
                let runtime_elem = SmallFp128::from(val);
                assert_eq!(const_elem, runtime_elem, "u128 field from_u128({val}) mismatch");
            }
        }

        #[test]
        fn test_from_u128_reduction() {
            // Value larger than modulus should be reduced
            let modulus = 18446744069414584321u128; // Goldilocks
            let val = modulus + 7;
            let const_elem: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(val);
            let seven: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(7);
            assert_eq!(const_elem, seven, "from_u128(P+7) should equal from_u128(7)");
        }

        // ---------- from_sign_and_limbs ----------

        #[test]
        fn test_from_sign_and_limbs_positive() {
            let a: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_sign_and_limbs(true, &[7]);
            let expected: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(7);
            assert_eq!(a, expected);
        }

        #[test]
        fn test_from_sign_and_limbs_negative() {
            let a: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_sign_and_limbs(false, &[1]);
            let one: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(1);
            assert_eq!(a, -one, "from_sign_and_limbs(false, [1]) should be -1");
        }

        #[test]
        fn test_from_sign_and_limbs_negative_zero() {
            let a: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_sign_and_limbs(false, &[0]);
            assert!(a.is_zero(), "-0 should be 0");
        }

        #[test]
        fn test_from_sign_and_limbs_two_limbs() {
            // Test with a value that spans two u64 limbs (for u128 field)
            let val: u128 = (1u128 << 64) + 42;
            let lo = val as u64;
            let hi = (val >> 64) as u64;
            let const_elem: SmallFp128 = SmallFp128Config::from_sign_and_limbs(true, &[lo, hi]);
            let runtime_elem = SmallFp128::from(val);
            assert_eq!(const_elem, runtime_elem, "two-limb from_sign_and_limbs mismatch");
        }

        // ---------- const context ----------

        #[test]
        fn test_const_context() {
            // Verify these are actually usable in const contexts
            const SEVEN: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_u128(7);
            const NEG_ONE: SmallFp64Goldilock = SmallFp64GoldilockConfig::from_sign_and_limbs(false, &[1]);

            let runtime_seven = SmallFp64Goldilock::from(7u128);
            let runtime_neg_one = -SmallFp64Goldilock::from(1u128);

            assert_eq!(SEVEN, runtime_seven);
            assert_eq!(NEG_ONE, runtime_neg_one);
        }
    }
}

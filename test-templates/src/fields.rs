#![allow(unused)]
#![allow(clippy::eq_op)]

use ark_std::rand::Rng;
#[derive(Default, Clone, Copy, Debug)]
pub struct DummyFlags;

impl ark_serialize::Flags for DummyFlags {
    const BIT_SIZE: usize = 200;

    fn u8_bitmask(&self) -> u8 {
        0
    }

    fn from_u8(_value: u8) -> Option<Self> {
        Some(DummyFlags)
    }
}

pub fn sum_of_products_test_helper<F: ark_ff::Field, const N: usize>(rng: &mut impl Rng) {
    let a: [_; N] = core::array::from_fn(|_| F::rand(rng));
    let b: [_; N] = core::array::from_fn(|_| F::rand(rng));
    let result_1 = F::sum_of_products(&a, &b);
    let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<F>();
    assert_eq!(result_1, result_2, "length: {N}");

    let two_inv = F::from(2u64).inverse().unwrap();
    let neg_one = -F::one();
    let a_max = neg_one * two_inv - F::one();
    let b_max = neg_one * two_inv - F::one();
    let a = [a_max; N];
    let b = [b_max; N];

    let result_1 = F::sum_of_products(&a, &b);
    let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<F>();
    assert_eq!(result_1, result_2, "length: {N}");
}

pub fn prime_field_sum_of_products_test_helper<F: ark_ff::PrimeField, const N: usize>(
    a_max: F,
    b_max: F,
) {
    let a = [a_max; N];
    let b = [b_max; N];
    let result_1 = F::sum_of_products(&a, &b);
    let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<F>();
    assert_eq!(result_1, result_2, "length: {N}");
}

#[macro_export]
#[doc(hidden)]
macro_rules! __test_field {
    ($field: ty) => {
        #[test]
        pub fn test_frobenius() {
            use ark_ff::Field;
            use ark_std::UniformRand;
            let mut rng = ark_std::test_rng();
            let characteristic = <$field>::characteristic();
            let max_power = (<$field>::extension_degree() + 1) as usize;

            for _ in 0..ITERATIONS {
                let a = <$field>::rand(&mut rng);

                let mut a_0 = a;
                a_0.frobenius_map_in_place(0);
                assert_eq!(a, a_0);
                assert_eq!(a, a.frobenius_map(0));

                let mut a_q = a.pow(&characteristic);
                for power in 1..max_power {
                    assert_eq!(a_q, a.frobenius_map(power));

                    let mut a_qi = a;
                    a_qi.frobenius_map_in_place(power);
                    assert_eq!(a_qi, a_q, "failed on power {}", power);

                    a_q = a_q.pow(&characteristic);
                }
            }
        }

        #[test]
        fn test_serialization() {
            use ark_serialize::*;
            use ark_std::UniformRand;
            for compress in [Compress::Yes, Compress::No] {
                for validate in [Validate::Yes, Validate::No] {
                    let buf_size = <$field>::zero().serialized_size(compress);

                    let buffer_size =
                        buffer_bit_byte_size(<$field as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize).1 *
                        (<$field>::extension_degree() as usize);
                    assert_eq!(buffer_size, buf_size);

                    let mut rng = ark_std::test_rng();

                    for _ in 0..ITERATIONS {
                        let a = <$field>::rand(&mut rng);
                        {
                            let mut serialized = vec![0u8; buf_size];
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_mode(&mut cursor, compress).unwrap();

                            let mut cursor = Cursor::new(&serialized[..]);
                            let b = <$field>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                            assert_eq!(a, b);
                        }



                        {
                            let mut serialized = vec![0; buf_size];
                            let result = matches!(
                                a.serialize_with_flags(&mut &mut serialized[..], $crate::fields::DummyFlags).unwrap_err(),
                                SerializationError::NotEnoughSpace
                            );
                            assert!(result);

                            let result = matches!(
                                <$field>::deserialize_with_flags::<_, $crate::fields::DummyFlags>(&mut &serialized[..]).unwrap_err(),
                                SerializationError::NotEnoughSpace,
                            );
                            assert!(result);

                            {
                                let mut serialized = vec![0; buf_size - 1];
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap_err();

                                let mut cursor = Cursor::new(&serialized[..]);
                                <$field>::deserialize_with_mode(&mut cursor, compress, validate).unwrap_err();
                            }
                        }
                    }
                }
            }

        }

        #[test]
        fn test_add_properties() {
            use ark_std::UniformRand;
            let mut rng = test_rng();
            let zero = <$field>::zero();
            assert_eq!(-zero, zero);
            assert!(zero.is_zero());
            assert!(<$field>::ZERO.is_zero());
            assert_eq!(<$field>::ZERO, zero);

            for _ in 0..(ITERATIONS * ITERATIONS) {
                // Associativity
                let a = <$field>::rand(&mut rng);
                let b = <$field>::rand(&mut rng);
                let c = <$field>::rand(&mut rng);

                assert_eq!((a + b) + c, a + (b + c));

                // Commutativity
                assert_eq!(a + b, b + a);

                // Identity
                assert_eq!(zero + a, a);
                assert_eq!(zero + b, b);
                assert_eq!(zero + c, c);

                // Negation
                assert_eq!(-a + a, zero);
                assert_eq!(-b + b, zero);
                assert_eq!(-c + c, zero);
                assert_eq!(-zero, zero);

                // Associativity and commutativity simultaneously
                let t0 = (a + &b) + &c; // (a + b) + c
                let t1 = (a + &c) + &b; // (a + c) + b
                let t2 = (b + &c) + &a; // (b + c) + a

                assert_eq!(t0, t1);
                assert_eq!(t1, t2);

                // Doubling
                assert_eq!(a.double(), a + a);
                assert_eq!(b.double(), b + b);
                assert_eq!(c.double(), c + c);
            }
        }

        #[test]
        fn test_sub_properties() {
            use ark_std::UniformRand;
            let mut rng = test_rng();
            let zero = <$field>::zero();

            for _ in 0..(ITERATIONS * ITERATIONS){
                // Anti-commutativity
                let a = <$field>::rand(&mut rng);
                let b = <$field>::rand(&mut rng);
                assert!(((a - b) + (b - a)).is_zero());

                // Identity
                assert_eq!(zero - a, -a);
                assert_eq!(zero - b, -b);

                assert_eq!(a - zero, a);
                assert_eq!(b - zero, b);
            }
        }

        #[test]
        fn test_mul_properties() {
            use ark_std::UniformRand;
            let mut rng = test_rng();
            let zero = <$field>::zero();
            let one = <$field>::one();
            assert_eq!(one.inverse().unwrap(), one, "One inverse failed");
            assert!(one.is_one(), "One is not one");

            assert!(<$field>::ONE.is_one(), "One constant is not one");
            assert_eq!(<$field>::ONE, one, "One constant is incorrect");

            for _ in 0..ITERATIONS {
                // Associativity
                let a = <$field>::rand(&mut rng);
                let b = <$field>::rand(&mut rng);
                let c = <$field>::rand(&mut rng);
                assert_eq!((a * b) * c, a * (b * c), "Associativity failed");

                // Commutativity
                assert_eq!(a * b, b * a, "Commutativity failed");

                // Identity
                assert_eq!(one * a, a, "Identity mul failed");
                assert_eq!(one * b, b, "Identity mul failed");
                assert_eq!(one * c, c, "Identity mul failed");

                assert_eq!(zero * a, zero, "Mul by zero failed");
                assert_eq!(zero * b, zero, "Mul by zero failed");
                assert_eq!(zero * c, zero, "Mul by zero failed");

                // Inverses
                assert_eq!(a * a.inverse().unwrap(), one, "Mul by inverse failed");
                assert_eq!(b * b.inverse().unwrap(), one, "Mul by inverse failed");
                assert_eq!(c * c.inverse().unwrap(), one, "Mul by inverse failed");

                // Associativity and commutativity simultaneously
                let t0 = (a * b) * c;
                let t1 = (a * c) * b;
                let t2 = (b * c) * a;
                assert_eq!(t0, t1, "Associativity + commutativity failed");
                assert_eq!(t1, t2, "Associativity + commutativity failed");

                // Squaring
                assert_eq!(a * a, a.square(), "Squaring failed");
                assert_eq!(b * b, b.square(), "Squaring failed");
                assert_eq!(c * c, c.square(), "Squaring failed");

                // Distributivity
                assert_eq!(a * (b + c), a * b + a * c, "Distributivity failed");
                assert_eq!(b * (a + c), b * a + b * c, "Distributivity failed");
                assert_eq!(c * (a + b), c * a + c * b, "Distributivity failed");
                assert_eq!((a + b).square(), a.square() + b.square() + a * b.double(), "Distributivity for square failed");
                assert_eq!((b + c).square(), c.square() + b.square() + c * b.double(), "Distributivity for square failed");
                assert_eq!((c + a).square(), a.square() + c.square() + a * c.double(), "Distributivity for square failed");
            }
        }

        #[test]
        fn test_pow() {
            use ark_std::UniformRand;
            let mut rng = test_rng();
            for _ in 0..(ITERATIONS / 10) {
                for i in 0..20 {
                    // Exponentiate by various small numbers and ensure it is
                    // consistent with repeated multiplication.
                    let a = <$field>::rand(&mut rng);
                    let target = a.pow(&[i]);
                    let mut c = <$field>::one();
                    for _ in 0..i {
                        c *= a;
                    }
                    assert_eq!(c, target);

                }
                let a = <$field>::rand(&mut rng);

                // Exponentiating by the modulus should have no effect;
                let mut result = a;
                for i in 0..<$field>::extension_degree() {
                    result = result.pow(<$field>::characteristic())
                }
                assert_eq!(a, result);

                // Commutativity
                let e1: [u64; 10] = rng.gen();
                let e2: [u64; 10] = rng.gen();
                assert_eq!(a.pow(&e1).pow(&e2), a.pow(&e2).pow(&e1));

                // Distributivity
                let e3: [u64; 10] = rng.gen();
                let a_to_e1 = a.pow(e1);
                let a_to_e2 = a.pow(e2);
                let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                assert_eq!(a_to_e1_plus_e2.pow(&e3), a_to_e1.pow(&e3) * a_to_e2.pow(&e3));
            }
        }

        #[test]
        fn test_sum_of_products_tests() {
            use ark_std::{UniformRand, rand::Rng};
            let rng = &mut test_rng();

            for _ in 0..ITERATIONS {
                $crate::fields::sum_of_products_test_helper::<$field, 1>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 2>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 3>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 4>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 5>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 6>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 7>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 8>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 9>(rng);
                $crate::fields::sum_of_products_test_helper::<$field, 10>(rng);
            }
        }

        #[test]
        fn test_sqrt() {
            if <$field>::SQRT_PRECOMP.is_some() {
                use ark_std::UniformRand;
                let rng = &mut test_rng();

                assert!(<$field>::zero().sqrt().unwrap().is_zero());

                for _ in 0..ITERATIONS {
                    // Ensure sqrt(a^2) = a or -a
                    let a = <$field>::rand(rng);
                    let b = a.square();
                    let sqrt = b.sqrt().unwrap();
                    assert!(a == sqrt || -a == sqrt);

                    if let Some(mut b) = a.sqrt() {
                        b.square_in_place();
                        assert_eq!(a, b);
                    }

                    let a = <$field>::rand(rng);
                    let b = a.square();
                    assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);
                }
            }
        }
    };
    ($field: ty; fft) => {
        $crate::__test_field!($field);

        #[test]
        fn test_fft() {
            use ark_ff::FftField;
            assert_eq!(
                <$field>::TWO_ADIC_ROOT_OF_UNITY.pow([1 << <$field>::TWO_ADICITY]),
                <$field>::one()
            );

            if let Some(small_subgroup_base) = <$field>::SMALL_SUBGROUP_BASE {
                let small_subgroup_base_adicity = <$field>::SMALL_SUBGROUP_BASE_ADICITY.unwrap();
                let large_subgroup_root_of_unity = <$field>::LARGE_SUBGROUP_ROOT_OF_UNITY.unwrap();
                let pow =
                (1 << <$field>::TWO_ADICITY) * (small_subgroup_base as u64).pow(small_subgroup_base_adicity);
                assert_eq!(large_subgroup_root_of_unity.pow([pow]), <$field>::one());

                for i in 0..=<$field>::TWO_ADICITY {
                    for j in 0..=small_subgroup_base_adicity {
                        let size = (1u64 << i) * (small_subgroup_base as u64).pow(j);
                        let root = <$field>::get_root_of_unity(size as u64).unwrap();
                        assert_eq!(root.pow([size as u64]), <$field>::one());
                    }
                }
            } else {
                for i in 0..=<$field>::TWO_ADICITY {
                    let size = 1 << i;
                    let root = <$field>::get_root_of_unity(size).unwrap();
                    assert_eq!(root.pow([size as u64]), <$field>::one());
                }
            }
        }
    };
    ($field: ty; prime) => {
        $crate::__test_field!($field; fft);

        #[test]
        fn test_sum_of_products_edge_case() {
            use ark_ff::BigInteger;
            let mut a_max = <$field>::ZERO.into_bigint();
            for (i, limb) in a_max.as_mut().iter_mut().enumerate() {
                if i == <$field as PrimeField>::BigInt::NUM_LIMBS - 1 {
                    let mod_num_bits_mod_64 =
                        64 * <$field as PrimeField>::BigInt::NUM_LIMBS
                        - (<$field as PrimeField>::MODULUS_BIT_SIZE as usize);
                    if mod_num_bits_mod_64 == 63 {
                        *limb = 0u64;
                    } else {
                        *limb = u64::MAX >> (mod_num_bits_mod_64 + 1);
                    }
                } else {
                    *limb = u64::MAX;
                }
            }
            let a_max = <$field>::from_bigint(a_max).unwrap();
            let b_max = -<$field>::one(); // p - 1.

            $crate::fields::prime_field_sum_of_products_test_helper::<_, 1>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 2>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 3>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 4>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 5>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 6>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 7>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 8>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 9>(a_max, b_max);
            $crate::fields::prime_field_sum_of_products_test_helper::<_, 10>(a_max, b_max);
        }

        #[test]
        fn test_constants() {
            use ark_ff::{FpConfig, BigInteger, SqrtPrecomputation};
            use $crate::num_bigint::BigUint;
            use $crate::num_integer::Integer;

            let modulus: BigUint = <$field>::MODULUS.into();
            let modulus_minus_one = &modulus - 1u8;
            assert_eq!(BigUint::from(<$field>::MODULUS_MINUS_ONE_DIV_TWO), &modulus_minus_one / 2u32);
            assert_eq!(<$field>::MODULUS_BIT_SIZE as u64, modulus.bits());
            if let Some(SqrtPrecomputation::Case3Mod4 { modulus_plus_one_div_four }) = <$field>::SQRT_PRECOMP {
                // Handle the case where `(MODULUS + 1) / 4`
                // has fewer limbs than `MODULUS`.
                let check = ((&modulus + 1u8) / 4u8).to_u64_digits();
                let len = check.len();
                assert_eq!(&modulus_plus_one_div_four[..len], &check);
                assert!(modulus_plus_one_div_four[len..].iter().all(|l| *l == 0));
            }

            let mut two_adicity = 0;
            let mut trace = modulus_minus_one;
            while trace.is_even() {
                trace /= 2u8;
                two_adicity += 1;
            }
            assert_eq!(two_adicity, <$field>::TWO_ADICITY);
            assert_eq!(BigUint::from(<$field>::TRACE), trace);
            let trace_minus_one_div_two = (&trace - 1u8) / 2u8;
            assert_eq!(BigUint::from(<$field>::TRACE_MINUS_ONE_DIV_TWO), trace_minus_one_div_two);

            let two_adic_root_of_unity: BigUint = <$field>::TWO_ADIC_ROOT_OF_UNITY.into();
            let generator: BigUint = <$field>::GENERATOR.into_bigint().into();
            assert_eq!(two_adic_root_of_unity, generator.modpow(&trace, &modulus));
            match (<$field>::SMALL_SUBGROUP_BASE, <$field>::SMALL_SUBGROUP_BASE_ADICITY) {
                (Some(base), Some(adicity)) => {
                    let mut e = generator;
                    for _i in 0..adicity {
                        e = e.modpow(&base.into(), &modulus)
                    }
                },
                (None, None) => {},
                (_, _) => {
                    panic!("Should specify both `SMALL_SUBGROUP_BASE` and `SMALL_SUBGROUP_BASE_ADICITY`")
                },
            }
        }
    };
    ($field: ty; mont_prime_field) => {
        $crate::__test_field!($field; prime);

        #[test]
        pub fn test_montgomery_config() {
            use ark_ff::{FpConfig, BigInteger};
            use $crate::num_bigint::{BigUint, BigInt};
            use $crate::num_integer::Integer;
            use $crate::num_traits::{Signed, cast::ToPrimitive};

            let limbs = <$field as PrimeField>::BigInt::NUM_LIMBS;
            let modulus: BigUint = <$field>::MODULUS.into();
            let r = BigUint::from(2u8).modpow(&((limbs * 64) as u64).into(), &modulus);
            let r2 = (&r * &r) % &modulus;
            let inv = {
                // We compute this as follows.
                // First, MODULUS mod 2^64 is just the lower 64 bits of MODULUS.
                // Hence MODULUS mod 2^64 = MODULUS.0[0] mod 2^64.
                //
                // Next, computing the inverse mod 2^64 involves exponentiating by
                // the multiplicative group order, which is euler_totient(2^64) - 1.
                // Now, euler_totient(2^64) = 1 << 63, and so
                // euler_totient(2^64) - 1 = (1 << 63) - 1 = 1111111... (63 digits).
                // We compute this powering via standard square and multiply.
                let mut inv = 1u128;
                let two_to_64 = 1u128 << 64;
                for _ in 0..63 {
                    // Square
                    inv = inv.checked_mul(inv).unwrap() % two_to_64;
                    // Multiply
                    inv = inv.checked_mul(<$field>::MODULUS.0[0] as u128).unwrap() % &two_to_64;
                };
                let mut inv = inv as i128;
                let two_to_64 = two_to_64 as i128;
                inv = (-inv) % two_to_64;
                inv as u64
            };
            let group_order = 0b111111111111111111111111111111111111111111111111111111111111111u64;
            let group_order_lower = ((group_order << 32) >> 32) as u32; // clear the upper 32 bits
            let group_order_upper = ((group_order) >> 32) as u32; // drop the lower 32 bits
            let modulus_lower_limb = <$field>::MODULUS.0[0];
            let modulus_lower_limb_to2_32 = modulus_lower_limb.wrapping_pow(u32::MAX).wrapping_mul(modulus_lower_limb);
            let inv2 = modulus_lower_limb
                .wrapping_pow(group_order_lower)
                .wrapping_mul(modulus_lower_limb_to2_32.wrapping_pow(group_order_upper))
                .wrapping_neg();

            assert_eq!(r, <$field>::R.into());
            assert_eq!(r2, <$field>::R2.into());
            assert_eq!(inv, u64::from(<$field>::INV));
            assert_eq!(inv2, <$field>::INV);
        }
    }
}

#[macro_export]
macro_rules! test_field {
    ($mod_name: ident; $field: ty $(; $tail:tt)*) => {
        mod $mod_name {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand};
            const ITERATIONS: usize = 1000;

            $crate::__test_field!($field $(; $tail)*);
        }
    };
}

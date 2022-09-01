#![allow(unused)]
#![allow(clippy::eq_op)]
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
                a_0.frobenius_map(0);
                assert_eq!(a, a_0);

                let mut a_q = a.pow(&characteristic);
                for power in 1..max_power {
                    let mut a_qi = a;
                    a_qi.frobenius_map(power);
                    assert_eq!(a_qi, a_q, "failed on power {}", power);

                    a_q = a_q.pow(&characteristic);
                }
            }
        }

        #[test]
        fn test_serialization() {
            use ark_serialize::*;
            use ark_std::UniformRand;
            let buf_size = <$field>::zero().serialized_size();

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
                    a.serialize(&mut cursor).unwrap();

                    let mut cursor = Cursor::new(&serialized[..]);
                    let b = <$field>::deserialize(&mut cursor).unwrap();
                    assert_eq!(a, b);
                }

                {
                    let mut serialized = vec![0u8; a.uncompressed_size()];
                    let mut cursor = Cursor::new(&mut serialized[..]);
                    a.serialize_uncompressed(&mut cursor).unwrap();

                    let mut cursor = Cursor::new(&serialized[..]);
                    let b = <$field>::deserialize_uncompressed(&mut cursor).unwrap();
                    assert_eq!(a, b);
                }

                {
                    let mut serialized = vec![0u8; buf_size + 1];
                    let mut cursor = Cursor::new(&mut serialized[..]);
                    a.serialize_with_flags(&mut cursor, SWFlags::from_y_sign(true))
                    .unwrap();
                    let mut cursor = Cursor::new(&serialized[..]);
                    let (b, flags) = <$field>::deserialize_with_flags::<_, SWFlags>(&mut cursor).unwrap();
                    assert_eq!(flags.is_positive(), Some(true));
                    assert!(!flags.is_infinity());
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
                        a.serialize(&mut cursor).unwrap_err();

                        let mut cursor = Cursor::new(&serialized[..]);
                        <$field>::deserialize(&mut cursor).unwrap_err();
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
            assert_eq!(one.inverse().unwrap(), one);
            assert!(one.is_one());

            assert!(<$field>::ONE.is_one());
            assert_eq!(<$field>::ONE, one);

            for _ in 0..ITERATIONS {
                // Associativity
                let a = <$field>::rand(&mut rng);
                let b = <$field>::rand(&mut rng);
                let c = <$field>::rand(&mut rng);
                assert_eq!((a * b) * c, a * (b * c));

                // Commutativity
                assert_eq!(a * b, b * a);

                // Identity
                assert_eq!(one * a, a);
                assert_eq!(one * b, b);
                assert_eq!(one * c, c);

                assert_eq!(zero * a, zero);
                assert_eq!(zero * b, zero);
                assert_eq!(zero * c, zero);

                // Inverses
                assert_eq!(a * a.inverse().unwrap(), one);
                assert_eq!(b * b.inverse().unwrap(), one);
                assert_eq!(c * c.inverse().unwrap(), one);

                // Associativity and commutativity simultaneously
                let t0 = (a * b) * c;
                let t1 = (a * c) * b;
                let t2 = (b * c) * a;
                assert_eq!(t0, t1);
                assert_eq!(t1, t2);

                // Squaring
                assert_eq!(a * a, a.square());
                assert_eq!(b * b, b.square());
                assert_eq!(c * c, c.square());

                // Distributivity
                assert_eq!(a * (b + c), a * b + a * c);
                assert_eq!(b * (a + c), b * a + b * c);
                assert_eq!(c * (a + b), c * a + c * b);
                assert_eq!((a + b).square(), a.square() + b.square() + a * b.double());
                assert_eq!((b + c).square(), c.square() + b.square() + c * b.double());
                assert_eq!((c + a).square(), a.square() + c.square() + a * c.double());
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
            use ark_std::UniformRand;
            let rng = &mut test_rng();
            for _ in 0..ITERATIONS {
                for length in 1..20 {
                    let a = (0..length).map(|_| <$field>::rand(rng)).collect::<Vec<_>>();
                    let b = (0..length).map(|_| <$field>::rand(rng)).collect::<Vec<_>>();
                    let result_1 = <$field>::sum_of_products(&a, &b);
                    let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<$field>();
                    assert_eq!(result_1, result_2, "length: {length}");
                }

                let two_inv = <$field>::from(2u64).inverse().unwrap();
                let neg_one = -<$field>::one();
                let a_max = neg_one * two_inv - <$field>::one();
                let b_max = neg_one * two_inv - <$field>::one();
                for length in 1..20 {
                    let a = vec![a_max; length];
                    let b = vec![b_max; length];
                    let result_1 = <$field>::sum_of_products(&a, &b);
                    let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<$field>();
                    assert_eq!(result_1, result_2, "length: {length}");
                }
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

                for i in 0..<$field>::TWO_ADICITY {
                    for j in 0..small_subgroup_base_adicity {
                        use core::convert::TryFrom;
                        let size = usize::try_from(1 << i as usize).unwrap()
                        * usize::try_from((small_subgroup_base as u64).pow(j)).unwrap();
                        let root = <$field>::get_root_of_unity(size as u64).unwrap();
                        assert_eq!(root.pow([size as u64]), <$field>::one());
                    }
                }
            } else {
                for i in 0..<$field>::TWO_ADICITY {
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
                    *limb = u64::MAX >> (64 - ((<$field>::MODULUS_BIT_SIZE - 1) % 64));
                } else {
                    *limb = u64::MAX;
                }
            }
            let a_max = <$field>::from_bigint(a_max).unwrap();
            let b_max = -<$field>::one(); // p - 1.
            for length in 1..100 {
                let a = vec![a_max; length];
                let b = vec![b_max; length];
                let result_1 = <$field>::sum_of_products(&a, &b);
                let result_2 = a.into_iter().zip(b).map(|(a, b)| a * b).sum::<$field>();
                assert_eq!(result_1, result_2, "length: {length}");
            }
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
                assert_eq!(modulus_plus_one_div_four, &((&modulus + 1u8) / 4u8).to_u64_digits());
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
            assert_eq!(inv, <$field>::INV.into());
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
            use ark_serialize::{buffer_bit_byte_size, Flags, SWFlags};
            use ark_std::{io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand};
            const ITERATIONS: usize = 1000;

            $crate::__test_field!($field $(; $tail)*);
        }
    };
}

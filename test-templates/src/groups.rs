#[macro_export]
#[doc(hidden)]
macro_rules! __test_group {
    ($group: ty) => {
        type ScalarField = <$group as Group>::ScalarField;
        #[test]
        fn test_add_properties() {
            let mut rng = &mut ark_std::test_rng();
            let zero = <$group>::zero();
            for _ in 0..ITERATIONS {
                let a = <$group>::rand(rng);
                let b = <$group>::rand(rng);
                let c = <$group>::rand(rng);

                // Associativity
                assert_eq!((a + b) + c, a + (b + c));

                // Commutativity
                assert_eq!(a + b, b + a);

                // Identity
                assert_eq!(zero + a, a);
                assert_eq!(zero + b, b);
                assert_eq!(zero + c, c);
                assert_eq!(a + zero, a);
                assert_eq!(b + zero, b);
                assert_eq!(c + zero, c);

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
                assert_eq!(zero.double(), zero);
                assert_eq!((-zero).double(), zero);
            }
        }

        #[test]
        fn test_sub_properties() {
            use ark_std::UniformRand;
            let mut rng = test_rng();
            let zero = <$group>::zero();

            for _ in 0..ITERATIONS{
                // Anti-commutativity
                let a = <$group>::rand(&mut rng);
                let b = <$group>::rand(&mut rng);
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
            let zero = ScalarField::zero();
            let one = ScalarField::one();
            assert_eq!(one.inverse().unwrap(), one);
            assert!(one.is_one());

            for _ in 0..ITERATIONS {
                // Associativity
                let a = <$group>::rand(&mut rng);
                let b = ScalarField::rand(&mut rng);
                let c = ScalarField::rand(&mut rng);
                assert_eq!((a * b) * c, a * (b * c));

                // Identity
                assert_eq!(a * one, a);

                assert_eq!(a * zero, <$group>::zero());

                // Inverses
                assert_eq!((a * b.inverse().unwrap()) * b, a);

                // Distributivity
                assert_eq!(a * (b + c), a * b + a * c);

                // s ( a + b) using wNAF for several window values in [2,5]
                for w in 2..=5 {
                    let context = WnafContext::new(w);
                    assert_eq!(a * b, context.mul(a, &b));

                    let table = context.table(a);
                    assert_eq!(a * b, context.mul_with_table(&table, &b).unwrap());

                    if w > 2 {
                        let bad_context = WnafContext::new(w - 1);
                        let bad_table = bad_context.table(a);
                        assert_eq!(context.mul_with_table(&bad_table, &b), None);
                    }
                }
            }
        }

        #[test]
        fn test_serialization() {
            for compress in [Compress::Yes, Compress::No] {
                for validate in [Validate::Yes, Validate::No] {
                    let buf_size = <$group>::zero().serialized_size(compress);

                    let mut rng = ark_std::test_rng();

                    for _ in 0..ITERATIONS {
                        let a = <$group>::rand(&mut rng);
                        {
                            let mut serialized = vec![0; buf_size];
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_mode(&mut cursor, compress).unwrap();

                            let mut cursor = Cursor::new(&serialized[..]);
                            let b = <$group>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                            assert_eq!(a, b);
                        }

                        {
                            let a = <$group>::zero();
                            let mut serialized = vec![0; buf_size];
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_mode(&mut cursor, compress).unwrap();
                            let mut cursor = Cursor::new(&serialized[..]);
                            let b = <$group>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                            assert_eq!(a, b);
                        }

                        {
                            let a = <$group>::zero();
                            let mut serialized = vec![0; buf_size - 1];
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                        }

                        {
                            let serialized = vec![0; buf_size - 1];
                            let mut cursor = Cursor::new(&serialized[..]);
                            <$group>::deserialize_with_mode(&mut cursor, compress, validate).unwrap_err();
                        }
                    }
                }
            }
        }
    };
    ($group:ty; msm) => {
        #[test]
        fn test_var_base_msm() {
            $crate::msm::test_var_base_msm::<$group>();
        }

        #[test]
        fn test_chunked_pippenger() {
            $crate::msm::test_chunked_pippenger::<$group>();
        }

        #[test]
        fn test_hashmap_pippenger() {
            $crate::msm::test_hashmap_pippenger::<$group>();
        }
    };
    ($group:ty; curve) => {
        $crate::__test_group!($group);
        $crate::__test_group!($group; msm);
        type Affine = <$group as CurveGroup>::Affine;
        type Config = <$group as CurveGroup>::Config;
        type BaseField = <$group as CurveGroup>::BaseField;

        #[test]
        fn test_affine_conversion() {
            let mut rng = &mut ark_std::test_rng();

            for _ in 0..ITERATIONS {
                let g = <$group>::rand(&mut rng);
                let g_affine = g.into_affine();
                let g_projective = g_affine.into_group();
                assert_eq!(g, g_projective);
            }

            // Batch normalization
            for _ in 0..10 {
                let mut v = (0..ITERATIONS)
                    .map(|_| <$group>::rand(&mut rng).double())
                    .collect::<Vec<_>>();

                use ark_std::rand::distributions::{Distribution, Uniform};
                let between = Uniform::from(0..ITERATIONS);
                // Sprinkle in some normalized points
                for _ in 0..5 {
                    v[between.sample(&mut rng)] = <$group>::zero();
                }
                for _ in 0..5 {
                    let s = between.sample(&mut rng);
                    v[s] = v[s].into_affine().into_group();
                }

                let expected_v = v.iter().map(|v| v.into_affine()).collect::<Vec<_>>();
                let actual_v = <$group>::normalize_batch(&v);

                assert_eq!(actual_v, expected_v);
            }
        }

        #[test]
        fn test_cofactor_ops() {
            let rng = &mut ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a = Affine::rand(rng);
                assert_eq!(a.mul_by_cofactor_to_group(), a.mul_bigint(&Config::COFACTOR));
                assert_eq!(a.mul_by_cofactor(), a.mul_bigint(&Config::COFACTOR));
                assert_eq!(a.mul_by_cofactor().mul_by_cofactor_inv(), a);
                assert_eq!(a.mul_by_cofactor_inv().mul_by_cofactor(), a);
                assert_eq!(a.mul_by_cofactor_inv(), a * Config::COFACTOR_INV);

                assert!(a.clear_cofactor().is_in_correct_subgroup_assuming_on_curve());
            }
        }

        #[test]
        fn test_mixed_addition() {
            let rng = &mut ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a = Affine::rand(rng);
                let a_group = a.into_group();
                let b = <$group>::rand(rng);
                assert!(a.is_on_curve());
                assert!(b.into_affine().is_on_curve());
                assert_eq!(b + a, b + a_group, "b + a failed on input {a}, {b}");
                assert_eq!(a + b, a_group + b, "a + b failed on input {a}, {b}");
            }
        }
    };
    ($group:ty; sw) => {
        $crate::__test_group!($group; curve);

        #[test]
        fn test_sw_properties() {
            let mut rng = &mut ark_std::test_rng();

            let generator = <$group>::generator().into_affine();
            assert!(generator.is_on_curve());
            assert!(generator.is_in_correct_subgroup_assuming_on_curve());

            for i in 0.. {
                let x = BaseField::from(i);
                // y^2 = x^3 + a * x + b
                let rhs = x * x.square() + x * <Config as SWCurveConfig>::COEFF_A + <Config as SWCurveConfig>::COEFF_B;

                if let Some(y) = rhs.sqrt() {
                    let p = Affine::new_unchecked(x, if y < -y { y } else { -y });
                    if !<<$group as CurveGroup>::Config as CurveConfig>::cofactor_is_one() {
                        if p.is_in_correct_subgroup_assuming_on_curve() {
                            continue;
                        }
                    }

                    let g1 = p.mul_by_cofactor_to_group();
                    if !g1.is_zero() {
                        let g1 = Affine::from(g1);
                        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
                        break;
                    }
                }
            }

            for _ in 0..ITERATIONS {
                let f = BaseField::rand(rng);
                assert_eq!(<Config as SWCurveConfig>::mul_by_a(f), f * <Config as SWCurveConfig>::COEFF_A);
                assert_eq!(<Config as SWCurveConfig>::add_b(f), f + <Config as SWCurveConfig>::COEFF_B);
            }
            {
                use ark_ec::models::short_weierstrass::SWFlags;
                for compress in [Compress::Yes, Compress::No] {
                    for flag in [SWFlags::PointAtInfinity, SWFlags::YIsNegative, SWFlags::YIsPositive] {
                        let a = BaseField::rand(&mut rng);
                        let buf_size = a.serialized_size(compress);
                        let mut serialized = vec![0u8; buf_size + 1];
                        let mut cursor = Cursor::new(&mut serialized[..]);
                        a.serialize_with_flags(&mut cursor, flag)
                        .unwrap();
                        let mut cursor = Cursor::new(&serialized[..]);
                        let (b, flags) = BaseField::deserialize_with_flags::<_, SWFlags>(&mut cursor).unwrap();
                        assert_eq!(flags, flag);
                        assert_eq!(a, b);
                    }

                }
            }
        }
    };
    ($group:ty; te) => {
        $crate::__test_group!($group; curve);

        #[test]
        fn test_te_properties() {
            let mut rng = &mut ark_std::test_rng();

            let generator = <$group>::generator().into_affine();
            assert!(generator.is_on_curve());
            assert!(generator.is_in_correct_subgroup_assuming_on_curve());
            let mut y = BaseField::zero();
            let one = BaseField::one();
            for _ in 0..ITERATIONS {
                let f = BaseField::rand(rng);
                assert_eq!(<Config as TECurveConfig>::mul_by_a(f), f * <Config as TECurveConfig>::COEFF_A);
            }
            {
                use ark_ec::models::twisted_edwards::TEFlags;
                for compress in [Compress::Yes, Compress::No] {
                    for flag in [TEFlags::XIsPositive, TEFlags::XIsNegative] {
                        let a = BaseField::rand(&mut rng);
                        let buf_size = a.serialized_size(compress);
                        let mut serialized = vec![0u8; buf_size + 1];
                        let mut cursor = Cursor::new(&mut serialized[..]);
                        a.serialize_with_flags(&mut cursor, flag)
                        .unwrap();
                        let mut cursor = Cursor::new(&serialized[..]);
                        let (b, flags) = BaseField::deserialize_with_flags::<_, TEFlags>(&mut cursor).unwrap();
                        assert_eq!(flags, flag);
                        assert_eq!(a, b);
                    }

                }
            }
        }

        #[test]
        fn test_montgomery_conversion_test()
        {
            use ark_ec::twisted_edwards::MontCurveConfig;
            // A = 2 * (a + d) / (a - d)
            let a = <Config as CurveConfig>::BaseField::one().double()
                * &(<Config as TECurveConfig>::COEFF_A + &<Config as TECurveConfig>::COEFF_D)
                * &(<Config as TECurveConfig>::COEFF_A - &<Config as TECurveConfig>::COEFF_D).inverse().unwrap();
            // B = 4 / (a - d)
            let b = <Config as CurveConfig>::BaseField::one().double().double() *
                &(<Config as TECurveConfig>::COEFF_A - &<Config as TECurveConfig>::COEFF_D).inverse().unwrap();

            assert_eq!(a, <Config as MontCurveConfig>::COEFF_A);
            assert_eq!(b, <Config as MontCurveConfig>::COEFF_B);
        }
    }
}

#[macro_export]
macro_rules! test_group {
    ($mod_name: ident; $group: ty $(; $tail:tt)*) => {
        mod $mod_name {
            use super::*;
            use ark_ff::*;
            use ark_ec::{Group, CurveGroup, ScalarMul, AffineRepr, CurveConfig, short_weierstrass::SWCurveConfig, twisted_edwards::TECurveConfig, scalar_mul::{*, wnaf::*}};
            use ark_serialize::*;
            use ark_std::{io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand};
            const ITERATIONS: usize = 500;

            $crate::__test_group!($group $(; $tail)*);
        }
    };
}

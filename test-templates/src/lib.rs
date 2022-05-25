pub mod curves;
pub mod fields;
pub mod groups;
pub mod msm;

#[macro_export]
macro_rules! generate_g1_test {
    () => {};

    (curve_tests; $($tail:tt)*) => {
        #[test]
        fn test_g1_projective_curve() {
            curve_tests::<G1Projective>();
        }
        generate_g1_test!($($tail)*);
    };

    (sw_tests; $($tail:tt)*) => {
        #[test]
        fn test_g1_projective_sw() {
            sw_tests::<g1::Parameters>();
        }
        generate_g1_test!($($tail)*);
    };


    (edwards_tests; $($tail:tt)*) => {
        #[test]
        fn test_g1_projective_edwards() {
            edwards_tests::<g1::Parameters>();
        }
        generate_g1_test!($($tail)*);
    };

    (te_group_tests; $($tail:tt)*) => {
        #[test]
        fn test_g1_projective_te_group() {
            let mut rng = ark_std::test_rng();
            let c = rng.gen();
            let d = rng.gen();
            group_test::<G1TEProjective>(c, d);
        }
        generate_g1_test!($($tail)*);
    };

    ($curve_name: ident; $($tail:tt)*) => {
        #[test]
        fn test_g1_affine_curve() {
            test_var_base_msm::<G1Affine>();
            ark_algebra_test_templates::msm::test_chunked_pippenger::<G1Affine>();
            ark_algebra_test_templates::msm::test_hashmap_pippenger::<G1Affine>();
        }

        #[test]
        fn test_g1_projective_group() {
            let mut rng = ark_std::test_rng();
            let a: G1Projective = rng.gen();
            let b: G1Projective = rng.gen();
            group_test(a, b);
        }

        #[test]
        fn test_g1_generator() {
            let generator = G1Affine::prime_subgroup_generator();
            assert!(generator.is_on_curve());
            assert!(generator.is_in_correct_subgroup_assuming_on_curve());
        }

        generate_g1_test!($($tail)*);
    };
}

#[macro_export]
macro_rules! generate_g2_test {
    () => {};

    (curve_tests; $($tail:tt)*) => {
        #[test]
        fn test_g2_projective_curve() {
            curve_tests::<G2Projective>();
        }
        generate_g2_test!($($tail)*);
    };

    (sw_tests; $($tail:tt)*) => {
        #[test]
        fn test_g2_projective_sw() {
            sw_tests::<g2::Parameters>();
        }
        generate_g2_test!($($tail)*);
    };


    (edwards_tests; $($tail:tt)*) => {
        #[test]
        fn test_g2_projective_edwards() {
            edwards_tests::<g2::Parameters>();
        }
        generate_g2_test!($($tail)*);
    };

    ($curve_name: ident; $($tail:tt)*) => {
        #[test]
        fn test_g2_projective_group() {
            let mut rng = test_rng();
            let a: G2Projective = rng.gen();
            let b: G2Projective = rng.gen();
            group_test(a, b);
        }

        #[test]
        fn test_g2_generator() {
            let generator = G2Affine::prime_subgroup_generator();
            assert!(generator.is_on_curve());
            assert!(generator.is_in_correct_subgroup_assuming_on_curve());
        }

        generate_g2_test!($($tail)*);
    };
}

#[macro_export]
macro_rules! generate_bilinearity_test {
    () => {};

    ($curve_name: ident, $filed_name: ident) => {
        #[test]
        fn test_bilinearity() {
            let mut rng = test_rng();
            let a: G1Projective = rng.gen();
            let b: G2Projective = rng.gen();
            let s: Fr = rng.gen();

            let mut sa = a;
            sa.mul_assign(s);
            let mut sb = b;
            sb.mul_assign(s);

            let ans1 = $curve_name::pairing(sa, b);
            let ans2 = $curve_name::pairing(a, sb);
            let ans3 = $curve_name::pairing(a, b).pow(s.into_bigint());

            assert_eq!(ans1, ans2);
            assert_eq!(ans2, ans3);

            assert_ne!(ans1, $filed_name::one());
            assert_ne!(ans2, $filed_name::one());
            assert_ne!(ans3, $filed_name::one());

            assert_eq!(ans1.pow(Fr::characteristic()), $filed_name::one());
            assert_eq!(ans2.pow(Fr::characteristic()), $filed_name::one());
            assert_eq!(ans3.pow(Fr::characteristic()), $filed_name::one());
        }
    };
}

#[macro_export]
macro_rules! generate_product_of_pairings_test {
    () => {};

    ($curve_name: ident) => {
        #[test]
        fn test_product_of_pairings() {
            let rng = &mut test_rng();

            let a = G1Projective::rand(rng).into_affine();
            let b = G2Projective::rand(rng).into_affine();
            let c = G1Projective::rand(rng).into_affine();
            let d = G2Projective::rand(rng).into_affine();
            let ans1 = $curve_name::pairing(a, b) * &$curve_name::pairing(c, d);
            let ans2 =
                $curve_name::product_of_pairings(&[(a.into(), b.into()), (c.into(), d.into())]);
            assert_eq!(ans1, ans2);
        }
    };
}

#[macro_export]
macro_rules! generate_g1_generator_raw_test {
    () => {};

    ($curve_name: ident, $const: expr) => {
        #[test]
        fn test_g1_generator_raw() {
            let mut x = Fq::zero();
            let mut i = 0;
            loop {
                // y^2 = x^3 + b
                let mut rhs = x;
                rhs.square_in_place();
                rhs.mul_assign(&x);
                rhs.add_assign(&g1::Parameters::COEFF_B);

                if let Some(y) = rhs.sqrt() {
                    let p = G1Affine::new(x, if y < -y { y } else { -y }, false);
                    assert!(!p.is_in_correct_subgroup_assuming_on_curve());

                    let g1 = p.mul_by_cofactor_to_projective();
                    if !g1.is_zero() {
                        assert_eq!(i, $const);
                        let g1 = G1Affine::from(g1);

                        assert!(g1.is_in_correct_subgroup_assuming_on_curve());

                        assert_eq!(g1, G1Affine::prime_subgroup_generator());
                        break;
                    }
                }

                i += 1;
                x.add_assign(&Fq::one());
            }
        }
    };
}

#[macro_export]
macro_rules! generate_field_test {
    () => {
        pub(crate) const ITERATIONS: usize = 5;
    };

    (fq2; $($tail:tt)*) => {
        #[test]
        fn test_fq2() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a: Fq2 = UniformRand::rand(&mut rng);
                let b: Fq2 = UniformRand::rand(&mut rng);
                field_test(a, b);
                sqrt_field_test(a);
            }
            frobenius_test::<Fq2, _>(Fq::characteristic(), 13);
        }

        generate_field_test!($($tail)*);
    };

    (fq3; $($tail:tt)*) => {
        #[test]
        fn test_fq3() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a: Fq3 = UniformRand::rand(&mut rng);
                let b: Fq3 = UniformRand::rand(&mut rng);
                field_test(a, b);
                sqrt_field_test(a);
            }
            frobenius_test::<Fq3, _>(Fq::characteristic(), 13);
        }

        generate_field_test!($($tail)*);
    };

    (fq4; $($tail:tt)*) => {
        #[test]
        fn test_fq4() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let g: Fq4 = UniformRand::rand(&mut rng);
                let h: Fq4 = UniformRand::rand(&mut rng);
                field_test(g, h);
            }
            frobenius_test::<Fq4, _>(Fq::characteristic(), 13);
        }

        generate_field_test!($($tail)*);
    };

    (fq6; $($tail:tt)*) => {
        #[test]
        fn test_fq6() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let g: Fq6 = UniformRand::rand(&mut rng);
                let h: Fq6 = UniformRand::rand(&mut rng);
                field_test(g, h);
            }
            frobenius_test::<Fq6, _>(Fq::characteristic(), 13);
        }

        generate_field_test!($($tail)*);
    };

    (fq12; $($tail:tt)*) => {
        #[test]
        fn test_fq12() {
            let mut rng = test_rng();
            for _ in 0..ITERATIONS {
                let g: Fq12 = rng.gen();
                let h: Fq12 = rng.gen();
                field_test(g, h);
            }
            frobenius_test::<Fq12, _>(Fq::characteristic(), 13);
        }

        generate_field_test!($($tail)*);
    };

    ($curve_name: ident; $($tail:tt)*) => {
        #[test]
        fn test_fr() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a: Fr = UniformRand::rand(&mut rng);
                let b: Fr = UniformRand::rand(&mut rng);
                field_test(a, b);
                primefield_test::<Fr>();
                sqrt_field_test(b);
            }
        }

        #[test]
        fn test_fq() {
            let mut rng = ark_std::test_rng();
            for _ in 0..ITERATIONS {
                let a: Fq = UniformRand::rand(&mut rng);
                let b: Fq = UniformRand::rand(&mut rng);
                field_test(a, b);
                primefield_test::<Fq>();
                sqrt_field_test(a);
            }
        }

        #[test]
        fn test_fq_add_assign() {
            // Test associativity

            let mut rng = test_rng();

            for _ in 0..1000 {
                // Generate a, b, c and ensure (a + b) + c == a + (b + c).
                let a = Fq::rand(&mut rng);
                let b = Fq::rand(&mut rng);
                let c = Fq::rand(&mut rng);

                let mut tmp1 = a;
                tmp1.add_assign(&b);
                tmp1.add_assign(&c);

                let mut tmp2 = b;
                tmp2.add_assign(&c);
                tmp2.add_assign(&a);

                assert_eq!(tmp1, tmp2);
            }
        }

        #[test]
        fn test_fq_sub_assign() {
            let mut rng = test_rng();

            for _ in 0..1000 {
                // Ensure that (a - b) + (b - a) = 0.
                let a = Fq::rand(&mut rng);
                let b = Fq::rand(&mut rng);

                let mut tmp1 = a;
                tmp1.sub_assign(&b);

                let mut tmp2 = b;
                tmp2.sub_assign(&a);

                tmp1.add_assign(&tmp2);
                assert!(tmp1.is_zero());
            }
        }

        #[test]
        fn test_fq_mul_assign() {
            let mut rng = test_rng();

            for _ in 0..1000000 {
                // Ensure that (a * b) * c = a * (b * c)
                let a = Fq::rand(&mut rng);
                let b = Fq::rand(&mut rng);
                let c = Fq::rand(&mut rng);

                let mut tmp1 = a;
                tmp1.mul_assign(&b);
                tmp1.mul_assign(&c);

                let mut tmp2 = b;
                tmp2.mul_assign(&c);
                tmp2.mul_assign(&a);

                assert_eq!(tmp1, tmp2);
            }

            for _ in 0..1000000 {
                // Ensure that r * (a + b + c) = r*a + r*b + r*c

                let r = Fq::rand(&mut rng);
                let mut a = Fq::rand(&mut rng);
                let mut b = Fq::rand(&mut rng);
                let mut c = Fq::rand(&mut rng);

                let mut tmp1 = a;
                tmp1.add_assign(&b);
                tmp1.add_assign(&c);
                tmp1.mul_assign(&r);

                a.mul_assign(&r);
                b.mul_assign(&r);
                c.mul_assign(&r);

                a.add_assign(&b);
                a.add_assign(&c);

                assert_eq!(tmp1, a);
            }
        }

        #[test]
        fn test_fq_squaring() {
            let mut rng = test_rng();

            for _ in 0..1000000 {
                // Ensure that (a * a) = a^2
                let a = Fq::rand(&mut rng);

                let mut tmp = a;
                tmp.square_in_place();

                let mut tmp2 = a;
                tmp2.mul_assign(&a);

                assert_eq!(tmp, tmp2);
            }
        }

        #[test]
        fn test_fq_inverse() {
            assert!(Fq::zero().inverse().is_none());

            let mut rng = test_rng();

            let one = Fq::one();

            for _ in 0..1000 {
                // Ensure that a * a^-1 = 1
                let mut a = Fq::rand(&mut rng);
                let ainv = a.inverse().unwrap();
                a.mul_assign(&ainv);
                assert_eq!(a, one);
            }
        }

        #[test]
        fn test_fq_double_in_place() {
            let mut rng = test_rng();

            for _ in 0..1000 {
                // Ensure doubling a is equivalent to adding a to itself.
                let mut a = Fq::rand(&mut rng);
                let mut b = a;
                b.add_assign(&a);
                a.double_in_place();
                assert_eq!(a, b);
            }
        }

        #[test]
        fn test_fq_negate() {
            {
                let a = -Fq::zero();

                assert!(a.is_zero());
            }

            let mut rng = test_rng();

            for _ in 0..1000 {
                // Ensure (a - (-a)) = 0.
                let mut a = Fq::rand(&mut rng);
                let b = -a;
                a.add_assign(&b);

                assert!(a.is_zero());
            }
        }

        #[test]
        fn test_fq_pow() {
            let mut rng = test_rng();

            for i in 0..1000 {
                // Exponentiate by various small numbers and ensure it consists with repeated
                // multiplication.
                let a = Fq::rand(&mut rng);
                let target = a.pow(&[i]);
                let mut c = Fq::one();
                for _ in 0..i {
                    c.mul_assign(&a);
                }
                assert_eq!(c, target);
            }

            for _ in 0..1000 {
                // Exponentiating by the modulus should have no effect in a prime field.
                let a = Fq::rand(&mut rng);

                assert_eq!(a, a.pow(Fq::characteristic()));
            }
        }

        #[test]
        fn test_fq_sqrt() {
            let mut rng = test_rng();

            assert_eq!(Fq::zero().sqrt().unwrap(), Fq::zero());

            for _ in 0..1000 {
                // Ensure sqrt(a^2) = a or -a
                let a = Fq::rand(&mut rng);
                let nega = -a;
                let mut b = a;
                b.square_in_place();

                let b = b.sqrt().unwrap();

                assert!(a == b || nega == b);
            }

            for _ in 0..1000 {
                // Ensure sqrt(a)^2 = a for random a
                let a = Fq::rand(&mut rng);

                if let Some(mut tmp) = a.sqrt() {
                    tmp.square_in_place();

                    assert_eq!(a, tmp);
                }
            }
        }

        generate_field_test!($($tail)*);
    };
    (mont($fq_num_limbs:expr, $fr_num_limbs:expr); $($tail:tt)*) => {
        #[test]
        fn test_fq_mont() {
            montgomery_primefield_test::<FqConfig, $fq_num_limbs>();
        }

        #[test]
        fn test_fr_mont() {
            montgomery_primefield_test::<FrConfig, $fr_num_limbs>();
        }

        generate_field_test!($($tail)*);
    }
}

#[macro_export]
macro_rules! generate_field_serialization_test {
    () => {};

    (fq2; $($tail:tt)*) => {
        #[test]
        fn test_fq2_serialization() {
            let byte_size = Fq2::zero().serialized_size();
            field_serialization_test::<Fq2>(byte_size);
        }

        generate_field_serialization_test!($($tail)*);
    };

    (fq6; $($tail:tt)*) => {
        #[test]
        fn test_fq6_serialization() {
            let byte_size = Fq6::zero().serialized_size();
            field_serialization_test::<Fq6>(byte_size);
        }

        generate_field_serialization_test!($($tail)*);
    };

    (fq12; $($tail:tt)*) => {
        #[test]
        fn test_fq12_serialization() {
            let byte_size = Fq12::zero().serialized_size();
            field_serialization_test::<Fq12>(byte_size);
        }

        generate_field_serialization_test!($($tail)*);
    };

    ($curve_name: ident; $($tail:tt)*) => {
        #[test]
        fn test_field_serialization() {
            let mut rng = test_rng();
            for _ in 0..ITERATIONS {
                let a: Fr = rng.gen();
                let b: Fq = rng.gen();

                let byte_size = a.serialized_size();
                let (_, buffer_size) = buffer_bit_byte_size(Fr::MODULUS_BIT_SIZE as usize);
                assert_eq!(byte_size, buffer_size);
                field_serialization_test::<Fr>(byte_size);

                let byte_size = b.serialized_size();
                let (_, buffer_size) = buffer_bit_byte_size(Fq::MODULUS_BIT_SIZE as usize);
                assert_eq!(byte_size, buffer_size);
                field_serialization_test::<Fq>(byte_size);
            }
        }

        generate_field_serialization_test!($($tail)*);
    };
}

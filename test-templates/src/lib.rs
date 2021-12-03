pub mod curves;
pub mod fields;
pub mod groups;
pub mod msm;

#[macro_export]
macro_rules! generate_g1_test {
    ($curve_name: ident) => {
        #[test]
        fn test_g1_affine_curve() {
            test_var_base_msm::<G1Affine>();
        }

        #[test]
        fn test_g1_projective_curve() {
            curve_tests::<G1Projective>();
            sw_tests::<g1::Parameters>();
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
    };
}

#[macro_export]
macro_rules! generate_base_field_test {
    ($curve_name: ident) => {
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
    };
}

#[macro_export]
macro_rules! generate_base_fq2_test {
    ($curve_name: ident) => {
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
    };
}

#[macro_export]
macro_rules! generate_base_fq6_test {
    ($curve_name: ident) => {
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
    };
}

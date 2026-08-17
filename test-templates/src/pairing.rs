#[macro_export]
macro_rules! test_pairing {
    ($mod_name: ident; $Pairing: ty) => {
        mod $mod_name {
            pub const ITERATIONS: usize = 100;
            use ark_ec::{pairing::*, CurveGroup, PrimeGroup};
            use ark_ff::{CyclotomicMultSubgroup, Field, PrimeField};
            use ark_std::{test_rng, One, UniformRand, Zero};
            #[test]
            fn test_bilinearity() {
                for _ in 0..100 {
                    let mut rng = test_rng();
                    let a: <$Pairing as Pairing>::G1 = UniformRand::rand(&mut rng);
                    let b: <$Pairing as Pairing>::G2 = UniformRand::rand(&mut rng);
                    let s: <$Pairing as Pairing>::ScalarField = UniformRand::rand(&mut rng);

                    let sa = a * s;
                    let sb = b * s;

                    let ans1 = <$Pairing>::pairing(sa, b);
                    let ans2 = <$Pairing>::pairing(a, sb);
                    let ans3 = <$Pairing>::pairing(a, b) * s;

                    assert_eq!(ans1, ans2);
                    assert_eq!(ans2, ans3);

                    assert_ne!(ans1, PairingOutput::zero());
                    assert_ne!(ans2, PairingOutput::zero());
                    assert_ne!(ans3, PairingOutput::zero());
                    let group_order = <<$Pairing as Pairing>::ScalarField>::characteristic();

                    assert_eq!(ans1.mul_bigint(group_order), PairingOutput::zero());
                    assert_eq!(ans2.mul_bigint(group_order), PairingOutput::zero());
                    assert_eq!(ans3.mul_bigint(group_order), PairingOutput::zero());
                }
            }

            #[test]
            fn test_multi_pairing() {
                for _ in 0..ITERATIONS {
                    let rng = &mut test_rng();

                    let a = <$Pairing as Pairing>::G1::rand(rng).into_affine();
                    let b = <$Pairing as Pairing>::G2::rand(rng).into_affine();
                    let c = <$Pairing as Pairing>::G1::rand(rng).into_affine();
                    let d = <$Pairing as Pairing>::G2::rand(rng).into_affine();
                    let ans1 = <$Pairing>::pairing(a, b) + &<$Pairing>::pairing(c, d);
                    let ans2 = <$Pairing>::multi_pairing(&[a, c], &[b, d]);
                    assert_eq!(ans1, ans2);
                }
            }

            #[test]
            fn test_final_exp() {
                for _ in 0..ITERATIONS {
                    let rng = &mut test_rng();
                    let fp_ext = <$Pairing as Pairing>::TargetField::rand(rng);
                    let gt = <$Pairing as Pairing>::final_exponentiation(MillerLoopOutput(fp_ext))
                        .unwrap()
                        .0;
                    let r = <$Pairing as Pairing>::ScalarField::MODULUS;
                    assert!(gt.cyclotomic_exp(r).is_one());
                }
            }
        }
    };
}

/// Checks the line-coefficient vectors that a `G2Prepared` constructor fills.
///
/// Every model reserves those vectors up front from its loop-count constant, so the
/// reservation has to match the loop exactly and cannot depend on the point. Each model
/// names the vectors differently, so they are listed by the caller: `ell_coeffs` for
/// `bls12` and `bn`, `ell_coeffs_1` and `ell_coeffs_2` for `bw6`, and
/// `double_coefficients` and `addition_coefficients` for `mnt4` and `mnt6`.
///
/// Pass a trailing `; infinity` for the models whose constructor short-circuits the point
/// at infinity before the loop, namely `bls12`, `bn` and `bw6`. `mnt4` and `mnt6` have no
/// such path.
#[macro_export]
macro_rules! test_g2_prepared {
    ($mod_name: ident; $Pairing: ty; $($coeffs: ident),+ $(,)?) => {
        mod $mod_name {
            $crate::__test_g2_prepared!($Pairing; $($coeffs),+);
        }
    };

    ($mod_name: ident; $Pairing: ty; $($coeffs: ident),+; infinity) => {
        mod $mod_name {
            $crate::__test_g2_prepared!($Pairing; $($coeffs),+);

            /// The point at infinity returns before the loop with nothing to store, so it
            /// must not reserve either. Reserving there would allocate the whole
            /// coefficient buffer -- 19 KiB on BLS12-381 -- for a prepared point that
            /// holds no coefficients at all, which is the one case where reserving up
            /// front is strictly worse than growing on demand.
            #[test]
            fn test_infinity_reserves_nothing() {
                use ark_std::Zero;

                let prepared = G2Prepared::from(G2::zero().into_affine());
                $(
                    assert_eq!(
                        prepared.$coeffs.capacity(),
                        0,
                        concat!(
                            "`",
                            stringify!($coeffs),
                            "` allocated for the point at infinity, which stores no \
                             coefficients",
                        ),
                    );
                )+
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __test_g2_prepared {
    ($Pairing: ty; $($coeffs: ident),+) => {
        use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
        use ark_std::{test_rng, UniformRand};
        const ITERATIONS: usize = 10;

        type G2 = <$Pairing as Pairing>::G2;
        type G2Affine = <$Pairing as Pairing>::G2Affine;
        type G2Prepared = <$Pairing as Pairing>::G2Prepared;

        /// Each vector is reserved to its exact final length, so it neither reallocates
        /// while being filled nor leaves unused slots behind. `len == capacity` catches
        /// both directions: an under-reservation grows the vector past what was reserved,
        /// and an over-reservation never fills it.
        ///
        /// The constructors also carry `debug_assert_eq!`s on the length, but those are
        /// compiled out of release builds and say nothing about the capacity.
        #[test]
        fn test_coeffs_reserve_exact_capacity() {
            let rng = &mut test_rng();
            for _ in 0..ITERATIONS {
                let q = G2::rand(rng);
                // The projective constructor delegates to the affine one; check both so
                // the delegation cannot start over-allocating unnoticed.
                for prepared in &[G2Prepared::from(q), G2Prepared::from(q.into_affine())] {
                    $({
                        let coeffs = &prepared.$coeffs;
                        assert!(
                            !coeffs.is_empty(),
                            concat!(
                                "`",
                                stringify!($coeffs),
                                "` is empty, which would make the capacity check vacuous",
                            ),
                        );
                        assert_eq!(
                            coeffs.len(),
                            coeffs.capacity(),
                            concat!(
                                "`",
                                stringify!($coeffs),
                                "` was not reserved exactly: the capacity expression has \
                                 drifted from the loop that fills it",
                            ),
                        );
                    })+
                }
            }
        }

        /// The counts come from the curve's loop-count constant, so they are the same for
        /// every point. That is what makes reserving before the loop possible at all, and
        /// it is the assumption every capacity expression is written against.
        #[test]
        fn test_coeff_counts_are_point_independent() {
            let rng = &mut test_rng();
            let generator = G2Prepared::from(G2Affine::generator());

            let default = G2Prepared::default();
            $(
                assert_eq!(
                    default.$coeffs.len(),
                    generator.$coeffs.len(),
                    concat!("`", stringify!($coeffs), "` differs for `G2Prepared::default`"),
                );
            )+

            for _ in 0..ITERATIONS {
                let random = G2Prepared::from(G2::rand(rng).into_affine());
                $(
                    assert_eq!(
                        random.$coeffs.len(),
                        generator.$coeffs.len(),
                        concat!("`", stringify!($coeffs), "` length depends on the point"),
                    );
                )+
            }
        }
    };
}

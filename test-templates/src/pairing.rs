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

            #[test]
            fn test_mul_bits_be() {
                use ark_ff::BigInteger;
                let rng = &mut test_rng();
                let a = <$Pairing>::pairing(
                    <$Pairing as Pairing>::G1::rand(rng),
                    <$Pairing as Pairing>::G2::rand(rng),
                );

                // `mul_bits_be` consumes a *big-endian* bit representation, so e.g.
                // `[true, false]` is 2, not 1.
                let small_cases: [(&[bool], u64); 7] = [
                    (&[], 0),
                    (&[false, false], 0),
                    (&[true], 1),
                    (&[true, false], 2),
                    (&[true, true, false], 6),
                    (&[true, false, true, false], 10),
                    (&[false, true, false, true], 5),
                ];
                for (bits, scalar) in small_cases {
                    assert_eq!(
                        a.mul_bits_be(bits.iter().copied()),
                        a.mul_bigint([scalar]),
                        "mul_bits_be is inconsistent with mul_bigint for {scalar}"
                    );
                }

                // `2^64 + 1`, which pins down the ordering of the limbs, and not just
                // the ordering of the bits inside each limb.
                let mut bits = [false; 65];
                bits[0] = true;
                bits[64] = true;
                assert_eq!(
                    a.mul_bits_be(bits.iter().copied()),
                    a.mul_bigint([1u64, 1u64]),
                    "mul_bits_be is inconsistent with mul_bigint for 2^64 + 1"
                );

                // Full-width scalars, including their leading zero bits.
                for _ in 0..ITERATIONS {
                    let s = <$Pairing as Pairing>::ScalarField::rand(rng);
                    let bits = s.into_bigint().to_bits_be();
                    assert_eq!(a.mul_bits_be(bits.into_iter()), a * s);
                }
            }
        }
    };
}

use ark_ec::{
    scalar_mul::glv::{
        binary_scalar_mul_jsf, binary_scalar_mul_jsf_affine, joint_sparse_form, GLVConfig,
    },
    AffineRepr, CurveGroup,
};
use ark_ff::{AdditiveGroup, Field, PrimeField, UniformRand};
use ark_pallas::{Fr, PallasConfig, Projective as G};
use ark_std::test_rng;

#[test]
fn jsf_reconstructs_the_scalars() {
    let rng = &mut test_rng();
    for _ in 0..2000 {
        let k1 = Fr::rand(rng);
        let k2 = Fr::rand(rng);
        let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());

        // digits are most-significant first: acc = 2*acc + digit.
        let mut a1 = Fr::ZERO;
        let mut a2 = Fr::ZERO;
        for (u1, u2) in digits {
            a1.double_in_place();
            a2.double_in_place();
            match u1 {
                1 => a1 += Fr::ONE,
                -1 => a1 -= Fr::ONE,
                _ => {},
            }
            match u2 {
                1 => a2 += Fr::ONE,
                -1 => a2 -= Fr::ONE,
                _ => {},
            }
        }
        assert_eq!(a1, k1);
        assert_eq!(a2, k2);
    }
}

#[test]
fn jsf_recodes_full_width_limbs() {
    // Raw 128-bit inputs (independent of any field), including all-ones values
    // whose `-1` digit carries into the spare headroom limb. Reconstruct with
    // wrapping u128 arithmetic, which matches the true value since it is < 2^128.
    let cases: [(u128, u128); 7] = [
        (0, 0),
        (1, 0),
        (u128::MAX, 0),
        (u128::MAX, u128::MAX),
        (u128::MAX, 1),
        (0x8000_0000_0000_0000_0000_0000_0000_0000, u128::MAX),
        (
            0xDEAD_BEEF_DEAD_BEEF_FFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_0000_0000_FFFF_FFFF_FFFF_FFFF,
        ),
    ];
    let to_limbs = |x: u128| [x as u64, (x >> 64) as u64];
    for (k1, k2) in cases {
        let digits = joint_sparse_form(&to_limbs(k1), &to_limbs(k2));
        let (mut a1, mut a2) = (0u128, 0u128);
        for (u1, u2) in digits {
            a1 = a1.wrapping_mul(2).wrapping_add(u1 as i128 as u128);
            a2 = a2.wrapping_mul(2).wrapping_add(u2 as i128 as u128);
        }
        assert_eq!(
            (a1, a2),
            (k1, k2),
            "JSF reconstruction failed for ({k1:#x}, {k2:#x})"
        );
    }
}

#[test]
fn jsf_mul_handles_edge_scalars() {
    let rng = &mut test_rng();
    let b1 = G::rand(rng);
    let b2 = G::rand(rng);
    let specials = [Fr::ZERO, Fr::ONE, -Fr::ONE, PallasConfig::LAMBDA];
    for &k1 in &specials {
        for &k2 in &specials {
            let naive = b1 * k1 + b2 * k2;
            assert_eq!(binary_scalar_mul_jsf(b1, k1, b2, k2), naive);
            assert_eq!(
                binary_scalar_mul_jsf_affine(b1.into_affine(), k1, b2.into_affine(), k2),
                naive
            );
        }
    }
}

#[test]
fn glv_mul_identity_point() {
    // The identity point makes the whole normalized table the identity, which
    // exercises `normalize_batch` and the mixed adds on infinity inputs.
    let id = G::ZERO;
    for k in [Fr::ONE, -Fr::ONE, PallasConfig::LAMBDA, Fr::from(12345u64)] {
        assert_eq!(PallasConfig::glv_mul_projective(id, k), G::ZERO);
        assert!(PallasConfig::glv_mul_affine(id.into_affine(), k).is_zero());
    }
}

#[test]
fn glv_mul_handles_edge_scalars() {
    let rng = &mut test_rng();
    let p = G::rand(rng);
    let cases = [
        Fr::ZERO,
        Fr::ONE,
        -Fr::ONE,
        PallasConfig::LAMBDA,
        -PallasConfig::LAMBDA,
    ];
    for k in cases {
        assert_eq!(PallasConfig::glv_mul_projective(p, k), p * k);
    }
}

//! Run with:
//! `cargo test --release --manifest-path curves/pallas/Cargo.toml --test glv_bench -- --ignored --nocapture`

use ark_ec::{
    scalar_mul::glv::{
        binary_scalar_mul_jsf, binary_scalar_mul_jsf_affine, fast_scalar_decomposition,
        generic_scalar_decomposition, GLVConfig,
    },
    AffineRepr, CurveGroup,
};
use ark_ff::{UniformRand, Zero};
use ark_pallas::{Affine as GAffine, Fr, PallasConfig, Projective as G};
use ark_std::{test_rng, vec::Vec};
use std::time::Instant;

#[test]
#[ignore = "timing comparison; run explicitly with --release --nocapture"]
fn jsf_affine_vs_projective() {
    let rng = &mut test_rng();
    let n = 1000;
    let b1: Vec<GAffine> = (0..n).map(|_| G::rand(rng).into_affine()).collect();
    let b2: Vec<GAffine> = (0..n).map(|_| G::rand(rng).into_affine()).collect();
    let k1: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
    let k2: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();

    let t = Instant::now();
    let mut acc = G::zero();
    for i in 0..n {
        acc += binary_scalar_mul_jsf(b1[i].into_group(), k1[i], b2[i].into_group(), k2[i]);
    }
    let proj = t.elapsed();
    let g1 = acc;

    let t = Instant::now();
    let mut acc = G::zero();
    for i in 0..n {
        acc += binary_scalar_mul_jsf_affine(b1[i], k1[i], b2[i], k2[i]);
    }
    let affine = t.elapsed();
    assert_eq!(g1, acc);

    println!(
        "jsf (affine bases) over {n}: projective {proj:?}, mixed-add {affine:?}  ({:.2}x)",
        proj.as_secs_f64() / affine.as_secs_f64()
    );
}

#[test]
#[ignore = "timing comparison; run explicitly with --release --nocapture"]
fn fast_decomposition_throughput() {
    let rng = &mut test_rng();
    let n = 10000;
    let scalars: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
    let fd = PallasConfig::FAST_DECOMP.unwrap();
    let lambda = PallasConfig::LAMBDA;
    let signed = |(pos, mag): (bool, Fr)| if pos { mag } else { -mag };

    let t = Instant::now();
    let mut acc = Fr::zero();
    for s in &scalars {
        let (k1, k2) = generic_scalar_decomposition::<PallasConfig>(*s);
        acc += signed(k1) + lambda * signed(k2);
    }
    let generic = t.elapsed();
    let generic_acc = acc;

    let t = Instant::now();
    let mut acc = Fr::zero();
    for s in &scalars {
        let (k1, k2) = fast_scalar_decomposition::<PallasConfig>(*s, &fd);
        acc += signed(k1) + lambda * signed(k2);
    }
    let fast = t.elapsed();
    assert_eq!(generic_acc, acc);

    println!(
        "scalar_decomposition over {n}: generic {generic:?}, fast {fast:?}  ({:.2}x)",
        generic.as_secs_f64() / fast.as_secs_f64()
    );
}

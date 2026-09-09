use ark_bls12_381::{g1, Fq, G1Projective};
use ark_ec::{
    hashing::{
        curve_maps::wb::{WBConfig, WBMap},
        map_to_curve_hasher::MapToCurveBasedHasher,
        HashToCurve,
    },
    short_weierstrass::Affine,
};
use ark_ff::{field_hashers::DefaultFieldHasher, Field};
use ark_std::{test_rng, UniformRand};
use criterion::{criterion_group, criterion_main, Criterion};
use sha2::Sha256;

fn bench_isogeny_map(c: &mut Criterion) {
    let mut rng = test_rng();
    let points: Vec<Affine<<g1::Config as WBConfig>::IsogenousCurve>> =
        (0..64).map(|_| Affine::rand(&mut rng)).collect();
    let mut i = 0;
    c.bench_function("BLS12-381 G1 11-isogeny, generic Horner", |b| {
        b.iter(|| {
            i = (i + 1) % points.len();
            <g1::Config as WBConfig>::ISOGENY_MAP
                .apply(points[i])
                .unwrap()
        })
    });
    c.bench_function("BLS12-381 G1 11-isogeny, specialised", |b| {
        b.iter(|| {
            i = (i + 1) % points.len();
            <g1::Config as WBConfig>::isogeny_map(points[i]).unwrap()
        })
    });
}

/// The isogeny map costs one field inversion (batched over the two
/// denominators) plus the four polynomial evaluations; benchmarking the
/// inversion alone lets the polynomial stage be read off by subtraction.
fn bench_inversion(c: &mut Criterion) {
    let mut rng = test_rng();
    let xs: Vec<Fq> = (0..64).map(|_| Fq::rand(&mut rng)).collect();
    let mut i = 0;
    c.bench_function("BLS12-381 Fq inversion", |b| {
        b.iter(|| {
            i = (i + 1) % xs.len();
            xs[i].inverse().unwrap()
        })
    });
}

fn bench_hash_to_g1(c: &mut Criterion) {
    let hasher = MapToCurveBasedHasher::<
        G1Projective,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<g1::Config>,
    >::new(b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_")
    .unwrap();
    let mut rng = test_rng();
    let msgs: Vec<[u8; 32]> = (0..64)
        .map(|_| {
            let mut m = [0u8; 32];
            for b in m.iter_mut() {
                *b = u8::rand(&mut rng);
            }
            m
        })
        .collect();
    let mut i = 0;
    c.bench_function("BLS12-381 hash_to_G1 (SSWU, SHA-256)", |b| {
        b.iter(|| {
            i = (i + 1) % msgs.len();
            hasher.hash(&msgs[i]).unwrap()
        })
    });
}

criterion_group!(benches, bench_isogeny_map, bench_inversion, bench_hash_to_g1);
criterion_main!(benches);

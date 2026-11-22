use ark_algebra_bench_templates::*;
use ark_bls12_381::{Bls12_381, Config, G1Projective, G2Projective};
use ark_ec::{bls12::Bls12Config, pairing::Pairing};
use ark_ff::{CyclotomicMultSubgroup, UniformRand};

pairing_bench!(Bls12_381);

fn cyclotomic_seed(c: &mut Criterion) {
    const SAMPLES: usize = 64;
    let mut rng = ark_std::test_rng();
    let elems: Vec<_> = (0..SAMPLES)
        .map(|_| {
            let p = G1Projective::rand(&mut rng);
            let q = G2Projective::rand(&mut rng);
            Bls12_381::pairing(p, q).0
        })
        .collect();
    let mut i = 0;
    let mut group = c.benchmark_group("Pairing for Bls12_381");
    group.bench_function("Cyclotomic Exp (Seed X) for Bls12_381", |b| {
        b.iter(|| {
            i = (i + 1) % SAMPLES;
            elems[i].cyclotomic_exp(Config::X)
        })
    });
}

criterion_group!(seed_benches, cyclotomic_seed);
criterion_main!(pairing::benches, seed_benches);

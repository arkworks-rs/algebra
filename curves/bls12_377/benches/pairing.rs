use ark_algebra_bench_templates::*;
use ark_bls12_377::{Bls12_377, Config, G1Projective, G2Projective};
use ark_ec::{bls12::Bls12Config, pairing::Pairing};
use ark_ff::{CyclotomicMultSubgroup, UniformRand};

pairing_bench!(Bls12_377);

fn cyclotomic_seed(c: &mut Criterion) {
    const SAMPLES: usize = 64;
    let mut rng = ark_std::test_rng();
    let elems: Vec<_> = (0..SAMPLES)
        .map(|_| {
            let p = G1Projective::rand(&mut rng);
            let q = G2Projective::rand(&mut rng);
            Bls12_377::pairing(p, q).0
        })
        .collect();
    let mut i = 0;
    let mut group = c.benchmark_group("Pairing for Bls12_377");
    group.bench_function("Cyclotomic Exp (Seed X) for Bls12_377", |b| {
        b.iter(|| {
            i = (i + 1) % SAMPLES;
            elems[i].cyclotomic_exp(Config::X)
        })
    });
}

criterion_group!(seed_benches, cyclotomic_seed);
criterion_main!(pairing::benches, seed_benches);

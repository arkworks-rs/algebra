use ark_algebra_bench_templates::*;
use ark_bn254::{Bn254, Config, G1Projective, G2Projective};
use ark_ec::{bn::BnConfig, pairing::Pairing};
use ark_ff::{CyclotomicMultSubgroup, UniformRand};

pairing_bench!(Bn254);

fn cyclotomic_seed(c: &mut Criterion) {
    const SAMPLES: usize = 64;
    let mut rng = ark_std::test_rng();
    let elems: Vec<_> = (0..SAMPLES)
        .map(|_| {
            let p = G1Projective::rand(&mut rng);
            let q = G2Projective::rand(&mut rng);
            Bn254::pairing(p, q).0
        })
        .collect();
    let mut i = 0;
    let mut group = c.benchmark_group("Pairing for Bn254");
    group.bench_function("Cyclotomic Exp (Seed X) for Bn254", |b| {
        b.iter(|| {
            i = (i + 1) % SAMPLES;
            elems[i].cyclotomic_exp(Config::X)
        })
    });
}

criterion_group!(seed_benches, cyclotomic_seed);
criterion_main!(pairing::benches, seed_benches);

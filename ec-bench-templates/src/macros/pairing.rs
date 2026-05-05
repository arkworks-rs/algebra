#[macro_export]
macro_rules! pairing_bench {
    ($curve:ident) => {
        mod pairing {
            use super::*;
            use ark_std::UniformRand;
            fn pairing(c: &mut $crate::criterion::Criterion) {
                use ark_ec::{pairing::Pairing, CurveGroup};

                type G1 = <$curve as Pairing>::G1;
                type G2 = <$curve as Pairing>::G2;
                type G1Prepared = <$curve as Pairing>::G1Prepared;
                type G2Prepared = <$curve as Pairing>::G2Prepared;

                const SAMPLES: usize = 1000;

                let mut rng = ark_std::test_rng();

                let g1s = (0..SAMPLES).map(|_| G1::rand(&mut rng)).collect::<Vec<_>>();
                let g2s = (0..SAMPLES).map(|_| G2::rand(&mut rng)).collect::<Vec<_>>();
                let g1s = G1::normalize_batch(&g1s);
                let g2s = G2::normalize_batch(&g2s);
                let (prepared_1, prepared_2): (Vec<G1Prepared>, Vec<G2Prepared>) = g1s
                    .iter()
                    .zip(&g2s)
                    .map(|(g1, g2)| {
                        let g1: G1Prepared = g1.into();
                        let g2: G2Prepared = g2.into();
                        (g1, g2)
                    })
                    .unzip();
                let miller_loop_outputs = prepared_1
                    .iter()
                    .cloned()
                    .zip(prepared_2.iter().cloned())
                    .map(|(g1, g2)| <$curve as Pairing>::multi_miller_loop([g1], [g2]))
                    .collect::<Vec<_>>();
                let mut i = 0;
                let mut pairing = c.benchmark_group(format!("Pairing for {}", stringify!($curve)));
                pairing.bench_function(
                    &format!("G1 Preparation for {}", stringify!($curve)),
                    |b| {
                        b.iter(|| {
                            i = (i + 1) % SAMPLES;
                            G1Prepared::from(g1s[i].clone())
                        })
                    },
                );
                pairing.bench_function(
                    &format!("G2 Preparation for {}", stringify!($curve)),
                    |b| {
                        b.iter(|| {
                            i = (i + 1) % SAMPLES;
                            G2Prepared::from(g2s[i])
                        })
                    },
                );
                pairing.bench_function(&format!("Miller Loop for {}", stringify!($curve)), |b| {
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        <$curve as Pairing>::multi_miller_loop(
                            [prepared_1[i].clone()],
                            [prepared_2[i].clone()],
                        )
                    })
                });
                pairing.bench_function(
                    &format!("Final Exponentiation for {}", stringify!($curve)),
                    |b| {
                        b.iter(|| {
                            i = (i + 1) % SAMPLES;
                            <$curve as Pairing>::final_exponentiation(miller_loop_outputs[i])
                        })
                    },
                );

                const NUM_PAIRS: usize = 10;

                for pairs in 1..=NUM_PAIRS {
                    pairing.bench_function(
                        &format!(
                            "Multi Pairing for {} with {} pairs",
                            stringify!($curve),
                            pairs
                        ),
                        |b| {
                            b.iter(|| {
                                i = (i + 1) % (SAMPLES - NUM_PAIRS);
                                <$curve as Pairing>::multi_pairing(
                                    g1s[(i)..(i + pairs)].to_vec(),
                                    g2s[(i)..(i + pairs)].to_vec(),
                                )
                            })
                        },
                    );
                }
            }

            $crate::criterion_group!(benches, pairing);
        }
    };
}

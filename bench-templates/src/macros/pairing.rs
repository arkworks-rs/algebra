#[macro_export]
macro_rules! pairing_bench {
    ($curve:ident, $pairing_field:ident) => {
        fn miller_loop(b: &mut $crate::bencher::Bencher) {
            use ark_ec::pairing::Pairing;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let g1s = (0..SAMPLES).map(|_| G1::rand(&mut rng)).collect::<Vec<_>>();
            let g2s = (0..SAMPLES).map(|_| G2::rand(&mut rng)).collect::<Vec<_>>();
            let g1s = G1::normalize_batch(&g1s);
            let g2s = G2::normalize_batch(&g2s);
            let (prepared_1, prepared_2): (
                Vec<<$curve as Pairing>::G1Prepared>,
                Vec<<$curve as Pairing>::G2Prepared>,
            ) = g1s
                .into_iter()
                .zip(g2s)
                .map(|(g1, g2)| {
                    let g1: <$curve as Pairing>::G1Prepared = g1.into();
                    let g2: <$curve as Pairing>::G2Prepared = g2.into();
                    (g1, g2)
                })
                .unzip();
            let mut count = 0;
            b.iter(|| {
                let tmp = $curve::multi_miller_loop(
                    [prepared_1[count].clone()],
                    [prepared_2[count].clone()],
                );
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn final_exponentiation(b: &mut $crate::bencher::Bencher) {
            use ark_ec::pairing::Pairing;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| {
                    (
                        G1Prepared::from(G1::rand(&mut rng)),
                        G2Prepared::from(G2::rand(&mut rng)),
                    )
                })
                .map(|(p, q)| $curve::multi_miller_loop([p], [q]))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let tmp = <$curve as Pairing>::final_exponentiation(v[count]);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn full_pairing(b: &mut $crate::bencher::Bencher) {
            use ark_ec::pairing::Pairing;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let (v1, v2): (Vec<G1>, Vec<G2>) = (0..SAMPLES)
                .map(|_| (G1::rand(&mut rng), G2::rand(&mut rng)))
                .unzip();

            let mut count = 0;
            b.iter(|| {
                let tmp = <$curve as Pairing>::pairing(v1[count], v2[count]);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        $crate::benchmark_group!(pairing, miller_loop, final_exponentiation, full_pairing,);
    };
}

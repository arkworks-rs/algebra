#[macro_export]
macro_rules! pairing_bench {
    ($curve:ident, $pairing_field:ident) => {
        fn miller_loop(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let g1s = (0..SAMPLES).map(|_| G1::rand(&mut rng)).collect::<Vec<_>>();
            let g2s = (0..SAMPLES).map(|_| G2::rand(&mut rng)).collect::<Vec<_>>();
            let g1s = G1::batch_normalization_into_affine(&g1s);
            let g2s = G2::batch_normalization_into_affine(&g2s);
            let prepared = g1s
                .into_iter()
                .zip(g2s)
                .map(|(g1, g2)| (g1.into(), g2.into()))
                .collect::<Vec<(
                    <$curve as PairingEngine>::G1Prepared,
                    <$curve as PairingEngine>::G2Prepared,
                )>>();
            let mut count = 0;
            b.iter(|| {
                let tmp =
                    $curve::miller_loop(&[(prepared[count].0.clone(), prepared[count].1.clone())]);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn final_exponentiation(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| {
                    (
                        G1Affine::from(G1::rand(&mut rng)).into(),
                        G2Affine::from(G2::rand(&mut rng)).into(),
                    )
                })
                .map(|(p, q)| $curve::miller_loop(&[(p, q)]))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let tmp = $curve::final_exponentiation(&v[count]);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn full_pairing(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<(G1, G2)> = (0..SAMPLES)
                .map(|_| (G1::rand(&mut rng), G2::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let tmp = $curve::pairing(v[count].0, v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        $crate::benchmark_group!(pairing, miller_loop, final_exponentiation, full_pairing,);
    };
}

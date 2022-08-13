#[macro_export]
macro_rules! ec_bench {
    ($projective:ty, $affine:ty) => {
        fn rand(b: &mut $crate::bencher::Bencher) {
            let mut rng = ark_std::test_rng();
            b.iter(|| <$projective>::rand(&mut rng));
        }

        fn mul_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<($projective, Fr)> = (0..SAMPLES)
                .map(|_| (<$projective>::rand(&mut rng), Fr::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                tmp *= v[count].1;
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn add_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<($projective, $projective)> = (0..SAMPLES)
                .map(|_| (<$projective>::rand(&mut rng), <$projective>::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, add_assign, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn sub_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<($projective, $projective)> = (0..SAMPLES)
                .map(|_| (<$projective>::rand(&mut rng), <$projective>::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, sub_assign, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn double(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$projective> = (0..SAMPLES)
                .map(|_| <$projective>::rand(&mut rng))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                n_fold!(tmp, double_in_place);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn add_assign_mixed(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<($projective, $affine)> = (0..SAMPLES)
                .map(|_| {
                    (
                        <$projective>::rand(&mut rng),
                        <$projective>::rand(&mut rng).into(),
                    )
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, add_assign_mixed, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn deser(b: &mut $crate::bencher::Bencher) {
            use ark_ec::ProjectiveCurve;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut num_bytes = 0;
            let tmp = <$projective>::rand(&mut rng).into_affine();
            let v: Vec<_> = (0..SAMPLES)
                .flat_map(|_| {
                    let mut bytes = Vec::with_capacity(1000);
                    tmp.serialize(&mut bytes).unwrap();
                    num_bytes = bytes.len();
                    bytes
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let index = count * num_bytes;
                <$affine>::deserialize(&v[index..(index + num_bytes)]).unwrap()
            });
        }

        fn ser(b: &mut $crate::bencher::Bencher) {
            use ark_ec::ProjectiveCurve;
            use ark_serialize::CanonicalSerialize;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut v: Vec<_> = (0..SAMPLES)
                .map(|_| <$projective>::rand(&mut rng))
                .collect();
            let v = <$projective>::batch_normalization_into_affine(v.as_mut_slice());
            let mut bytes = Vec::with_capacity(1000);

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count];
                count = (count + 1) % SAMPLES;
                bytes.clear();
                tmp.serialize(&mut bytes)
            });
        }

        fn deser_unchecked(b: &mut $crate::bencher::Bencher) {
            use ark_ec::ProjectiveCurve;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut num_bytes = 0;
            let tmp = <$projective>::rand(&mut rng).into_affine();
            let v: Vec<_> = (0..SAMPLES)
                .flat_map(|_| {
                    let mut bytes = Vec::with_capacity(1000);
                    tmp.serialize_unchecked(&mut bytes).unwrap();
                    num_bytes = bytes.len();
                    bytes
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let index = count * num_bytes;
                <$affine>::deserialize_unchecked(&v[index..(index + num_bytes)]).unwrap()
            });
        }

        fn ser_unchecked(b: &mut $crate::bencher::Bencher) {
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut v: Vec<_> = (0..SAMPLES)
                .map(|_| <$projective>::rand(&mut rng))
                .collect();
            let v = <$projective>::batch_normalization_into_affine(v.as_mut_slice());
            let mut bytes = Vec::with_capacity(1000);

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count];
                count = (count + 1) % SAMPLES;
                bytes.clear();
                tmp.serialize_unchecked(&mut bytes)
            });
        }

        fn deser_uncompressed(b: &mut $crate::bencher::Bencher) {
            use ark_ec::ProjectiveCurve;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut num_bytes = 0;
            let tmp = <$projective>::rand(&mut rng).into_affine();
            let v: Vec<_> = (0..SAMPLES)
                .flat_map(|_| {
                    let mut bytes = Vec::with_capacity(1000);
                    tmp.serialize_uncompressed(&mut bytes).unwrap();
                    num_bytes = bytes.len();
                    bytes
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let index = count * num_bytes;
                <$affine>::deserialize_uncompressed(&v[index..(index + num_bytes)]).unwrap()
            });
        }

        fn msm_131072(b: &mut $crate::bencher::Bencher) {
            use ark_ec::msm::VariableBaseMSM;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 131072;

            let mut rng = ark_std::test_rng();

            let g = <$projective>::rand(&mut rng).into_affine();
            let v: Vec<_> = (0..SAMPLES).map(|_| g).collect();
            let scalars: Vec<_> = (0..SAMPLES)
                .map(|_| Fr::rand(&mut rng).into_bigint())
                .collect();
            b.bench_n(1, |b| {
                b.iter(|| <$projective as VariableBaseMSM>::msm_bigint(&v, &scalars));
            })
        }

        $crate::benchmark_group!(
            group_ops,
            rand,
            mul_assign,
            add_assign,
            sub_assign,
            add_assign_mixed,
            double,
            ser,
            deser,
            ser_unchecked,
            deser_unchecked,
            deser_uncompressed,
            msm_131072,
        );
    };
}

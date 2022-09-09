#[macro_export]
macro_rules! ec_bench {
    ($Projective:ty) => {
        fn rand(c: &mut $crate::criterion::Criterion) {
            use ark_std::UniformRand;
            let mut rng = ark_std::test_rng();
            c.bench_function(
                &format!("Sample {} elements", stringify!($Projective)),
                |b| b.iter(|| <$Projective>::rand(&mut rng)),
            );
        }

        fn arithmetic(c: &mut $crate::criterion::Criterion) {
            use ark_ec::{CurveGroup, Group};
            use ark_std::UniformRand;

            type Scalar = <$Projective as Group>::ScalarField;
            const SAMPLES: usize = 1000;
            let mut rng = ark_std::test_rng();
            let mut arithmetic =
                c.benchmark_group(format!("Arithmetic for {}", stringify!($Projective)));
            let group_elements_left = (0..SAMPLES)
                .map(|_| <$Projective>::rand(&mut rng))
                .collect::<Vec<_>>();
            let group_elements_right = (0..SAMPLES)
                .map(|_| <$Projective>::rand(&mut rng))
                .collect::<Vec<_>>();
            let group_elements_right_affine = <$Projective>::normalize_batch(&group_elements_right);
            let scalars = (0..SAMPLES)
                .map(|_| Scalar::rand(&mut rng))
                .collect::<Vec<_>>();
            arithmetic.bench_function(&format!("Addition for {}", stringify!($Projective)), |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    group_elements_left[i] + group_elements_right[i]
                })
            });
            arithmetic.bench_function(
                &format!("Subtraction for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        group_elements_left[i] - group_elements_right[i]
                    })
                },
            );

            arithmetic.bench_function(
                &format!("Mixed Addition for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        group_elements_left[i] + group_elements_right_affine[i]
                    })
                },
            );

            arithmetic.bench_function(
                &format!("Mixed Subtraction for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        group_elements_left[i] - group_elements_right_affine[i]
                    })
                },
            );

            arithmetic.bench_function(&format!("Double for {}", stringify!($Projective)), |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    group_elements_left[i].double()
                })
            });

            arithmetic.bench_function(
                &format!("Scalar Multiplication for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        group_elements_left[i] * scalars[i]
                    })
                },
            );
        }

        fn serialization(c: &mut $crate::criterion::Criterion) {
            use ark_ec::CurveGroup;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            use ark_std::UniformRand;

            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| <$Projective>::rand(&mut rng))
                .collect();
            let v = <$Projective>::normalize_batch(&v);
            let mut bytes = Vec::with_capacity(1000);
            let v_compressed = v
                .iter()
                .map(|a| {
                    let mut bytes = Vec::with_capacity(1000);
                    a.serialize_compressed(&mut bytes).unwrap();
                    bytes
                })
                .collect::<Vec<_>>();
            let v_uncompressed = v
                .iter()
                .map(|a| {
                    let mut bytes = Vec::with_capacity(1000);
                    a.serialize_uncompressed(&mut bytes).unwrap();
                    bytes
                })
                .collect::<Vec<_>>();
            let mut serialization =
                c.benchmark_group(format!("Serialization for {}", stringify!($Projective)));
            serialization.bench_function(
                &format!("Serialize Compressed for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        v[i].serialize_compressed(&mut bytes).unwrap()
                    })
                },
            );
            serialization.bench_function(
                &format!("Serialize Uncompressed for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        v[i].serialize_uncompressed(&mut bytes).unwrap()
                    })
                },
            );
            serialization.bench_function(
                &format!("Deserialize Compressed for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        <$Projective>::deserialize_compressed(v_compressed[i].as_slice()).unwrap()
                    })
                },
            );
            serialization.bench_function(
                &format!(
                    "Deserialize Compressed Unchecked for {}",
                    stringify!($Projective)
                ),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        <$Projective>::deserialize_compressed_unchecked(v_compressed[i].as_slice())
                            .unwrap()
                    })
                },
            );
            serialization.bench_function(
                &format!("Deserialize Uncompressed for {}", stringify!($Projective)),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        <$Projective>::deserialize_uncompressed(v_uncompressed[i].as_slice())
                            .unwrap()
                    })
                },
            );
            serialization.bench_function(
                &format!(
                    "Deserialize Uncompressed Unchecked for {}",
                    stringify!($Projective)
                ),
                |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        bytes.clear();
                        <$Projective>::deserialize_uncompressed_unchecked(
                            v_uncompressed[i].as_slice(),
                        )
                        .unwrap()
                    })
                },
            );
        }

        fn msm_131072(c: &mut $crate::criterion::Criterion) {
            use ark_ec::{scalar_mul::variable_base::VariableBaseMSM, CurveGroup};
            use ark_ff::PrimeField;
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            use ark_std::UniformRand;

            const SAMPLES: usize = 131072;

            let mut rng = ark_std::test_rng();

            let g = <$Projective>::rand(&mut rng).into_affine();
            let v: Vec<_> = (0..SAMPLES).map(|_| g).collect();
            let scalars: Vec<_> = (0..SAMPLES)
                .map(|_| Fr::rand(&mut rng).into_bigint())
                .collect();
            c.bench_function(&format!("MSM for {}", stringify!($Projective)), |b| {
                b.iter(|| {
                    let result: $Projective = VariableBaseMSM::msm_bigint(&v, &scalars);
                    result
                })
            });
        }

        $crate::criterion_group!(benches, rand, arithmetic, serialization, msm_131072,);
    };
}

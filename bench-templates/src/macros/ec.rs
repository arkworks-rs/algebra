#[macro_export]
macro_rules! ec_bench {
    ($curve_name:expr, $Group:ident) => {
        $crate::paste! {
            mod [<$Group:lower>] {
                use ark_ec::Group;
                use super::*;

                type Scalar = <$Group as Group>::ScalarField;
                fn rand(c: &mut $crate::criterion::Criterion) {
                    let name = format!("{}::{}", $curve_name, stringify!($Group));
                    use ark_std::UniformRand;
                    let mut rng = ark_std::test_rng();
                    c.bench_function(
                        &format!("Sample {name} elements"),
                        |b| b.iter(|| <$Group>::rand(&mut rng)),
                    );
                }

                fn arithmetic(c: &mut $crate::criterion::Criterion) {
                    use ark_ec::{CurveGroup, Group};
                    use ark_std::UniformRand;
                    let name = format!("{}::{}", $curve_name, stringify!($Group));

                    type Scalar = <$Group as Group>::ScalarField;
                    const SAMPLES: usize = 1000;
                    let mut rng = ark_std::test_rng();
                    let mut arithmetic =
                        c.benchmark_group(format!("Arithmetic for {name}"));
                    let group_elements_left = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect::<Vec<_>>();
                    let group_elements_right = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect::<Vec<_>>();
                    let group_elements_right_affine = <$Group>::normalize_batch(&group_elements_right);
                    let scalars = (0..SAMPLES)
                        .map(|_| Scalar::rand(&mut rng))
                        .collect::<Vec<_>>();
                    arithmetic.bench_function("Addition", |b| {
                        let mut i = 0;
                        b.iter(|| {
                            i = (i + 1) % SAMPLES;
                            group_elements_left[i] + group_elements_right[i]
                        })
                    });
                    arithmetic.bench_function(
                        "Subtraction",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                group_elements_left[i] - group_elements_right[i]
                            })
                        },
                    );

                    arithmetic.bench_function(
                        "Mixed Addition",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                group_elements_left[i] + group_elements_right_affine[i]
                            })
                        },
                    );

                    arithmetic.bench_function(
                        "Mixed Subtraction",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                group_elements_left[i] - group_elements_right_affine[i]
                            })
                        },
                    );

                    arithmetic.bench_function("Double", |b| {
                        let mut i = 0;
                        b.iter(|| {
                            i = (i + 1) % SAMPLES;
                            group_elements_left[i].double()
                        })
                    });

                    arithmetic.bench_function(
                        "Scalar Multiplication",
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

                    let name = format!("{}::{}", $curve_name, stringify!($Group));
                    let mut rng = ark_std::test_rng();

                    let v: Vec<_> = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect();
                    let v = <$Group>::normalize_batch(&v);
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
                        c.benchmark_group(format!("Serialization for {name}"));
                    serialization.bench_function(
                        "Serialize Compressed",
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
                        "Serialize Uncompressed",
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
                        "Deserialize Compressed",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                bytes.clear();
                                <$Group>::deserialize_compressed(v_compressed[i].as_slice()).unwrap()
                            })
                        },
                    );
                    serialization.bench_function(
                        "Deserialize Compressed Unchecked",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                bytes.clear();
                                <$Group>::deserialize_compressed_unchecked(v_compressed[i].as_slice())
                                    .unwrap()
                            })
                        },
                    );
                    serialization.bench_function(
                        "Deserialize Uncompressed",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                bytes.clear();
                                <$Group>::deserialize_uncompressed(v_uncompressed[i].as_slice())
                                    .unwrap()
                            })
                        },
                    );
                    serialization.bench_function(
                        "Deserialize Uncompressed Unchecked",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                bytes.clear();
                                <$Group>::deserialize_uncompressed_unchecked(
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

                    let name = format!("{}::{}", $curve_name, stringify!($Group));
                    let mut rng = ark_std::test_rng();

                    let v: Vec<_> = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect();
                    let v = <$Group>::normalize_batch(&v);
                    let scalars: Vec<_> = (0..SAMPLES)
                        .map(|_| Scalar::rand(&mut rng).into_bigint())
                        .collect();
                    c.bench_function(&format!("MSM for {name}"), |b| {
                        b.iter(|| {
                            let result: $Group = VariableBaseMSM::msm_bigint(&v, &scalars);
                            result
                        })
                    });
                }

                $crate::criterion_group!(benches, rand, arithmetic, serialization, msm_131072,);
            }
        }
    };
}

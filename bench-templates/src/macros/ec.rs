#[macro_export]
macro_rules! ec_bench {
    ($curve_name:expr, $Group:ident) => {
        $crate::paste! {
            mod [<$Group:lower>] {
                use ark_ec::PrimeGroup;
                use super::*;

                type Scalar = <$Group as PrimeGroup>::ScalarField;
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
                    use ark_ff::AdditiveGroup;
                    use ark_ec::{CurveGroup, PrimeGroup};
                    use ark_std::UniformRand;
                    let name = format!("{}::{}", $curve_name, stringify!($Group));

                    type Scalar = <$Group as PrimeGroup>::ScalarField;
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

                fn msm(c: &mut $crate::criterion::Criterion) {
                    use ark_ec::{scalar_mul::variable_base::VariableBaseMSM, CurveGroup};
                    use ark_ff::PrimeField;
                    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
                    use ark_std::{UniformRand, rand::seq::SliceRandom};
                    let mut c = c.benchmark_group("MSM");
                    c.sample_size(10);

                    const SAMPLES: usize = 1 << 20;

                    let name = format!("{}::{}", $curve_name, stringify!($Group));
                    let mut rng = ark_std::test_rng();

                    let v: Vec<_> = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect();
                    let v = <$Group>::normalize_batch(&v);

                    c.bench_function(&format!("MSM-random for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::rand(&mut rng).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });


                    c.bench_function(&format!("MSM-bool for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(bool::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-bool-direct for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| bool::rand(&mut rng))
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_u1(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u8 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(u8::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u8-direct for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| u8::rand(&mut rng))
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_u8(&v, &s))
                    });

                    c.bench_function(&format!("MSM-i8 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(i8::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u16 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(u16::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u16-direct for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| u16::rand(&mut rng))
                            .collect();
                        b.iter(|| <$Group>::msm_u16(&v, &s))
                    });

                    c.bench_function(&format!("MSM-i16 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(i16::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u32 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(u32::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u32-direct for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| u32::rand(&mut rng))
                            .collect();
                        b.iter(|| <$Group>::msm_u32(&v, &s))
                    });

                    c.bench_function(&format!("MSM-i32 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(i32::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u64 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(u64::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-u64-direct for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| u64::rand(&mut rng))
                            .collect();
                        b.iter(|| <$Group>::msm_u64(&v, &s))
                    });
                    c.bench_function(&format!("MSM-i64 for {name}"), |b| {
                        let s: Vec<_> = (0..SAMPLES)
                            .map(|_| Scalar::from(i64::rand(&mut rng)).into_bigint())
                            .collect();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });

                    c.bench_function(&format!("MSM-mixed for {name}"), |b| {
                        const S: usize = SAMPLES / 11;
                        let mut s = Vec::with_capacity(S * 11);
                        // Positive and negative u1s
                        s.extend((0..S).map(|_| Scalar::from(bool::rand(&mut rng))));
                        s.extend((0..S).map(|_| -Scalar::from(bool::rand(&mut rng))));

                        // Positive and negative u8s
                        s.extend((0..S).map(|_| Scalar::from(u8::rand(&mut rng))));
                        s.extend((0..S).map(|_| -Scalar::from(u8::rand(&mut rng))));

                        // Positive and negative u16s
                        s.extend((0..S).map(|_| Scalar::from(u16::rand(&mut rng))));
                        s.extend((0..S).map(|_| -Scalar::from(u16::rand(&mut rng))));

                        // Positive and negative u32s
                        s.extend((0..S).map(|_| Scalar::from(u32::rand(&mut rng))));
                        s.extend((0..S).map(|_| -Scalar::from(u32::rand(&mut rng))));

                        // Positive and negative u64s
                        s.extend((0..S).map(|_| Scalar::from(u64::rand(&mut rng))));
                        s.extend((0..S).map(|_| -Scalar::from(u64::rand(&mut rng))));

                        // Random s
                        s.extend((0..S).map(|_| Scalar::rand(&mut rng)));
                        s.shuffle(&mut rng);
                        let s = s
                            .into_iter()
                            .map(|s| s.into_bigint())
                            .collect::<Vec<_>>();
                        b.iter(|| <$Group as VariableBaseMSM>::msm_bigint(&v, &s))
                    });
                }

                $crate::criterion_group!(benches, rand, arithmetic, serialization, msm);
            }
        }
    };
}

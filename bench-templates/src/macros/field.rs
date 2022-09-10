#[macro_export]
macro_rules! f_bench {
    // Use this for base fields
    (prime, $curve_name:expr, $F:ident) => {
        $crate::paste! {
            mod [<$F:lower>] {
                use super::*;
                use ark_ff::{Field, PrimeField, UniformRand};
                field_common!($curve_name, $F);
                sqrt!($curve_name, $F);
                prime_field!($curve_name, $F);
                $crate::criterion_group!(
                    benches,
                    // common stuff
                    arithmetic,
                    serialization,
                    // sqrt field stuff
                    sqrt,
                    // prime field stuff
                    bigint,
                );
            }
        }
    };
    // use this for intermediate fields
    (extension, $curve_name:expr, $F:ident) => {
        $crate::paste! {
            mod [<$F:lower>] {
                use super::*;
                use ark_ff::{Field, UniformRand};
                field_common!($curve_name, $F);
                sqrt!($curve_name, $F);
                $crate::criterion_group!(
                    benches,
                    // common stuff
                    arithmetic,
                    serialization,
                    // sqrt field stuff
                    sqrt,
                );
            }
        }
    };
    // Use this for the target field.
    (target, $curve_name:expr, $F:ident) => {
        $crate::paste! {
            mod [<$F:lower>] {
                use super::*;
                use ark_ff::{Field, UniformRand};
                field_common!($curve_name, $F);
                $crate::criterion_group!(
                    benches,
                    // common stuff
                    arithmetic,
                    serialization,
                );
            }
        }
    };
}

#[macro_export]
macro_rules! field_common {
    ($curve_name:expr, $F:ident) => {
        fn arithmetic(c: &mut $crate::criterion::Criterion) {
            let name = format!("{}::{}", stringify!($curve), stringify!($F));
            const SAMPLES: usize = 1000;
            let mut rng = ark_std::test_rng();
            let mut arithmetic = c.benchmark_group(format!("Arithmetic for {name}"));
            let field_elements_left = (0..SAMPLES)
                .map(|_| <$F>::rand(&mut rng))
                .collect::<Vec<_>>();
            let field_elements_right = (0..SAMPLES)
                .map(|_| <$F>::rand(&mut rng))
                .collect::<Vec<_>>();
            arithmetic.bench_function("Addition", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i] + field_elements_right[i]
                })
            });
            arithmetic.bench_function("Subtraction", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i] - field_elements_right[i]
                })
            });
            arithmetic.bench_function("Negation", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    -field_elements_left[i]
                })
            });

            arithmetic.bench_function("Double", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i].double()
                })
            });

            arithmetic.bench_function("Multiplication", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i] * field_elements_right[i]
                })
            });
            arithmetic.bench_function("Square", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i].square()
                })
            });
            arithmetic.bench_function("Inverse", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    field_elements_left[i].inverse().unwrap()
                })
            });
            arithmetic.bench_function("Sum of products of size 2", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let j = (i + 1) % SAMPLES;
                    <$F>::sum_of_products(
                        &[field_elements_left[i], field_elements_right[j]],
                        &[field_elements_left[j], field_elements_right[i]],
                    )
                })
            });
            arithmetic.bench_function("Naive sum of products of size 2", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let j = (i + 1) % SAMPLES;
                    field_elements_left[i] * field_elements_left[j]
                        + field_elements_right[j] * field_elements_right[i]
                })
            });
        }

        fn serialization(c: &mut $crate::criterion::Criterion) {
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            let name = format!("{}::{}", stringify!($curve), stringify!($F));
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let f = (0..SAMPLES)
                .map(|_| <$F>::rand(&mut rng))
                .collect::<Vec<_>>();
            let mut bytes = Vec::with_capacity(1000);

            let f_compressed = f
                .iter()
                .map(|a| {
                    let mut bytes = Vec::with_capacity(1000);
                    a.serialize_compressed(&mut bytes).unwrap();
                    bytes
                })
                .collect::<Vec<_>>();

            let f_uncompressed = f
                .iter()
                .map(|a| {
                    let mut bytes = Vec::with_capacity(1000);
                    a.serialize_uncompressed(&mut bytes).unwrap();
                    bytes
                })
                .collect::<Vec<_>>();

            let mut serialization = c.benchmark_group(format!("Serialization for {name}"));

            serialization.bench_function("Serialize Compressed", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    f[i].serialize_compressed(&mut bytes).unwrap()
                })
            });
            serialization.bench_function("Serialize Uncompressed", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    f[i].serialize_uncompressed(&mut bytes).unwrap()
                })
            });
            serialization.bench_function("Deserialize Compressed", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    <$F>::deserialize_compressed(f_compressed[i].as_slice()).unwrap()
                })
            });
            serialization.bench_function("Deserialize Compressed Unchecked", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    <$F>::deserialize_compressed_unchecked(f_compressed[i].as_slice()).unwrap()
                })
            });
            serialization.bench_function("Deserialize Uncompressed", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    <$F>::deserialize_uncompressed(f_uncompressed[i].as_slice()).unwrap()
                })
            });
            serialization.bench_function("Deserialize Uncompressed Unchecked", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    bytes.clear();
                    <$F>::deserialize_uncompressed_unchecked(f_uncompressed[i].as_slice()).unwrap()
                })
            });
            serialization.finish()
        }
    };
}

#[macro_export]
macro_rules! sqrt {
    ($curve_name:expr, $F:ident) => {
        fn sqrt(c: &mut $crate::criterion::Criterion) {
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;
            let name = format!("{}::{}", stringify!($curve), stringify!($F));

            let mut rng = ark_std::test_rng();

            let f = (0..SAMPLES)
                .map(|_| <$F>::rand(&mut rng))
                .collect::<Vec<_>>();
            let qrs = f.iter().map(|s| s.square()).collect::<Vec<_>>();
            let mut sqrt = c.benchmark_group(format!("SquareRoot for {name}"));

            sqrt.bench_function("Square Root for QR", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    qrs[i].sqrt().unwrap()
                })
            });
            sqrt.bench_function("Legendre for QR", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    qrs[i].legendre()
                })
            });
            sqrt.finish();
        }
    };
}

#[macro_export]
macro_rules! prime_field {
    ($curve_name:expr, $F:ident) => {
        fn bigint(c: &mut $crate::criterion::Criterion) {
            use ark_ff::{BigInteger, PrimeField};
            type BigInt = <$F as PrimeField>::BigInt;
            const SAMPLES: usize = 1000;

            let name = format!("{}::{}", stringify!($curve), stringify!($F));
            let mut rng = ark_std::test_rng();

            let (v1, v2): (Vec<_>, Vec<_>) = (0..SAMPLES)
                .map(|_| {
                    let mut tmp1 = BigInt::rand(&mut rng);
                    let mut tmp2 = BigInt::rand(&mut rng);
                    // Shave a few bits off to avoid overflow.
                    for _ in 0..3 {
                        tmp1.div2();
                        tmp2.div2();
                    }
                    tmp2.div2();
                    (tmp1, tmp2)
                })
                .unzip();
            let mut arithmetic = c.benchmark_group(format!("Arithmetic for {name}::BigInt"));
            arithmetic.bench_function("Addition with carry", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let mut tmp = v1[i];
                    (tmp, tmp.add_with_carry(&v2[i]))
                })
            });
            arithmetic.bench_function("Subtraction with borrow", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let mut tmp = v1[i];
                    (tmp, tmp.sub_with_borrow(&v2[i]))
                })
            });
            arithmetic.bench_function("Multiplication by 2", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let mut tmp = v1[i];
                    tmp.mul2()
                })
            });
            arithmetic.bench_function("Division by 2", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    let mut tmp = v1[i];
                    tmp.div2()
                })
            });
            arithmetic.finish();
            let mut bits = c.benchmark_group(format!("Bitwise operations for {name}::BigInt"));
            bits.bench_function("Number of bits", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    v2[i].num_bits()
                })
            });
            let v_bits_le = v2
                .iter()
                .map(|s| ark_ff::BitIteratorLE::new(s).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            bits.bench_function("From Little-Endian bits", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    BigInt::from_bits_be(&v_bits_le[i]);
                })
            });
            let v_bits_be = v1
                .iter()
                .map(|s| ark_ff::BitIteratorBE::new(s).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            bits.bench_function("From Big-Endian bits", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    BigInt::from_bits_be(&v_bits_be[i]);
                })
            });
            bits.bench_function("Comparison", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    v1[i] > v2[i]
                })
            });
            bits.bench_function("Equality", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    v1[i] == v2[i]
                })
            });
            bits.finish();

            let f = (0..SAMPLES)
                .map(|_| <$F>::rand(&mut rng))
                .collect::<Vec<_>>();
            let bigints = f.iter().map(|f| f.into_bigint()).collect::<Vec<_>>();
            let mut conversions = c.benchmark_group(format!("Conversions for {name}"));
            conversions.bench_function("From BigInt", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    <$F>::from_bigint(bigints[i])
                })
            });
            conversions.bench_function("Into BigInt", |b| {
                let mut i = 0;
                b.iter(|| {
                    i = (i + 1) % SAMPLES;
                    f[i].into_bigint()
                })
            });
            conversions.finish()
        }
    };
}

#[macro_export]
macro_rules! glv_bench {
    ($curve_name:expr, $curve:ident) => {
        mod glv {
            use super::*;
            use ark_ec::Group;

            fn glv(c: &mut $crate::criterion::Criterion) {
                use ark_ec::{scalar_mul::glv::GLVConfig, CurveGroup, Group};
                use ark_std::UniformRand;
                let name = format!("{}::{}", $curve_name, stringify!($Group));

                type Scalar = <$curve as Group>::ScalarField;
                const SAMPLES: usize = 1000;
                let mut rng = ark_std::test_rng();
                let mut arithmetic = c.benchmark_group(format!("Arithmetic for {name}"));
                let group_elements = (0..SAMPLES)
                    .map(|_| <$curve>::rand(&mut rng))
                    .collect::<Vec<_>>();
                let scalars = (0..SAMPLES)
                    .map(|_| Scalar::rand(&mut rng))
                    .collect::<Vec<_>>();

                arithmetic.bench_function("GLV Scalar Multiplication", |b| {
                    let mut i = 0;
                    b.iter(|| {
                        i = (i + 1) % SAMPLES;
                        <<$curve as CurveGroup>::Config as GLVConfig>::glv_mul(
                            group_elements[i],
                            scalars[i],
                        )
                    })
                });
            }

            $crate::criterion_group!(benches, glv,);
        }
    };
}

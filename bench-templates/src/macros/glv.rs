#[macro_export]
macro_rules! glv_bench {
    ($curve_name:expr, $Group:ident) => {
        $crate::paste! {
            mod [<$Group:lower>] {
                use ark_ec::Group;
                use super::*;

                type Scalar = <$Group as Group>::ScalarField;
                type Config = <$group as CurveGroup>::Config;

                fn glv(c: &mut $crate::criterion::Criterion) {
                    use ark_ec::{CurveGroup, Group};
                    use ark_std::UniformRand;
                    let name = format!("{}::{}", $curve_name, stringify!($Group));

                    type Scalar = <$Group as Group>::ScalarField;
                    const SAMPLES: usize = 1000;
                    let mut rng = ark_std::test_rng();
                    let mut arithmetic =
                        c.benchmark_group(format!("Arithmetic for {name}"));
                    let group_elements = (0..SAMPLES)
                        .map(|_| <$Group>::rand(&mut rng))
                        .collect::<Vec<_>>();
                    let scalars = (0..SAMPLES)
                        .map(|_| Scalar::rand(&mut rng))
                        .collect::<Vec<_>>();

                    arithmetic.bench_function(
                        "GLV Scalar Multiplication",
                        |b| {
                            let mut i = 0;
                            b.iter(|| {
                                i = (i + 1) % SAMPLES;
                                Config::glv_mul(g, k);
                                group_elements[i], scalars[i]
                            })
                        },
                    );
                }

                $crate::criterion_group!(benches, glv,);
            }
        }
    };
}

#[macro_use]
extern crate criterion;

use ark_test_curves::bn384_small_two_adicity;
use criterion::Criterion;

mod templates;

fn bench_bn384(c: &mut Criterion) {
    templates::field_arithmetic_bench::<bn384_small_two_adicity::Fq>(c, "Bn384", "Fq");
    templates::field_arithmetic_bench::<bn384_small_two_adicity::Fr>(c, "Bn384", "Fr");

    templates::square_root_field_bench::<bn384_small_two_adicity::Fq>(c, "Bn384", "Fq");
    templates::square_root_field_bench::<bn384_small_two_adicity::Fr>(c, "Bn384", "Fr");

    templates::curve_affine_arithmetic_bench::<bn384_small_two_adicity::G1Affine>(
        c, "Bn384", "G1Affine",
    );
    templates::curve_projective_arithmetic_bench::<bn384_small_two_adicity::G1Projective>(
        c,
        "Bn384",
        "G1Projective",
    );
}

criterion_group!(benches, bench_bn384);
criterion_main!(benches);

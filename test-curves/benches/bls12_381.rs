#[macro_use]
extern crate criterion;

use ark_test_curves::bls12_381;
use criterion::Criterion;

mod templates;

fn bench_bls_381(c: &mut Criterion) {
    templates::field_arithmetic_bench::<bls12_381::Fq>(c, "Bls12-381", "Fq");
    templates::field_arithmetic_bench::<bls12_381::Fq2>(c, "Bls12-381", "Fq2");
    templates::field_arithmetic_bench::<bls12_381::Fq6>(c, "Bls12-381", "Fq6");
    templates::field_arithmetic_bench::<bls12_381::Fr>(c, "Bls12-381", "Fr");

    templates::square_root_field_bench::<bls12_381::Fq>(c, "Bls12-381", "Fq");
    templates::square_root_field_bench::<bls12_381::Fq2>(c, "Bls12-381", "Fq2");
    templates::square_root_field_bench::<bls12_381::Fr>(c, "Bls12-381", "Fr");

    templates::curve_affine_arithmetic_bench::<bls12_381::G1Affine>(c, "Bls12-381", "G1Affine");
    templates::curve_projective_arithmetic_bench::<bls12_381::G1Projective>(
        c,
        "Bls12-381",
        "G1Projective",
    );
}

criterion_group!(benches, bench_bls_381);
criterion_main!(benches);

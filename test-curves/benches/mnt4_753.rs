#[macro_use]
extern crate criterion;

use ark_test_curves::mnt4_753;
use criterion::Criterion;

mod templates;

fn bench_mnt4_753(c: &mut Criterion) {
    templates::field_arithmetic_bench::<mnt4_753::Fq>(c, "Mnt4-753", "Fq");
    templates::field_arithmetic_bench::<mnt4_753::Fr>(c, "Mnt4-753", "Fr");

    templates::square_root_field_bench::<mnt4_753::Fq>(c, "Mnt4-753", "Fq");
    templates::square_root_field_bench::<mnt4_753::Fr>(c, "Mnt4-753", "Fr");

    templates::curve_affine_arithmetic_bench::<mnt4_753::G1Affine>(c, "Mnt4-753", "G1Affine");
    templates::curve_projective_arithmetic_bench::<mnt4_753::G1Projective>(
        c,
        "Mnt4-753",
        "G1Projective",
    );
}

criterion_group!(benches, bench_mnt4_753);
criterion_main!(benches);

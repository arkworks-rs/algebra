use ark_algebra_bench_templates::*;
use ark_test_curves::bls12_381::{
    fq::Fq, fq2::Fq2, fr::Fr, Bls12_381, Fq12, G1Projective as G1, G2Projective as G2,
};

mod g1 {
    use super::*;
    ec_bench!(G1);
}
mod g2 {
    use super::*;
    ec_bench!(G2);
}

f_bench!(prime, Fq, fq);
f_bench!(prime, Fr, fr);
f_bench!(extension, Fq2, fq2);
f_bench!(target, Fq12, fq12);
pairing_bench!(Bls12_381);

criterion_main!(
    g1::benches,
    g2::benches,
    fq::benches,
    fr::benches,
    fq2::benches,
    fq12::benches
);

use ark_algebra_bench_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{
    biginteger::{BigInteger256 as FrRepr, BigInteger384 as FqRepr},
    BigInteger, Field, PrimeField, UniformRand,
};
use ark_test_curves::bls12_381::{
    fq::Fq, fq2::Fq2, fr::Fr, Bls12_381, Fq12, G1Affine, G1Projective as G1, G2Affine,
    G2Projective as G2,
};

mod g1 {
    use super::*;
    ec_bench!(G1, G1Affine);
}
mod g2 {
    use super::*;
    ec_bench!(G2, G2Affine);
}

f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);
f_bench!(extension, Fq2, Fq2, fq2);
f_bench!(target, Fq12, Fq12, fq12);

pairing_bench!(Bls12_381, Fq12);

bencher::benchmark_main!(fq, fr, fq2, fq12, g1::group_ops, g2::group_ops, pairing);

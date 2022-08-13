use ark_algebra_bench_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::ProjectiveCurve;
use ark_ff::{biginteger::BigInteger768 as FqRepr, BigInteger, Field, PrimeField, UniformRand};
use ark_test_curves::mnt4_753::{fq::Fq, fr::Fr, G1Affine, G1Projective as G1};

mod g1 {
    use super::*;
    ec_bench!(G1, G1Affine);
}

f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FqRepr, FqRepr, fr);

bencher::benchmark_main!(fq, fr, g1::group_ops);

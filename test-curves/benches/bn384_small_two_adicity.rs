use ark_algebra_bench_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::ProjectiveCurve;
use ark_ff::{biginteger::BigInteger384 as Repr, BigInteger, Field, PrimeField, UniformRand};
use ark_test_curves::bn384_small_two_adicity::{fq::Fq, fr::Fr, G1Affine, G1Projective as G1};

mod g1 {
    use super::*;
    ec_bench!(G1, G1Affine);
}

f_bench!(Fq, Fq, Repr, Repr, fq);
f_bench!(Fr, Fr, Repr, Repr, fr);

bencher::benchmark_main!(fq, fr, g1::group_ops);

use ark_algebra_bench_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::{CurveGroup, Group};
use ark_ff::{biginteger::BigInteger256 as Repr, BigInteger, Field, PrimeField, UniformRand};
use ark_test_curves::ed_on_bls12_381::{Affine, Fq, Fr, Projective};

f_bench!(Fq, Fq, Repr, Repr, fq);
f_bench!(Fr, Fr, Repr, Repr, fr);
ec_bench!(Projective, Affine);

bencher::benchmark_main!(fq, fr, group_ops);

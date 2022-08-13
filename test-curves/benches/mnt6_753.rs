use ark_algebra_bench_templates::*;
use ark_std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ff::{biginteger::BigInteger768 as FqRepr, BigInteger, Field, PrimeField, UniformRand};
use ark_test_curves::mnt6_753::{fq::Fq, fq3::Fq3, fr::Fr};

f_bench!(extension, Fq3, Fq3, fq3);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FqRepr, FqRepr, fr);

bencher::benchmark_main!(fq, fr, fq3);

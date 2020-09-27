use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::{
    mnt4::{G1Prepared, G2Prepared},
    PairingEngine, ProjectiveCurve,
};
use ark_ff::{
    biginteger::BigInteger320 as FqRepr, BigInteger, Field, PrimeField, SquareRootField,
    UniformRand,
};
use ark_mnt_298::mnt4_298::{
    fq::Fq, fq2::Fq2, fr::Fr, Fq4, G1Affine, G1Projective as G1, G2Affine, G2Projective as G2,
    Parameters, MNT4_298,
};

ec_bench!();
f_bench!(1, Fq2, Fq2, fq2);
f_bench!(2, Fq4, Fq4, fq4);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
pairing_bench!(MNT4_298, Fq4, prepared_v);

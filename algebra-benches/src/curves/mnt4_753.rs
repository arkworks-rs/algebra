use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ff::{
    biginteger::{BigInteger768 as FqRepr},
    BigInteger, Field, PrimeField, SquareRootField, UniformRand,
};
use ark_ec::{
    mnt4::{G1Prepared, G2Prepared},
    PairingEngine, ProjectiveCurve, 
};
use ark_mnt_753::mnt4_753::{
    fq::Fq, fq2::Fq2, fr::Fr, Fq4, G1Affine, G1Projective as G1, G2Affine, G2Projective as G2,
    Parameters, MNT4_753,
};

ec_bench!();
f_bench!(1, Fq2, Fq2, fq2);
f_bench!(2, Fq4, Fq4, fq4);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
pairing_bench!(MNT4_753, Fq4, prepared_v);

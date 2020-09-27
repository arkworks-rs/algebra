use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use ark_ec::{
    bn::{G1Prepared, G2Prepared},
    PairingEngine, ProjectiveCurve,
};
use ark_ef::{
    biginteger::{BigInteger256 as FrRepr, BigInteger256 as FqRepr},
    BigInteger, Field, PrimeField, SquareRootField, UniformRand,
};
use ark_en254::bn254::{
    fq::Fq, fq2::Fq2, fr::Fr, Bls12_381, Fq12, G1Affine, G1Projective as G1, G2Affine,
    G2Projective as G2, Parameters,
};

ec_bench!();
f_bench!(1, Fq2, Fq2, fq2);
f_bench!(2, Fq12, Fq12, fq12);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);
pairing_bench!(Bn254, Fq12, prepared_v);

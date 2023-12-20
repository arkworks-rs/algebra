use ark_ff::{
    fields::fp2::{Fp2, Fp2Config},
    Field, MontFp,
};

use crate::Fq;

pub type Fq2 = Fp2<Fq2Config>;

pub struct Fq2Config;

impl Fp2Config for Fq2Config {
    type Fp = Fq;

    /// The quadratic non-residue (17) used to construct the extension is
    /// the same as that used in [`libff`](https://github.com/scipr-lab/libff/blob/c927821ebe02e0a24b5e0f9170cec5e211a35f08/libff/algebra/curves/mnt/mnt4/mnt4_init.cpp#L102).
    const NONRESIDUE: Fq = MontFp!("17");

    /// Precomputed coefficients:
    /// `[1, 475922286169261325753349249653048451545124879242694725395555128576210262817955800483758080]`
    const FROBENIUS_COEFF_FP2_C1: &'static [Self::Fp] = &[
        Fq::ONE,
        MontFp!("475922286169261325753349249653048451545124879242694725395555128576210262817955800483758080"),
    ];
}

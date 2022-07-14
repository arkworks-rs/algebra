use crate::bls12_381::*;
use ark_ff::{fields::*, MontFp};

pub type Fq2 = Fp2<Fq2Config>;

pub struct Fq2Config;

impl Fp2Config for Fq2Config {
    type Fp = Fq;

    /// NONRESIDUE = -1
    #[rustfmt::skip]
    const NONRESIDUE: Fq = MontFp!("-1");

    /// Coefficients for the Frobenius automorphism.
    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP2_C1: &'static [Fq] = &[
        // Fq(-1)**(((q^0) - 1) / 2)
        MontFp!("1"),
        // Fq(-1)**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];

    #[inline(always)]
    fn mul_fp_by_nonresidue(fp: &Self::Fp) -> Self::Fp {
        -(*fp)
    }
}

pub const FQ2_ZERO: Fq2 = Fq2::new(FQ_ZERO, FQ_ZERO);
pub const FQ2_ONE: Fq2 = Fq2::new(FQ_ONE, FQ_ZERO);

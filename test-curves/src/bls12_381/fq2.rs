use crate::bls12_381::{Fq, FQ_ONE, FQ_ZERO};
use ark_ff::{
    fields::{AdditiveGroup, Fp2, Fp2Config},
    MontFp,
};

pub type Fq2 = Fp2<Fq2Config>;

pub struct Fq2Config;

impl Fp2Config for Fq2Config {
    type Fp = Fq;

    /// NONRESIDUE = -1
    const NONRESIDUE: Fq = MontFp!("-1");

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &[Fq] = &[
        // Fq(-1)**(((q^0) - 1) / 2)
        MontFp!("1"),
        // Fq(-1)**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];

    #[inline(always)]
    fn mul_fp_by_nonresidue_in_place(fp: &mut Self::Fp) -> &mut Self::Fp {
        fp.neg_in_place()
    }

    #[inline(always)]
    fn mul_fp_by_nonresidue_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        y.neg_in_place();
        *y += x;
    }

    #[inline(always)]
    fn mul_fp_by_nonresidue_plus_one_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        *y = *x;
    }

    #[inline(always)]
    fn sub_and_mul_fp_by_nonresidue(y: &mut Self::Fp, x: &Self::Fp) {
        *y += x;
    }
}

pub const FQ2_ZERO: Fq2 = Fq2::new(FQ_ZERO, FQ_ZERO);
pub const FQ2_ONE: Fq2 = Fq2::new(FQ_ONE, FQ_ZERO);

use super::quadratic_extension::*;
use crate::{fields::PrimeField, Field};
use core::marker::PhantomData;
use num_traits::Zero;

pub trait Fp2Parameters: 'static + Send + Sync {
    type Fp: PrimeField;

    const NONRESIDUE: Self::Fp;

    const NONRESIDUE_I64: Option<i64> = None;

    const QUADRATIC_NONRESIDUE: (Self::Fp, Self::Fp);

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &'static [Self::Fp];

    /// Return `fe * Self::NONRESIDUE`.
    #[inline(always)]
    fn mul_fp_by_nonresidue(fe: &Self::Fp) -> Self::Fp {
        Self::NONRESIDUE * fe
    }
}

pub struct Fp2ParamsWrapper<P: Fp2Parameters>(PhantomData<P>);

impl<P: Fp2Parameters> QuadExtParameters for Fp2ParamsWrapper<P> {
    type BasePrimeField = P::Fp;
    type BaseField = P::Fp;
    type FrobCoeff = P::Fp;

    const DEGREE_OVER_BASE_PRIME_FIELD: usize = 2;

    const NONRESIDUE: Self::BaseField = P::NONRESIDUE;

    const NONRESIDUE_I64: Option<i64> = P::NONRESIDUE_I64;

    const FROBENIUS_COEFF_C1: &'static [Self::FrobCoeff] = P::FROBENIUS_COEFF_FP2_C1;

    fn mul_base_field_by_frob_coeff(fe: &mut Self::BaseField, power: usize) {
        *fe *= &Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }

    #[inline(always)]
    #[ark_ff_asm::unroll_for_loops]
    fn op_and_mul_base_field_by_nonresidue(
        other: &Self::BaseField,
        fe: &Self::BaseField,
        mode: MulNonResidueMode,
    ) -> Self::BaseField {
        if let Some(mut i) = Self::NONRESIDUE_I64 {
            if mode == MulNonResidueMode::PlusAddOne {
                i += 1;
            }
            if i.abs() < (1 << 5) {
                if i == 0 {
                    return Self::BaseField::zero();
                }
                let neg = mode == MulNonResidueMode::Minus;
                let add = i >= 0 && !neg || i < 0 && neg;
                let i = i.abs() as u64;

                let mut res = *fe;

                for j in 1..5 {
                    if i >= 1 << (5 - j) {
                        res.double_in_place();
                        // if the next bit is 1
                        if (i >> (4 - j)) % 2 == 1 {
                            res += fe;
                        }
                    }
                }
                if add {
                    return *other + res;
                } else {
                    return *other - res;
                }
            }
        }
        match mode {
            MulNonResidueMode::Minus => *other - P::mul_fp_by_nonresidue(fe),
            MulNonResidueMode::Plus => *other + P::mul_fp_by_nonresidue(fe),
            MulNonResidueMode::PlusAddOne => *other + P::mul_fp_by_nonresidue(fe) + fe,
        }
    }
}

pub type Fp2<P> = QuadExtField<Fp2ParamsWrapper<P>>;

impl<P: Fp2Parameters> Fp2<P> {
    pub fn mul_assign_by_fp(&mut self, other: &P::Fp) {
        self.c0 *= other;
        self.c1 *= other;
    }
}

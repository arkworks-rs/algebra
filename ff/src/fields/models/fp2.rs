use super::quadratic_extension::*;
use crate::{fields::PrimeField, CyclotomicField, Zero};
use core::marker::PhantomData;
use core::ops::Not;

pub trait Fp2Parameters: 'static + Send + Sync {
    type Fp: PrimeField;

    const NONRESIDUE: Self::Fp;

    const QUADRATIC_NONRESIDUE: (Self::Fp, Self::Fp);

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &'static [Self::Fp];

    /// Return `fe * Self::NONRESIDUE`.
    #[inline(always)]
    fn mul_fp_by_nonresidue(fe: &Self::Fp) -> Self::Fp {
        Self::NONRESIDUE * fe
    }

    /// A specializable method for computing `x + mul_base_field_by_nonresidue(y)`
    /// This allows for optimizations when the non-residue is
    /// canonically negative in the field.
    #[inline(always)]
    fn add_and_mul_fp_by_nonresidue(x: &Self::Fp, y: &Self::Fp) -> Self::Fp {
        *x + Self::mul_fp_by_nonresidue(y)
    }

    /// A specializable method for computing `x + y + mul_base_field_by_nonresidue(y)`
    /// This allows for optimizations when the non-residue is not `-1`.
    #[inline(always)]
    fn add_and_mul_fp_by_nonresidue_plus_one(x: &Self::Fp, y: &Self::Fp) -> Self::Fp {
        let mut tmp = *x;
        tmp += y;
        Self::add_and_mul_fp_by_nonresidue(&tmp, &y)
    }

    /// A specializable method for computing `x - mul_base_field_by_nonresidue(y)`
    /// This allows for optimizations when the non-residue is
    /// canonically negative in the field.
    #[inline(always)]
    fn sub_and_mul_fp_by_nonresidue(x: &Self::Fp, y: &Self::Fp) -> Self::Fp {
        *x - Self::mul_fp_by_nonresidue(y)
    }
}

pub struct Fp2ParamsWrapper<P: Fp2Parameters>(PhantomData<P>);

impl<P: Fp2Parameters> QuadExtParameters for Fp2ParamsWrapper<P> {
    type BasePrimeField = P::Fp;
    type BaseField = P::Fp;
    type FrobCoeff = P::Fp;

    const DEGREE_OVER_BASE_PRIME_FIELD: usize = 2;

    const NONRESIDUE: Self::BaseField = P::NONRESIDUE;

    const FROBENIUS_COEFF_C1: &'static [Self::FrobCoeff] = P::FROBENIUS_COEFF_FP2_C1;

    #[inline(always)]
    fn mul_base_field_by_nonresidue(fe: &Self::BaseField) -> Self::BaseField {
        P::mul_fp_by_nonresidue(fe)
    }

    #[inline(always)]
    fn add_and_mul_base_field_by_nonresidue(
        x: &Self::BaseField,
        y: &Self::BaseField,
    ) -> Self::BaseField {
        P::add_and_mul_fp_by_nonresidue(x, y)
    }

    #[inline(always)]
    fn add_and_mul_base_field_by_nonresidue_plus_one(
        x: &Self::BaseField,
        y: &Self::BaseField,
    ) -> Self::BaseField {
        P::add_and_mul_fp_by_nonresidue_plus_one(x, y)
    }

    #[inline(always)]
    fn sub_and_mul_base_field_by_nonresidue(
        x: &Self::BaseField,
        y: &Self::BaseField,
    ) -> Self::BaseField {
        P::sub_and_mul_fp_by_nonresidue(x, y)
    }

    fn mul_base_field_by_frob_coeff(fe: &mut Self::BaseField, power: usize) {
        *fe *= &Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD];
    }
}

pub type Fp2<P> = QuadExtField<Fp2ParamsWrapper<P>>;

impl<P: Fp2Parameters> Fp2<P> {
    pub fn mul_assign_by_fp(&mut self, other: &P::Fp) {
        self.c0 *= other;
        self.c1 *= other;
    }
}

impl<P: Fp2Parameters> CyclotomicField for Fp2<P> {
    const INVERSE_IS_FAST: bool = true;
    fn cyclotomic_inverse_in_place(&mut self) -> Option<&mut Self> {
    /// As the multiplicative subgroup is of order p^2 - 1, the only non-trivial cyclotomic subgroup is of order p+1
    /// Therefore, for any element in the cyclotomic subgroup, we have that `x^(p+1) = 1`.
    /// Recall that `x^(p+1)` in a quadratic extension field is equal to the norm in the base field, so we have that
    /// `x * x.conjugate() = 1`. By uniqueness of inverses, for this subgroup, x.inverse() = x.conjugate()

        self.is_zero().not().then(|| {
            self.conjugate();
            self
        })
    }
}

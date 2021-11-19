use super::quadratic_extension::*;
use crate::fields::PrimeField;
use core::marker::PhantomData;

/// Parameters for defining degree-two extension fields.
pub trait Fp2Parameters: 'static + Send + Sync {
    /// Base prime field underlying this extension.
    type Fp: PrimeField;

    /// Quadratic non-residue in `Self::Fp` used to construct the extension
    /// field. That is, `NONRESIDUE` is such that the quadratic polynomial
    /// `f(X) = X^2 - Self::NONRESIDUE` in Fp\[X\] is irreducible in `Self::Fp`.
    const NONRESIDUE: Self::Fp;

    /// A quadratic nonresidue in Fp2, used for calculating square roots in Fp2.
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

/// Wrapper for Fp2Parameters, allowing combination of Fp2Parameters & QuadExtParameters traits
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

/// Alias for instances of quadratic extension fields. Helpful for omitting verbose
/// instantiations involving `Fp2ParamsWrapper`.
pub type Fp2<P> = QuadExtField<Fp2ParamsWrapper<P>>;

impl<P: Fp2Parameters> Fp2<P> {
    /// In-place multiply both coefficients `c0` & `c1` of the extension field
    /// `Fp2` by an element from `Fp`. The coefficients themselves
    /// are elements of `Fp`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ark_std::test_rng;
    /// # use ark_test_curves::bls12_381::{Fq as Fp, Fq2 as Fp2};
    /// # use ark_std::UniformRand;
    /// let c0: Fp = Fp::rand(&mut test_rng());
    /// let c1: Fp = Fp::rand(&mut test_rng());
    /// let mut ext_element: Fp2 = Fp2::new(c0, c1);
    ///
    /// let base_field_element: Fp = Fp::rand(&mut test_rng());
    /// ext_element.mul_assign_by_fp(&base_field_element);
    ///
    /// assert_eq!(ext_element.c0, c0*base_field_element);
    /// assert_eq!(ext_element.c1, c1*base_field_element);
    /// ```
    pub fn mul_assign_by_fp(&mut self, other: &P::Fp) {
        self.c0 *= other;
        self.c1 *= other;
    }
}

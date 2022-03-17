use crate::ProjectiveCurve;
use ark_ff::{Field, PrimeField, SquareRootField, Zero};

pub mod bls12;
pub mod bn;
pub mod bw6;
pub mod mnt4;
pub mod mnt6;
pub mod short_weierstrass_jacobian;
pub mod twisted_edwards_extended;

/// Elliptic curves can be represented via different "models" with varying
/// efficiency properties.
/// `ModelParameters` bundles together the types that are common
/// to all models of the given curve, namely the `BaseField` over which the
/// curve is defined, and the `ScalarField` defined by the appropriate
/// prime-order subgroup of the curve.
pub trait ModelParameters: Send + Sync + Sized + 'static {
    /// Base field that the curve is defined over.
    type BaseField: Field + SquareRootField;
    /// Finite prime field corresponding to an appropriate prime-order subgroup
    /// of the curve group.
    type ScalarField: PrimeField + SquareRootField + Into<<Self::ScalarField as PrimeField>::BigInt>;

    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;
}

/// Constants and convenience functions that collectively define the [Short Weierstrass model](https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html)
/// of the curve. In this model, the curve equation is `y² = x³ + a * x + b`,
/// for constants `a` and `b`.
pub trait SWModelParameters: ModelParameters {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `b` of the curve equation.
    const COEFF_B: Self::BaseField;
    /// Coefficients of the base point of the curve
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    /// Helper method for computing `elem * Self::COEFF_A`.
    ///
    /// The default implementation should be overridden only if
    /// the product can be computed faster than standard field multiplication
    /// (eg: via doubling if `COEFF_A == 2`, or if `COEFF_A.is_zero()`).
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    /// Helper method for computing `elem + Self::COEFF_B`.
    ///
    /// The default implementation should be overridden only if
    /// the sum can be computed faster than standard field addition (eg: via
    /// doubling).
    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        if !Self::COEFF_B.is_zero() {
            let mut copy = *elem;
            copy += &Self::COEFF_B;
            return copy;
        }
        *elem
    }

    /// Check if the provided curve point is in the prime-order subgroup.
    ///
    /// The default implementation multiplies `item` by the order `r` of the
    /// prime-order subgroup, and checks if the result is one.
    /// Implementors can choose to override this default impl
    /// if the given curve has faster methods
    /// for performing this check (for example, via leveraging curve
    /// isomorphisms).
    fn is_in_correct_subgroup_assuming_on_curve(
        item: &short_weierstrass_jacobian::GroupAffine<Self>,
    ) -> bool {
        Self::mul_affine(item, Self::ScalarField::characteristic()).is_zero()
    }

    /// Default implementation of group multiplication for projective
    /// coordinates
    fn mul_projective(
        base: &short_weierstrass_jacobian::GroupProjective<Self>,
        scalar: &[u64],
    ) -> short_weierstrass_jacobian::GroupProjective<Self> {
        let mut res = short_weierstrass_jacobian::GroupProjective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base;
            }
        }

        res
    }

    /// Default implementation of group multiplication for affine
    /// coordinates.
    fn mul_affine(
        base: &short_weierstrass_jacobian::GroupAffine<Self>,
        scalar: &[u64],
    ) -> short_weierstrass_jacobian::GroupProjective<Self> {
        let mut res = short_weierstrass_jacobian::GroupProjective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res.add_assign_mixed(base)
            }
        }

        res
    }
}

/// Constants and convenience functions that collectively define the [Twisted Edwards model](https://www.hyperelliptic.org/EFD/g1p/auto-twisted.html)
/// of the curve. In this model, the curve equation is
/// `a * x² + y² = 1 + d * x² * y²`, for constants `a` and `d`.
pub trait TEModelParameters: ModelParameters {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `d` of the curve equation.
    const COEFF_D: Self::BaseField;
    /// Coefficients of the base point of the curve
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    /// Model parameters for the Montgomery curve that is birationally
    /// equivalent to this curve.
    type MontgomeryModelParameters: MontgomeryModelParameters<BaseField = Self::BaseField>;

    /// Helper method for computing `elem * Self::COEFF_A`.
    ///
    /// The default implementation should be overridden only if
    /// the product can be computed faster than standard field multiplication
    /// (eg: via doubling if `COEFF_A == 2`, or if `COEFF_A.is_zero()`).
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    /// Checks that the current point is in the prime order subgroup given
    /// the point on the curve.
    fn is_in_correct_subgroup_assuming_on_curve(
        item: &twisted_edwards_extended::GroupAffine<Self>,
    ) -> bool {
        Self::mul_affine(item, Self::ScalarField::characteristic()).is_zero()
    }

    /// Default implementation of group multiplication for projective
    /// coordinates
    fn mul_projective(
        base: &twisted_edwards_extended::GroupProjective<Self>,
        scalar: &[u64],
    ) -> twisted_edwards_extended::GroupProjective<Self> {
        let mut res = twisted_edwards_extended::GroupProjective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base;
            }
        }

        res
    }

    /// Default implementation of group multiplication for affine
    /// coordinates
    fn mul_affine(
        base: &twisted_edwards_extended::GroupAffine<Self>,
        scalar: &[u64],
    ) -> twisted_edwards_extended::GroupProjective<Self> {
        let mut res = twisted_edwards_extended::GroupProjective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res.add_assign_mixed(base)
            }
        }

        res
    }
}

/// Constants and convenience functions that collectively define the [Montgomery model](https://www.hyperelliptic.org/EFD/g1p/auto-montgom.html)
/// of the curve. In this model, the curve equation is
/// `b * y² = x³ + a * x² + x`, for constants `a` and `b`.
pub trait MontgomeryModelParameters: ModelParameters {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `b` of the curve equation.
    const COEFF_B: Self::BaseField;

    /// Model parameters for the Twisted Edwards curve that is birationally
    /// equivalent to this curve.
    type TEModelParameters: TEModelParameters<BaseField = Self::BaseField>;
}

use crate::AffineCurve;
use ark_ff::{fields::BitIteratorBE, Field, PrimeField, SquareRootField, Zero};

pub mod bls12;
pub mod bn;
pub mod bw6;
pub mod mnt4;
pub mod mnt6;
pub mod short_weierstrass_jacobian;
pub mod twisted_edwards_extended;

/// Model parameters for an elliptic curve.
pub trait ModelParameters: Send + Sync + Sized + 'static {
    type BaseField: Field + SquareRootField;
    type ScalarField: PrimeField + SquareRootField + Into<<Self::ScalarField as PrimeField>::BigInt>;
    type Affine: AffineCurve<BaseField = Self::BaseField, ScalarField = Self::ScalarField>;

    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;

    /// Checks that the current point is in the prime order subgroup given
    /// the point on the curve.
    fn is_in_correct_subgroup_assuming_on_curve(item: &Self::Affine) -> bool {
        item.mul_bits(BitIteratorBE::new(Self::ScalarField::characteristic()))
            .is_zero()
    }
}

/// Model parameters for a Short Weierstrass curve.
pub trait SWModelParameters:
    ModelParameters<Affine = short_weierstrass_jacobian::GroupAffine<Self>>
{
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        if !Self::COEFF_B.is_zero() {
            let mut copy = *elem;
            copy += &Self::COEFF_B;
            return copy;
        }
        *elem
    }
}

/// Model parameters for a Twisted Edwards curve.
pub trait TEModelParameters:
    ModelParameters<Affine = twisted_edwards_extended::GroupAffine<Self>>
{
    const COEFF_A: Self::BaseField;
    const COEFF_D: Self::BaseField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    type MontgomeryModelParameters: MontgomeryModelParameters<BaseField = Self::BaseField>;

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }
}

/// Model parameters for a Montgomery curve.
pub trait MontgomeryModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;

    type TEModelParameters: TEModelParameters<BaseField = Self::BaseField>;
}

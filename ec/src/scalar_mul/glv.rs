use crate::{CurveConfig, CurveGroup};

/// The GLV parameters for computing the endomorphism and scalar decomposition.
pub trait GLVConfig: Send + Sync + 'static + CurveConfig {
    /// A representation of curve points that enables efficient arithmetic by
    /// avoiding inversions.
    type Curve: CurveGroup<Config = Self>;

    // Constants that are used to calculate `phi(G) := lambda*G`.

    /// Coefficient `a_1` of `f(y) = a_1 * (y + a_2) * (y + a_3)`.
    const COEFF_A1: Self::BaseField;
    /// Coefficient `a_2` of `f(y) = a_1 * (y + a_2) * (y + a_3)`.
    const COEFF_A2: Self::BaseField;
    /// Coefficient `a_3` of `f(y) = a_1 * (y + a_2) * (y + a_3)`.
    const COEFF_A3: Self::BaseField;

    /// Coefficient `b_1` of `g(y) = b_1 * (y + b_2) * (y + b_3)`.
    const COEFF_B1: Self::BaseField;
    /// Coefficient `b_2` of `g(y) = b_1 * (y + b_2) * (y + b_3)`.
    const COEFF_B2: Self::BaseField;
    /// Coefficient `b_3` of `g(y) = b_1 * (y + b_2) * (y + b_3)`.
    const COEFF_B3: Self::BaseField;

    /// Coefficient `c_1` of `h(y) = (y + c_1) * (y + c_2)`.
    const COEFF_C1: Self::BaseField;
    /// Coefficient `c_2` of `h(y) = (y + c_1) * (y + c_2)`.
    const COEFF_C2: Self::BaseField;

    // Constants for scalar decomposition.
    // This is a 2x2 matrix, which is practically the LLL-reduced bases.

    /// The first element of the matrix for scalar decomposition.
    const COEFF_N11: Self::ScalarField;
    /// The second element of the matrix for scalar decomposition.
    const COEFF_N12: Self::ScalarField;
    /// The third element of the matrix for scalar decomposition.
    const COEFF_N21: Self::ScalarField;
    /// The forth element of the matrix for the scalar decomposition.
    const COEFF_N22: Self::ScalarField;

    /// Maps a point G to phi(G):= lambda G where psi is the endomorphism.
    // On an affine curve, the function takes the following steps:
    //  f(y) = a_1 * (y + a_2) * (y + a_3)
    //  g(y) = b_1 * (y + b_2) * (y + b_3)
    //  h(y) = (y + c_1) * (y + c_2)
    //  return (x',y') where
    //  x' = x * f(y) / y
    //  y' = g(y) / h(y)
    fn endomorphism(
        base: &<Self::Curve as CurveGroup>::Affine,
    ) -> <Self::Curve as CurveGroup>::Affine;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(k: &Self::ScalarField) -> (Self::ScalarField, Self::ScalarField);

    /// Performs GLV multiplication.
    fn glv_mul(
        base: &<Self::Curve as CurveGroup>::Affine,
        scalar: &Self::ScalarField,
    ) -> Self::Curve;
}

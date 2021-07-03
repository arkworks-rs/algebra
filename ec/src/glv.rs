use crate::ModelParameters;

/// The GLV parameters that are useful to compute the endomorphism 
/// and scalar decomposition.
pub trait GLVParameters: Send + Sync + 'static + ModelParameters {
    type CurveAffine;
    type CurveProjective;
    
    // phi(P) = lambda*P for all P
    // constants that are used to calculate phi(P)
    const COEFF_A1: Self::BaseField;
    const COEFF_A2: Self::BaseField;
    const COEFF_A3: Self::BaseField;
    const COEFF_B1: Self::BaseField;
    const COEFF_B2: Self::BaseField;
    const COEFF_B3: Self::BaseField;
    const COEFF_C1: Self::BaseField;
    const COEFF_C2: Self::BaseField;

    // constants that are used to perform scalar decomposition
    // This is a matrix which is practically the LLL reduced bases
    const COEFF_N11: Self::ScalarField;
    const COEFF_N12: Self::ScalarField;
    const COEFF_N21: Self::ScalarField;
    const COEFF_N22: Self::ScalarField;

    /// mapping a point G to phi(G):= lambda G where psi is the endomorphism
    fn endomorphism(base: &Self::CurveAffine) -> Self::CurveAffine;

    /// decompose a scalar s into k1, k2, s.t. s = k1 + lambda k2
    fn scalar_decomposition(k: &Self::ScalarField) -> (Self::ScalarField, Self::ScalarField);

    /// perform GLV multiplication
    fn glv_mul(base: &Self::CurveAffine, scalar: &Self::ScalarField) -> Self::CurveProjective;
}

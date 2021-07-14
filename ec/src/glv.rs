use crate::ModelParameters;

/// The GLV parameters that are useful to compute the endomorphism
/// and scalar decomposition.
pub trait GLVParameters: Send + Sync + 'static + ModelParameters {
    type CurveAffine;
    type CurveProjective;


    // constants that are used to calculate phi(G) := lambda*G

    /// first coeff of f(y) = a_1 * (y + a_2) * (y + a_3)
    const COEFF_A1: Self::BaseField;
    /// second coeff of f(y) = a_1 * (y + a_2) * (y + a_3)
    const COEFF_A2: Self::BaseField;
    /// third coeff of f(y) = a_1 * (y + a_2) * (y + a_3)
    const COEFF_A3: Self::BaseField;
    ///  first coeff of g(y) = b_1 * (y + b_2) * (y + b_3)
    const COEFF_B1: Self::BaseField;
    ///  second coeff of g(y) = b_1 * (y + b_2) * (y + b_3)
    const COEFF_B2: Self::BaseField;
    /// third coeff of g(y) = b_1 * (y + b_2) * (y + b_3)
    const COEFF_B3: Self::BaseField;
    ///  first coeff of h(y) = (y + c_1) * (y + c_2)
    const COEFF_C1: Self::BaseField;
    ///  second coeff of h(y) = (y + c_1) * (y + c_2)
    const COEFF_C2: Self::BaseField;

    // constants that are used to perform scalar decomposition
    // This is a matrix which is practically the LLL reduced bases

    // The first element of the matrix that is used to find the scalar decomposition
    const COEFF_N11: Self::ScalarField;
    // The second element of the matrix that is used to find the scalar decomposition
    const COEFF_N12: Self::ScalarField;
    // The third element of the matrix that is used to find the scalar decomposition
    const COEFF_N21: Self::ScalarField;
    // The forth element of the matrix that is used to find the scalar decomposition
    const COEFF_N22: Self::ScalarField;

    /// mapping a point G to phi(G):= lambda G where psi is the endomorphism
    // assuming affine curve, the scheme takes in the following steps
    //  f(y) = a_1 * (y + a_2) * (y + a_3)
    //  g(y) = b_1 * (y + b_2) * (y + b_3)
    //  h(y) = (y + c_1) * (y + c_2)
    // return (x',y') where
    //  x' = x * f(y) / y
    //  y' = g(y) / h(y)
    fn endomorphism(base: &Self::CurveAffine) -> Self::CurveAffine;

    /// decompose a scalar s into k1, k2, s.t. s = k1 + lambda k2
    fn scalar_decomposition(k: &Self::ScalarField) -> (Self::ScalarField, Self::ScalarField);

    /// perform GLV multiplication
    fn glv_mul(base: &Self::CurveAffine, scalar: &Self::ScalarField) -> Self::CurveProjective;
}

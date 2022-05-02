use crate::{
    msm::{ScalarMul, VariableBase},
    AffineCurve, ModelParameters,
};
use ark_ff::PrimeField;
use num_bigint::BigUint;

/// The GLV parameters for computing the endomorphism and scalar decomposition.
pub trait GLVParameters: Send + Sync + 'static + ModelParameters + ScalarMul {
    /// A representation of curve points that enables efficient arithmetic by
    /// avoiding inversions.
    type CurveProjective;

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

    /// LAMBDA the eigenvalue corresponding to the endomorphism
    const LAMBDA: Self::ScalarField;

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
    /// the sign of the coefficients of the matrix N.
    const SGN_N: [bool;4];

    fn endomorphism(base: &Self::CurveAffine) -> Self::CurveAffine;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: &Self::ScalarField,
    ) -> (Self::ScalarField, bool, Self::ScalarField, bool) {
        // check this algorithm because seems to not work...
        let scalar: BigUint = (*k).into_bigint().into();
        let n11: BigUint = Self::COEFF_N11.into_bigint().into();
        let n12: BigUint = Self::COEFF_N12.into_bigint().into();
        let n21: BigUint = Self::COEFF_N21.into_bigint().into();
        let n22: BigUint = Self::COEFF_N22.into_bigint().into();

        let r: BigUint = Self::ScalarField::MODULUS.into();


        // issue with the sign for Bandersnatch, when n22 is negative... 
        
        println!("n22={}", n22);

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r
        let beta_1 = &scalar * &n22;
        let beta_2 = &scalar * &n12; // (the negative will be done after)

        let beta_1 = &beta_1 / &r;
        let beta_2 = &beta_2 / &r;
        println!("β1={}", beta_1);
        println!("β2={}", beta_2);

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = 1/r * (β1N11 - β2N21, β1N12 - β2N22)
        
        let b1: BigUint = &beta_1 * &n11 - &beta_2 * &n21;
        let b2: BigUint = (&beta_1 * &n12 - &beta_2 * &n22) % r;
        println!("b1={}", b1);
        println!("b2={}", b2);

        let is_k1_pos = scalar > b1;
        let k1 = if is_k1_pos {
            Self::ScalarField::from(scalar - b1)
        } else {
            Self::ScalarField::from(b1 - scalar)
        };
        let is_k2_pos = false;
        let k2 = Self::ScalarField::from(b2);
        (k1, is_k1_pos, k2, is_k2_pos)
    }

    /// Performs GLV multiplication.
    fn glv_mul(
        base: &Self::CurveAffine,
        scalar: &Self::ScalarField,
    ) -> <<Self as ScalarMul>::CurveAffine as AffineCurve>::Projective {
        let (k1, is_k1_positive, k2, is_k2_positive) = Self::scalar_decomposition(scalar);
        VariableBase::two_scalar_mul::<Self>(
            *base,
            k1.into_bigint(),
            is_k1_positive,
            Self::endomorphism(base),
            k2.into_bigint(),
            is_k2_positive,
        )
    }
}

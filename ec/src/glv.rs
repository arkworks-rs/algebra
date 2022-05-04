use std::cmp::{max, min};

use crate::{
    msm::{ScalarMul, VariableBase},
    AffineCurve, ModelParameters, models,
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
    const COEFF_N: [<<Self as ModelParameters>::ScalarField as PrimeField>::BigInt; 4];
    const SGN_N: [bool; 4];

    fn endomorphism(base: &Self::CurveAffine) -> Self::CurveAffine;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: Self::ScalarField,
    ) -> 
    (
        <Self as ModelParameters>::ScalarField,
        bool,
        <Self as ModelParameters>::ScalarField,
        bool,
    ) 
    {
        let scalar:BigUint = k.into_bigint().into();
        
        let (sgn_n11, n11): (bool, BigUint) = (Self::SGN_N[0], Self::COEFF_N[0].into());
        let (sgn_n12, n12): (bool, BigUint) = (Self::SGN_N[1], Self::COEFF_N[1].into());
        let (sgn_n21, n21): (bool, BigUint) = (Self::SGN_N[2], Self::COEFF_N[2].into());
        let (sgn_n22, n22): (bool, BigUint) = (Self::SGN_N[3], Self::COEFF_N[3].into());
        
        let r: BigUint = Self::ScalarField::MODULUS.into();

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r
        let beta_1 = &scalar * &n22 / &r; // sgn: sgn_n22
        let beta_2 = &scalar * &n12 / &r; // sgn: sgn_n12

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = (β1N11 + β2N21, β1N12 + β2N22) with the signs!
        //   = (b11   + b12  , b21   + b22)   with the signs!

        // b1
        let b11 = &beta_1 * &n11;
        let sgn_b11 = sgn_n22 == sgn_n11;
        let b12 = &beta_2 * &n21;
        let sgn_b12 = sgn_n12 == sgn_n21;
        let (b1, sgn_b1) =
        if sgn_b11 == sgn_b12 {
            (
                (b11+b12) % &r,
                sgn_b11
            )
        }
        else {
            if b11>b12 {
                (b11 - b12, sgn_b11)
            }
            else {
                (b12 - b11, sgn_b12)
            }
        };
        
        // b2
        let b21 = &beta_1 * &n12;
        let sgn_b21 = sgn_n22 == sgn_n12;
        let b22 = &beta_2 * &n22;
        let sgn_b22 = sgn_n12 == sgn_n22;
        let (b2, sgn_b2) = 
        if sgn_b21 == sgn_b22 {
            (
                (b21+b22) % &r,
                sgn_b21
            )
        }
        else {
            if b21>b22 {
                (b21 - b22, sgn_b21)
            }
            else {
            (b22-b21, sgn_b22)
            }
        };
        
        // k1
        let (k1, sgn_k1) =
        if !sgn_b1 {
            (scalar + b1, true)
        }
        else {
            if scalar > b1 {
                (scalar - b1, true)
            }
            else {
                (b1-scalar, false)
            }
        };

        // k2
        let (k2, sgn_k2) = (b2, sgn_b2);

        (Self::ScalarField::from(k1), sgn_k1, Self::ScalarField::from(k2), sgn_k2)
    }

    /// Performs GLV multiplication.
    fn glv_mul(
        base: &Self::CurveAffine,
        scalar: Self::ScalarField,
    ) -> <<Self as ScalarMul>::CurveAffine as AffineCurve>::Projective
    {
        let (k1, sgn_k1, k2, sgn_k2) = Self::scalar_decomposition(scalar);
        VariableBase::two_scalar_mul::<Self>(
            *base,
            k1.into_bigint(),
            sgn_k1,
            Self::endomorphism(base),
            k2.into_bigint(),
            sgn_k2,
        )
    }
}

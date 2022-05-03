use crate::{
    msm::{ScalarMul, VariableBase},
    AffineCurve, ModelParameters, models,
};
use ark_ff::PrimeField;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::Signed;

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
    const COEFF_N: [[u32; 4]; 4];
    const SGN_N: [Sign; 4];

    fn endomorphism(base: &Self::CurveAffine) -> Self::CurveAffine;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: BigInt,
    ) -> 
    (
        <<Self as ModelParameters>::ScalarField as PrimeField>::BigInt,
        bool,
        <<Self as ModelParameters>::ScalarField as PrimeField>::BigInt,
        bool,
    ) 
    where <Self as models::ModelParameters>::ScalarField: From<num_bigint::BigInt>
    {
        let scalar: BigInt = k;
        
        let n11 = BigInt::new(Self::SGN_N[0], Self::COEFF_N[0].to_vec());
        let n12 = BigInt::new(Self::SGN_N[1], Self::COEFF_N[1].to_vec());
        let n21 = BigInt::new(Self::SGN_N[2], Self::COEFF_N[2].to_vec());
        let n22 = BigInt::new(Self::SGN_N[3], Self::COEFF_N[3].to_vec());

        let r: BigUint = Self::ScalarField::MODULUS.into();
        let r: BigInt = r.into();

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r
        let beta_1 = &scalar * &n22 / &r;
        let beta_2 = &scalar * &n12 / &r;

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = 1/r * (β1N11 - β2N21, β1N12 - β2N22)
        let b1 = (&beta_1 * &n11 - &beta_2 * &n21) % &r;
        let b2 = (&beta_1 * &n12 - &beta_2 * &n22) % &r;

        let k1 = scalar-b1;
        let k2 = -b2;

        (
            Self::ScalarField::from(k1.abs()).into_bigint(),
            k1.is_positive(),
            Self::ScalarField::from(k2.abs()).into_bigint(),
            k2.is_positive(),
        )
    }

    /// Performs GLV multiplication.
    fn glv_mul(
        base: &Self::CurveAffine,
        scalar: BigInt,
    ) -> <<Self as ScalarMul>::CurveAffine as AffineCurve>::Projective
    where <Self as models::ModelParameters>::ScalarField: From<num_bigint::BigInt> 
    {
        // let (k1, is_k1_positive, k2, is_k2_positive) = Self::scalar_decomposition(scalar);
        let (k1, k1_sgn, k2, k2_sgn) = Self::scalar_decomposition(scalar);
        VariableBase::two_scalar_mul::<Self>(
            *base,
            k1,
            k1_sgn,
            Self::endomorphism(base),
            k2,
            k2_sgn,
        )
    }
}

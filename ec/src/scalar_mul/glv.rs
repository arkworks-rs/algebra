use core::ops::{Mul, Neg};

use crate::{
    short_weierstrass::Affine, AffineRepr, CurveConfig, CurveGroup, ScalarMul, VariableBaseMSM,
};
use ark_ff::PrimeField;
use num_bigint::BigUint;

/// The GLV parameters for computing the endomorphism and scalar decomposition.
pub trait GLVConfig: Send + Sync + 'static + CurveConfig {
    // /// A representation of curve points that enables efficient arithmetic by
    // /// avoiding inversions.
    // type Curve: CurveGroup<Config = Self>;

    // Constants that are used to calculate `phi(G) := lambda*G`.

    /// Coefficients for the CM endomorphism
    const COEFFS_ENDOMORPHISM: &'static [Self::BaseField];

    /// LAMBDA the eigenvalue corresponding to the endomorphism
    const LAMBDA: Self::ScalarField;

    // Constants for scalar decomposition.
    // This is a 2x2 matrix, which is practically the LLL-reduced bases.
    // We require this matrix N to satisfy det(N) = ScalarField::characteristic().

    const COEFF_N: [<Self as CurveConfig>::ScalarField; 4];
    const SGN_N: [bool; 4];

    // /// Maps a point G to phi(G):= lambda G where psi is the endomorphism.
    // fn endomorphism(
    //     base: &<Self::Curve as CurveGroup>::Affine,
    // ) -> <Self::Curve as CurveGroup>::Affine;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: Self::ScalarField,
    ) -> (
        <Self as CurveConfig>::ScalarField,
        bool,
        <Self as CurveConfig>::ScalarField,
        bool,
    ) {
        let scalar: BigUint = k.into_bigint().into();

        let (sgn_n11, n11): (bool, BigUint) = (Self::SGN_N[0], Self::COEFF_N[0].into());
        let (sgn_n12, n12): (bool, BigUint) = (Self::SGN_N[1], Self::COEFF_N[1].into());
        let (sgn_n21, n21): (bool, BigUint) = (Self::SGN_N[2], Self::COEFF_N[2].into());
        let (sgn_n22, n22): (bool, BigUint) = (Self::SGN_N[3], Self::COEFF_N[3].into());

        let r: BigUint = Self::ScalarField::MODULUS.into();

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r

        let beta_1 = &scalar * &n22 / &r;
        let sgn_beta_1 = sgn_n22;
        let beta_2 = &scalar * &n12 / &r;
        let sgn_beta_2 = !sgn_n12;

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = (β1N11 + β2N21, β1N12 + β2N22) with the signs!
        //   = (b11   + b12  , b21   + b22)   with the signs!

        // b1
        let b11 = &beta_1 * &n11;
        let sgn_b11 = sgn_beta_1 == sgn_n11;
        let b12 = &beta_2 * &n21;
        let sgn_b12 = sgn_beta_2 == sgn_n21;
        let (b1, sgn_b1) = if sgn_b11 == sgn_b12 {
            ((b11 + b12) % &r, sgn_b11)
        } else {
            if b11 > b12 {
                (b11 - b12, sgn_b11)
            } else {
                (b12 - b11, sgn_b12)
            }
        };

        // b2
        let b21 = &beta_1 * &n12;
        let sgn_b21 = sgn_beta_1 == sgn_n12;
        let b22 = &beta_2 * &n22;
        let sgn_b22 = sgn_beta_2 == sgn_n22;

        let (b2, sgn_b2) = if sgn_b21 == sgn_b22 {
            ((b21 + b22) % &r, sgn_b21)
        } else {
            if b21 > b22 {
                (b21 - b22, sgn_b21)
            } else {
                (b22 - b21, sgn_b22)
            }
        };

        // k1
        let (k1, sgn_k1) = if !sgn_b1 {
            (scalar + b1, true)
        } else {
            if scalar > b1 {
                (scalar - b1, true)
            } else {
                (b1 - scalar, false)
            }
        };

        // k2
        let (k2, sgn_k2) = (b2, !sgn_b2);

        (
            Self::ScalarField::from(k1),
            sgn_k1,
            Self::ScalarField::from(k2),
            sgn_k2,
        )
    }
}

//
// This is not working
//

pub trait GLV<T: ScalarMul> {
    fn endomorphism(p: T) -> T {
        p
    }

    fn glv_mul<C: GLVConfig>(p: T, k: C::ScalarField) -> T {
        let (k1, sgn_k1, k2, sgn_k2) = C::scalar_decomposition(k);
        let p1 = if sgn_k1 { p } else { -p };
        let p2 = if sgn_k2 {
            Self::endomorphism(p)
        } else {
            -Self::endomorphism(p)
        };
        p1.mul_bigint(k1.into_bigint()) + p2.mul_bigint(k2.into_bigint())
    }
}

//     fn glv_mul<V: VariableBaseMSM, C:GLVConfig> (
//         base: AffineRepr<C>,
//         scalar: V::ScalarField,
//     ) {
//     // ) -> V {
//         let (k1, sgn_k1, k2, sgn_k2) = C::scalar_decomposition(scalar);
//         let b1 = if sgn_k1 { base } else {-base};
//         let mut b2: V::MulBase = C::endomorphism::<V>(base);
//         b2 = if sgn_k2 { b2 } else {-b2};
//         let x = b2.mul(k2);
//         // VariableBaseMSM::msm_bigint(
//         //     &[b1, b2],
//         //     &[k1.into_bigint(), k2.into_bigint()],
//         // )
//     }
// }

// /// Performs NAF GLV multiplication.
// fn naf_glv_mul(
//     base: &<Self::Curve as CurveGroup>::Affine,
//     scalar: Self::ScalarField,
// ) -> Self::Curve {
//     let (k1, sgn_k1, k2, sgn_k2) = Self::scalar_decomposition(scalar);
//     variable_base::naf_two_scalar_mul::<Self>(
//         *base,
//         k1.into_bigint(),
//         sgn_k1,
//         Self::endomorphism(base),
//         k2.into_bigint(),
//         sgn_k2,
//     )
// }

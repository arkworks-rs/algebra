use crate::Group;
use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    CurveConfig, CurveGroup,
};
use ark_ff::{PrimeField, Zero};
use ark_std::vec::Vec;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::Signed;

/// The GLV parameters for computing the endomorphism and scalar decomposition.
pub trait GLVConfig: Send + Sync + 'static + SWCurveConfig {
    /// Constants that are used to calculate `phi(G) := lambda*G`.

    /// The coefficients of the endomorphism
    const ENDO_COEFFS: &'static [Self::BaseField];

    /// The eigenvalue corresponding to the endomorphism.
    const LAMBDA: Self::ScalarField;

    /// A 4-element vector representing a 2x2 matrix of coefficients the for scalar decomposition, s.t. k-th entry in the vector is at col i, row j in the matrix, with ij = BE binary decomposition of k.
    /// The entries are the LLL-reduced bases.
    /// The determinant of this matrix must equal `ScalarField::characteristic()`.
    const SCALAR_DECOMP_COEFFS: [(bool, Self::ScalarField); 4];

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: Self::ScalarField,
    ) -> (
        <Self as CurveConfig>::ScalarField,
        bool,
        <Self as CurveConfig>::ScalarField,
        bool,
    ) {
        let scalar: BigInt = k.into_bigint().into().into();

        let coeff_bigints: [BigInt; 4] = Self::SCALAR_DECOMP_COEFFS
            .iter()
            .map(|x| {
                BigInt::from_biguint(
                    x.0.then(|| Sign::Plus).unwrap_or_else(|| Sign::Minus),
                    x.1.into(),
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let [n11, n12, n21, n22] = coeff_bigints;

        let r = BigInt::from(Self::ScalarField::MODULUS.into());

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r

        let beta_1 = &scalar * &n22 / &r;
        let beta_2 = &scalar * &n12 / &r;

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = (β1N11 + β2N21, β1N12 + β2N22) with the signs!
        //   = (b11   + b12  , b21   + b22)   with the signs!

        // b1
        let b11 = &beta_1 * &n11;
        let b12 = &beta_2 * &n21;
        let b1 = (b11 + b12) % &r;

        // b2
        let b21 = &beta_1 * &n12;
        let b22 = &beta_2 * &n22;
        let b2 = (b21 + b22) % &r;

        let k1 = &scalar - b1;

        // k2
        let k2 = -b2;
        let k2_abs = BigUint::try_from(k2.abs()).unwrap();

        (
            Self::ScalarField::from(k1.to_biguint().unwrap()),
            k1.sign() == Sign::Plus,
            Self::ScalarField::from(k2_abs),
            k2.sign() == Sign::Plus,
        )
    }

    fn endomorphism(p: &Projective<Self>) -> Projective<Self>;

    fn endomorphism_affine(p: &Affine<Self>) -> Affine<Self>;

    fn glv_mul_projective(p: Projective<Self>, k: Self::ScalarField) -> Projective<Self> {
        let (k1, sgn_k1, k2, sgn_k2) = Self::scalar_decomposition(k);

        let mut b1 = p;
        let mut b2 = Self::endomorphism(&p);

        if !sgn_k1 {
            b1 = -b1;
        }
        if !sgn_k2 {
            b2 = -b2;
        }

        let b1b2 = b1 + b2;

        let iter_k1 = ark_ff::BitIteratorBE::new(k1.into_bigint());
        let iter_k2 = ark_ff::BitIteratorBE::new(k2.into_bigint());

        let mut res = Projective::<Self>::zero();
        let mut skip_zeros = true;
        for pair in iter_k1.zip(iter_k2) {
            if skip_zeros && pair == (false, false) {
                skip_zeros = false;
                continue;
            }
            res.double_in_place();
            match pair {
                (true, false) => res += b1,
                (false, true) => res += b2,
                (true, true) => res += b1b2,
                (false, false) => {},
            }
        }
        res
    }

    fn glv_mul_affine(p: Affine<Self>, k: Self::ScalarField) -> Affine<Self> {
        let (k1, sgn_k1, k2, sgn_k2) = Self::scalar_decomposition(k);

        let mut b1 = p;
        let mut b2 = Self::endomorphism_affine(&p);

        if !sgn_k1 {
            b1 = -b1;
        }
        if !sgn_k2 {
            b2 = -b2;
        }

        let b1b2 = b1 + b2;

        let iter_k1 = ark_ff::BitIteratorBE::new(k1.into_bigint());
        let iter_k2 = ark_ff::BitIteratorBE::new(k2.into_bigint());

        let mut res = Projective::<Self>::zero();
        let mut skip_zeros = true;
        for pair in iter_k1.zip(iter_k2) {
            if skip_zeros && pair == (false, false) {
                skip_zeros = false;
                continue;
            }
            res.double_in_place();
            match pair {
                (true, false) => res += b1,
                (false, true) => res += b2,
                (true, true) => res += b1b2,
                (false, false) => {},
            }
        }
        res.into_affine()
    }
}

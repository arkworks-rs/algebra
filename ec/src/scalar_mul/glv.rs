use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    AdditiveGroup, CurveGroup,
};
use ark_ff::{PrimeField, Zero};
use ark_std::ops::Neg;
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed};

/// The GLV parameters for computing the endomorphism and scalar decomposition.
pub trait GLVConfig: Send + Sync + 'static + SWCurveConfig {
    /// Constant used to calculate `phi(G) := lambda*G`.
    ///
    /// The coefficients of the endomorphism
    const ENDO_COEFFS: &[Self::BaseField];

    /// Constant used to calculate `phi(G) := lambda*G`.
    ///
    /// The eigenvalue corresponding to the endomorphism.
    const LAMBDA: Self::ScalarField;

    /// A 4-element vector representing a 2x2 matrix of coefficients the for scalar decomposition, s.t. k-th entry in the vector is at col i, row j in the matrix, with ij = BE binary decomposition of k.
    /// The entries are the LLL-reduced bases.
    /// The determinant of this matrix must equal `ScalarField::characteristic()`.
    const SCALAR_DECOMP_COEFFS: [(bool, <Self::ScalarField as PrimeField>::BigInt); 4];

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2,
    fn scalar_decomposition(
        k: Self::ScalarField,
    ) -> ((bool, Self::ScalarField), (bool, Self::ScalarField)) {
        let scalar: BigInt = k.into_bigint().into().into();

        let [n11, n12, n21, n22] = Self::SCALAR_DECOMP_COEFFS.map(|x| {
            let sign = if x.0 { Sign::Plus } else { Sign::Minus };
            BigInt::from_biguint(sign, x.1.into())
        });

        let r = BigInt::from(Self::ScalarField::MODULUS.into());

        // beta = vector([k,0]) * self.curve.N_inv
        // The inverse of N is 1/r * Matrix([[n22, -n12], [-n21, n11]]).
        // so β = (k*n22, -k*n12)/r

        let beta_1 = {
            let (mut div, rem) = (&scalar * &n22).div_rem(&r);
            if (&rem + &rem) > r {
                div += BigInt::one();
            }
            div
        };
        let beta_2 = {
            let (mut div, rem) = (&scalar * &n12.clone().neg()).div_rem(&r);
            if (&rem + &rem) > r {
                div += BigInt::one();
            }
            div
        };

        // b = vector([int(beta[0]), int(beta[1])]) * self.curve.N
        // b = (β1N11 + β2N21, β1N12 + β2N22) with the signs!
        //   = (b11   + b12  , b21   + b22)   with the signs!

        // b1
        let b11 = &beta_1 * &n11;
        let b12 = &beta_2 * &n21;
        let b1 = b11 + b12;

        // b2
        let b21 = &beta_1 * &n12;
        let b22 = &beta_2 * &n22;
        let b2 = b21 + b22;

        let k1 = &scalar - b1;
        let k1_abs = BigUint::try_from(k1.abs()).unwrap();

        // k2
        let k2 = -b2;
        let k2_abs = BigUint::try_from(k2.abs()).unwrap();

        (
            (k1.sign() == Sign::Plus, k1_abs.into()),
            (k2.sign() == Sign::Plus, k2_abs.into()),
        )
    }

    fn endomorphism(p: &Projective<Self>) -> Projective<Self>;

    fn endomorphism_affine(p: &Affine<Self>) -> Affine<Self>;

    fn glv_mul_projective(p: Projective<Self>, k: Self::ScalarField) -> Projective<Self> {
        let ((sgn_k1, k1), (sgn_k2, k2)) = Self::scalar_decomposition(k);
        let b1 = if sgn_k1 { p } else { -p };
        let b2 = if sgn_k2 {
            Self::endomorphism(&p)
        } else {
            -Self::endomorphism(&p)
        };
        glv_windowed_mul(b1, b2, k1, k2)
    }

    /// GLV scalar multiplication starting from an affine point.
    ///
    /// Note: this converts to projective and uses the 2-bit windowed table (projective additions),
    /// rather than mixed additions against affine table entries.
    fn glv_mul_affine(p: Affine<Self>, k: Self::ScalarField) -> Affine<Self> {
        Self::glv_mul_projective(p.into(), k).into_affine()
    }
}

/// Precompute the 15-point table for 2-bit windowed GLV.
///
/// Adapted from gnark-crypto's `mulGLV` (Apache-2.0, Copyright Consensys Software Inc.):
/// <https://github.com/ConsenSys/gnark-crypto/blob/v0.19.0/ecc/bls12-381/g1.go#L620>
/// implementing the GLV method (<https://www.iacr.org/archive/crypto2001/21390189.pdf>).
///
/// After scalar decomposition, multiplication is `k1*b1 + k2*b2`. Each loop step reads two bits
/// from each half-length scalar, giving digits `c1`, `c2` in `0..=3`. The point to add is
/// `c1*b1 + c2*b2`; the two preceding doublings account for advancing two bits on each leg.
///
/// There are `4*4` digit pairs, but `(c1, c2) = (0, 0)` adds nothing, so we store the other 15.
/// Pack digits as `idx = c2*4 + c1` (0..16) and use `table[idx - 1]` when `idx != 0`.
/// Example: `table[0]=b1`, `table[1]=2*b1`, `table[2]=3*b1`, `table[3]=b2`, `table[4]=b1+b2`,
/// …, `table[14]=3*b1 + 3*b2`.
#[inline]
fn glv_precompute_table<P: GLVConfig>(b1: Projective<P>, b2: Projective<P>) -> [Projective<P>; 15] {
    let b1_2 = b1.double();
    let b1_3 = b1_2 + b1;
    let b2_2 = b2.double();
    let b2_3 = b2_2 + b2;
    [
        b1,
        b1_2,
        b1_3,
        b2,
        b1 + b2,
        b1_2 + b2,
        b1_3 + b2,
        b2_2,
        b1 + b2_2,
        b1_2 + b2_2,
        b1_3 + b2_2,
        b2_3,
        b1 + b2_3,
        b1_2 + b2_3,
        b1_3 + b2_3,
    ]
}

/// 2-bit windowed scan for `k1*b1 + k2*b2` (bases must already include sign fixes).
fn glv_windowed_mul<P: GLVConfig>(
    b1: Projective<P>,
    b2: Projective<P>,
    k1: P::ScalarField,
    k2: P::ScalarField,
) -> Projective<P> {
    let table = glv_precompute_table(b1, b2);

    let k1_bi = k1.into_bigint();
    let k2_bi = k2.into_bigint();
    let limbs1 = k1_bi.as_ref();
    let limbs2 = k2_bi.as_ref();
    // `BitIteratorBE::new` / `into_bigint` always yield exactly `64 * NUM_LIMBS` bits for a
    // given `ScalarField`, so both scalars share the same (even) bit length.
    debug_assert_eq!(limbs1.len(), limbs2.len());
    let nbits = limbs1.len() * 64;

    let mut res = Projective::zero();
    let mut started = false;
    for chunk_idx in 0..(nbits / 2) {
        let c1 = glv_two_bit_digit(limbs1, chunk_idx);
        let c2 = glv_two_bit_digit(limbs2, chunk_idx);
        let idx = (c2 as usize) * 4 + (c1 as usize);
        if started {
            res.double_in_place();
            res.double_in_place();
            if idx != 0 {
                res += table[idx - 1];
            }
        } else if idx != 0 {
            started = true;
            res = table[idx - 1];
        }
    }
    res
}

/// Extract the `chunk_idx`-th 2-bit window from a big-endian limb encoding.
///
/// `chunk_idx = 0` is the most-significant pair of bits across `limbs`. The total bit length
/// `64 * limbs.len()` is always even, so every window is fully contained in a single limb.
#[inline]
fn glv_two_bit_digit(limbs: &[u64], chunk_idx: usize) -> u8 {
    let bit_from_msb = chunk_idx * 2;
    let limb = limbs[limbs.len() - 1 - bit_from_msb / 64];
    ((limb >> (62 - (bit_from_msb % 64))) & 3) as u8
}

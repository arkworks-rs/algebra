use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    AdditiveGroup, CurveGroup,
};
use ark_ff::{BigInteger, PrimeField, Zero};
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
        glv_wnaf_mul(b1, b2, k1, k2)
    }

    /// GLV scalar multiplication starting from an affine point.
    ///
    /// Note: this converts to projective and uses projective additions against the wNAF tables,
    /// rather than mixed additions against affine table entries.
    fn glv_mul_affine(p: Affine<Self>, k: Self::ScalarField) -> Affine<Self> {
        Self::glv_mul_projective(p.into(), k).into_affine()
    }
}

/// Width of the signed-digit windows used by [`glv_wnaf_mul`].
///
/// Recoded digits are odd and lie in `-(2^(W-1) - 1)..=2^(W-1) - 1`, so each base needs a table
/// of `2^(W-2)` odd multiples. Recoding an `n`-bit half-scalar at width `W` leaves about
/// `n / (W + 1)` non-zero digits, against `n * (1 - 4^-2) / 2` for the 2-bit joint window this
/// replaces. Counting table plus scan over real decompositions on BLS12-381, BN254 and
/// BLS12-377 G1, the saving against that window in base-field multiplications is -2.1% at
/// `W = 3`, -9.5% at `W = 4`, -10.0% at `W = 5` and -1.9% at `W = 6`. `W = 5` is the optimum,
/// though `W = 4` comes within half a percent of it using half the table.
const GLV_WNAF_WIDTH: u32 = 5;

/// `GLV_WNAF_WIDTH` is bounded by the `i8` that [`glv_wnaf_digits`] packs its digits into. The
/// binding constraint is the sign correction there: at `W = 7`, `1i8 << 7` is `-128`, so
/// `low - (1 << W)` overflows. Release builds happen to survive it, because the wrap is
/// congruent mod 256 and lands on the right residue, but any debug or test build panics on
/// the overflow. Six is the widest window this recoding can express, and nothing above five
/// is competitive anyway.
const _: () = assert!(
    GLV_WNAF_WIDTH >= 2 && (1i64 << GLV_WNAF_WIDTH) <= i8::MAX as i64,
    "GLV_WNAF_WIDTH must lie in 2..=6 so the width-sized constants fit in `i8`"
);

/// Number of odd multiples precomputed per base: `1, 3, 5, ..., 2^(W-1) - 1`.
const GLV_WNAF_TABLE_SIZE: usize = 1 << (GLV_WNAF_WIDTH - 2);

/// Capacity of the stack buffer holding one recoded half-scalar.
///
/// Recoding an `n`-bit value yields at most `n + 1` digits, and `scalar_decomposition` bounds
/// each half-scalar by `ceil(ScalarField::MODULUS_BIT_SIZE / 2)` bits. This bound holds a
/// *full-width* recoding for any scalar field up to 1023 bits, so it is reached only by a field
/// far wider than any in use (the widest, MNT4/6-753, is 753 bits) and only then via a
/// `GLVConfig` whose decomposition is not actually halving. Overrunning it is a bounds-check
/// panic in `glv_wnaf_digits`, not silent corruption.
const GLV_WNAF_MAX_DIGITS: usize = 1024;

/// Precompute `[b, 3*b, 5*b, ..., (2^(W-1) - 1)*b]`.
///
/// One doubling plus `2^(W-2) - 1` additions: `t[0] = b` and `t[i] = t[i - 1] + 2*b`.
#[inline]
fn glv_odd_multiples<P: GLVConfig>(b: Projective<P>) -> [Projective<P>; GLV_WNAF_TABLE_SIZE] {
    let b_2 = b.double();
    let mut table = [b; GLV_WNAF_TABLE_SIZE];
    for i in 1..GLV_WNAF_TABLE_SIZE {
        table[i] = table[i - 1] + b_2;
    }
    table
}

/// Recode `k` into width-`GLV_WNAF_WIDTH` non-adjacent form, writing digits into `digits`
/// least-significant first and returning how many were written.
///
/// Every digit is either zero or odd with absolute value below `2^(W-1)`, and any two non-zero
/// digits are at least `W` positions apart. A non-zero digit `d` selects table entry
/// `|d| / 2`, added when `d > 0` and subtracted when `d < 0`.
fn glv_wnaf_digits<F: PrimeField>(k: F, digits: &mut [i8; GLV_WNAF_MAX_DIGITS]) -> usize {
    // The recoding consumes `k` from the bottom up: at each odd residue it subtracts the signed
    // remainder mod `2^W`, which clears the low `W` bits and forces the next `W - 1` digits to
    // zero, then shifts right by one.
    let mut e = k.into_bigint();
    let mut len = 0;
    while !e.is_zero() {
        let digit = if e.is_odd() {
            // Signed remainder mod `2^W`, i.e. the representative in `-2^(W-1)..2^(W-1)`. It is
            // odd because `e` is, so it never attains the even bound `-2^(W-1)`.
            let low = (e.as_ref()[0] & ((1 << GLV_WNAF_WIDTH) - 1)) as i8;
            let digit = if low >= (1 << (GLV_WNAF_WIDTH - 1)) {
                low - (1 << GLV_WNAF_WIDTH)
            } else {
                low
            };
            // `e -= digit`, which cannot wrap: `e` is at least 1, and a negative digit only adds.
            if digit >= 0 {
                e.sub_with_borrow(&F::BigInt::from(digit as u64));
            } else {
                e.add_with_carry(&F::BigInt::from(digit.unsigned_abs() as u64));
            }
            digit
        } else {
            0
        };
        digits[len] = digit;
        len += 1;
        e.div2();
    }
    len
}

/// Interleaved width-`GLV_WNAF_WIDTH` wNAF evaluation of `k1*b1 + k2*b2`.
///
/// The bases must already carry the sign fixes from `scalar_decomposition`, so `k1` and `k2` are
/// the non-negative half-scalars. Both are recoded independently, then scanned together from the
/// most significant digit: one doubling per position, and one table addition per non-zero digit
/// on either leg.
///
/// This is the scheme gnark-crypto's `mulGLV` uses (Apache-2.0, Copyright Consensys Software
/// Inc.): <https://github.com/Consensys/gnark-crypto/blob/v0.21.0/ecc/bls12-381/g1.go#L777>,
/// implementing the GLV method (<https://www.iacr.org/archive/crypto2001/21390189.pdf>).
fn glv_wnaf_mul<P: GLVConfig>(
    b1: Projective<P>,
    b2: Projective<P>,
    k1: P::ScalarField,
    k2: P::ScalarField,
) -> Projective<P> {
    let mut digits1 = [0i8; GLV_WNAF_MAX_DIGITS];
    let mut digits2 = [0i8; GLV_WNAF_MAX_DIGITS];
    let len1 = glv_wnaf_digits(k1, &mut digits1);
    let len2 = glv_wnaf_digits(k2, &mut digits2);

    let table1 = glv_odd_multiples(b1);
    let table2 = glv_odd_multiples(b2);

    let mut res = Projective::zero();
    // The two recodings generally differ in length; the shorter one reads as zero above its own
    // top digit, which `digits` already holds. Doubling `res` while it is still zero is a no-op,
    // so no separate "first non-zero digit" flag is needed.
    for i in (0..len1.max(len2)).rev() {
        res.double_in_place();
        for (digit, table) in [(digits1[i], &table1), (digits2[i], &table2)] {
            if digit > 0 {
                res += table[(digit >> 1) as usize];
            } else if digit < 0 {
                res -= table[(digit.unsigned_abs() >> 1) as usize];
            }
        }
    }
    res
}

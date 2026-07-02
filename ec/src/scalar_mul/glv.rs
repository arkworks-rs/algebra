use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    CurveGroup,
};
use ark_ff::{biginteger::arithmetic as fa, BigInteger, PrimeField};
use ark_std::{
    ops::{AddAssign, Neg, SubAssign},
    vec::Vec,
};
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed};

/// Precomputed constants that let a curve decompose a scalar without any `num_bigint` (heap)
/// arithmetic.
/// With `N = ScalarField::BigInt::NUM_LIMBS` and `M = 64 * (N + 2)`, the
/// rounding `round(k * |n_ij| / r)` is computed as `round(k * g / 2^M)` for a
/// precomputed `g = round(2^M * |n_ij| / r)`; rounding by `2^M` is a shift, so
/// no division is needed. The fields are:
/// - `g1 = round(2^M * |n22| / r)` and `g2 = round(2^M * |n12| / r)`, each as
///   `N + 1` little-endian limbs (the `n_ij` are the [`GLVConfig::SCALAR_DECOMP_COEFFS`]).
/// - `a12 = |n12|` and `a22 = |n22|` as scalar field elements. These are duplicated from
///    [`GLVConfig::SCALAR_DECOMP_COEFFS`] to avoid multiplication during conversion
/// - `negate_k2` is `true` when `sign(n12) * sign(n22) == -1`.
///
/// These can be generated from `SCALAR_DECOMP_COEFFS` by `scripts/glv_fast_decomp.py`.
#[derive(Clone, Copy)]
pub struct GLVFastDecomp<F: PrimeField> {
    pub g1: &'static [u64],
    pub g2: &'static [u64],
    pub a12: F,
    pub a22: F,
    pub negate_k2: bool,
}

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

    /// Optional precomputed constants enabling allocation-free scalar
    /// decomposition. When `Some`, [`Self::scalar_decomposition`] uses
    /// [`fast_scalar_decomposition`] instead of the `num_bigint` path; when
    /// `None` the curve keeps the generic (slower) decomposition.
    const FAST_DECOMP: Option<GLVFastDecomp<Self::ScalarField>> = None;

    /// Decomposes a scalar s into k1, k2, s.t. s = k1 + lambda k2. Dispatches to
    /// [`fast_scalar_decomposition`] when [`Self::FAST_DECOMP`] is set, otherwise
    /// the generic [`generic_scalar_decomposition`].
    fn scalar_decomposition(
        k: Self::ScalarField,
    ) -> ((bool, Self::ScalarField), (bool, Self::ScalarField)) {
        match Self::FAST_DECOMP {
            Some(fd) => fast_scalar_decomposition::<Self>(k, &fd),
            None => generic_scalar_decomposition::<Self>(k),
        }
    }

    fn endomorphism(p: &Projective<Self>) -> Projective<Self>;

    fn endomorphism_affine(p: &Affine<Self>) -> Affine<Self>;

    fn glv_mul_projective(p: Projective<Self>, k: Self::ScalarField) -> Projective<Self> {
        let mut b1 = p;
        let mut b2 = Self::endomorphism(&p);

        let ((sgn_k1, k1), (sgn_k2, k2)) = Self::scalar_decomposition(k);

        if !sgn_k1 {
            b1 = -b1;
        }
        if !sgn_k2 {
            b2 = -b2;
        }

        binary_scalar_mul_jsf(b1, k1, b2, k2)
    }

    fn glv_mul_affine(p: Affine<Self>, k: Self::ScalarField) -> Affine<Self> {
        let mut b1 = p;
        let mut b2 = Self::endomorphism_affine(&p);

        let ((sgn_k1, k1), (sgn_k2, k2)) = Self::scalar_decomposition(k);

        if !sgn_k1 {
            b1 = -b1;
        }
        if !sgn_k2 {
            b2 = -b2;
        }

        binary_scalar_mul_jsf_affine(b1, k1, b2, k2).into_affine()
    }
}

/// Computes `round((k * g) / 2^(64 * shift_limbs))`, rounding up, and returns
/// it as a scalar field element. `k` is the little-endian canonical limbs of the scalar and
/// `g` is a precomputed multiplier; both are read as unsigned integers. The
/// result is small (below `2^128`)
fn mul_shift_round<F: PrimeField>(k: &[u64], g: &[u64], shift_limbs: usize) -> F {
    // Accumulator wide enough for the product of `k` and `g` and one more limb
    let mut prod = [0u64; 16];
    debug_assert!(k.len() + g.len() < prod.len());
    for (i, &ki) in k.iter().enumerate() {
        let mut carry = 0u64;
        for (j, &gj) in g.iter().enumerate() {
            prod[i + j] = fa::mac_with_carry(prod[i + j], ki, gj, &mut carry);
        }
        prod[i + g.len()] = carry;
    }

    // `floor((prod + 2^(64*shift_limbs - 1)) / 2^(64*shift_limbs))`
    let mut res = <F::BigInt as Default>::default();
    let mut carry = prod[shift_limbs - 1] >> 63;
    for (t, o) in res.as_mut().iter_mut().enumerate() {
        let (v, c) = prod[shift_limbs + t].overflowing_add(carry);
        *o = v;
        carry = c as u64;
    }
    debug_assert_eq!(carry, 0);
    F::from_bigint(res).expect("should be smaller than the modulus")
}

/// Splits the canonical representative of `x` into `(is_non_negative, magnitude)`.
/// Values up to `(r-1)/2` are treated as non-negative; the rest are negative,
/// and for those `-x` has canonical representative `r - rep(x)`, which is exactly
/// the magnitude.
fn sign_and_magnitude<F: PrimeField>(x: F) -> (bool, F) {
    if x.into_bigint() <= F::MODULUS_MINUS_ONE_DIV_TWO {
        (true, x)
    } else {
        (false, -x)
    }
}

/// Allocation-free GLV scalar decomposition using [`GLVFastDecomp`].
///
/// The two roundings `c1 = round(k * a22 / r)` and `c2 = round(k * a12 / r)` are
/// done with [`mul_shift_round`]; then `k2 = +/-(c2*a22 - c1*a12)` and
/// `k1 = k - lambda*k2` are evaluated in the scalar field. Defining `k1` this way
/// makes `k1 + lambda*k2 == k` hold by construction, so a rounding error of at
/// most one only affects how short `k1, k2` are, never the correctness of the
/// identity.
///
/// `mul_shift_round` ties up, so on a half-way boundary this can return a
/// `(k1, k2)` one unit from [`generic_scalar_decomposition`] (which rounds
/// toward zero). Both are valid and short; only the exact pair differs.
pub fn fast_scalar_decomposition<P: GLVConfig>(
    k: P::ScalarField,
    precomp: &GLVFastDecomp<P::ScalarField>,
) -> ((bool, P::ScalarField), (bool, P::ScalarField)) {
    let num_limbs = <<P::ScalarField as PrimeField>::BigInt as BigInteger>::NUM_LIMBS;
    // same as python script
    let shift = num_limbs + 2;
    debug_assert_eq!(precomp.g1.len(), num_limbs + 1);
    debug_assert_eq!(precomp.g2.len(), num_limbs + 1);

    let k_bigint = k.into_bigint();
    let k_limbs = k_bigint.as_ref();

    // round(k * a22 / modulus)
    let c1 = mul_shift_round::<P::ScalarField>(k_limbs, precomp.g1, shift);
    // round(k * a12 / modulus)
    let c2 = mul_shift_round::<P::ScalarField>(k_limbs, precomp.g2, shift);

    let mut k2 = c2 * precomp.a22 - c1 * precomp.a12;
    if precomp.negate_k2 {
        k2 = -k2;
    }
    let k1 = k - P::LAMBDA * k2;

    (sign_and_magnitude(k1), sign_and_magnitude(k2))
}

/// Generic GLV scalar decomposition
pub fn generic_scalar_decomposition<P: GLVConfig>(
    k: P::ScalarField,
) -> ((bool, P::ScalarField), (bool, P::ScalarField)) {
    let scalar: BigInt = k.into_bigint().into().into();

    let [n11, n12, n21, n22] = P::SCALAR_DECOMP_COEFFS.map(|x| {
        let sign = if x.0 { Sign::Plus } else { Sign::Minus };
        BigInt::from_biguint(sign, x.1.into())
    });

    let r = BigInt::from(P::ScalarField::MODULUS.into());

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

/// Computes the joint sparse form (JSF) of two non-negative integers, given as
/// little-endian `u64` limbs.
/// The result is a sequence of signed digit pairs `(u1, u2)`, each in `{-1, 0, 1}`, ordered from
/// most significant to least significant, such that `k1 = \sum_i{u1_i * 2^i}` and `k2 = \sum_i{u2_i * 2^i}`.
/// The JSF is the joint signed-binary representation of minimal weight: of any three consecutive
/// positions at least one is `(0, 0)`, so on average only about half the positions are nonzero
/// The returned sequence never starts with `(0, 0)` and is at most one digit longer than the bit length
/// of `max(k1, k2)`.
/// Reference: Taken from Algorithm 3.50 of the book [Guide to Elliptic Curve Cryptography](http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf)
pub fn joint_sparse_form(k1: &[u64], k2: &[u64]) -> Vec<(i8, i8)> {
    let len = k1.len().max(k2.len());
    let mut a = k1.to_vec();
    let mut b = k2.to_vec();
    // Add one extra limb for carry: a `-1` digit increments the value by 1 before halving,
    // which can carry out of a full-width top limb (top bit set). The spare limb absorbs that
    // carry, so the encoding is correct for any input — not only values with a clear top bit.
    a.resize(len + 1, 0);
    b.resize(len + 1, 0);

    // The JSF of an L-bit pair has at most L + 1 digits
    let mut digits = Vec::with_capacity(len * 64 + 1);
    while !limbs_is_zero(&a) || !limbs_is_zero(&b) {
        // The JSF in the book uses d for carry but here it's handled in limbs_sub_signed_then_halve
        let a_low = a[0];
        let b_low = b[0];

        let mut u1 = 0i8;
        // If odd
        if (a_low & 1) == 1 {
            // a mod 4 is 1 or 3, mapping to +1 or -1.
            u1 = 2 - (a_low & 3) as i8;
            // Flip the sign so that the next position can become a joint zero.
            if matches!(a_low & 7, 3 | 5) && (b_low & 3) == 2 {
                u1 = -u1;
            }
        }

        // If odd
        let mut u2 = 0i8;
        if (b_low & 1) == 1 {
            u2 = 2 - (b_low & 3) as i8;
            if matches!(b_low & 7, 3 | 5) && (a_low & 3) == 2 {
                u2 = -u2;
            }
        }

        digits.push((u1, u2));
        // a = (a - u1) / 2, b = (b - u2) / 2. `a - u1` is even (a is odd whenever u1 != 0), so the
        // halving is exact.
        limbs_sub_signed_then_halve(&mut a, u1);
        limbs_sub_signed_then_halve(&mut b, u2);
    }

    digits.reverse();
    digits
}

/// Computes `b1 * k1 + b2 * k2` using the joint sparse form of `(k1, k2)`.
///
/// Compared to [`binary_scalar_mul_shamir`] (Shamir's trick over the plain bits) this
/// does the same number of doublings but fewer additions, because the JSF has
/// about half as many nonzero positions. It precomputes `b1 + b2` and `b1 - b2`;
/// the four other table entries (the negations) are free for these groups.
///
/// When the bases are available in affine form, prefer
/// [`binary_scalar_mul_jsf_affine`], which uses cheaper mixed additions for the
/// single-base digits.
pub fn binary_scalar_mul_jsf<G: SWCurveConfig>(
    b1: Projective<G>,
    k1: G::ScalarField,
    b2: Projective<G>,
    k2: G::ScalarField,
) -> Projective<G> {
    let sum = b1 + b2;
    let diff = b1 - b2;
    let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());
    // Projective bases: the single-base digits use full projective additions.
    jsf_fold(b1, b2, sum, diff, digits)
}

/// Computes `b1 * k1 + b2 * k2`. Identical to [`binary_scalar_mul_jsf`] but for affine points
pub fn binary_scalar_mul_jsf_affine<G: SWCurveConfig>(
    b1: Affine<G>,
    k1: G::ScalarField,
    b2: Affine<G>,
    k2: G::ScalarField,
) -> Projective<G> {
    let sum = b1 + b2; // Affine + Affine -> Projective
    let diff = b1 + (-b2);
    let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());
    // Affine bases: the single-base digits use mixed (projective += affine) additions.
    jsf_fold(b1, b2, sum, diff, digits)
}

/// Shared double-and-add core for the JSF double-scalar multiplication, driven by the precomputed
/// MSB-first `digits` and the `sum = b1 + b2` / `diff = b1 - b2` table entries.
fn jsf_fold<G, B>(b1: B, b2: B, sum: G, diff: G, digits: Vec<(i8, i8)>) -> G
where
    G: CurveGroup + AddAssign<B> + SubAssign<B>,
    B: Copy,
{
    // Apply one JSF digit to the accumulator.
    let apply = |res: &mut G, (u1, u2): (i8, i8)| match (u1, u2) {
        (1, 0) => *res += b1,
        (-1, 0) => *res -= b1,
        (0, 1) => *res += b2,
        (0, -1) => *res -= b2,
        (1, 1) => *res += sum,
        (-1, -1) => *res -= sum,
        (1, -1) => *res += diff,
        (-1, 1) => *res -= diff,
        // (0, 0) contributes nothing; it never leads the sequence (see `joint_sparse_form`).
        _ => {},
    };

    let mut digits = digits.into_iter();
    let mut res = match digits.next() {
        // The digit sequence never starts with (0, 0)
        Some(first) => {
            let mut res = G::ZERO;
            apply(&mut res, first);
            res
        },
        // Both scalars are zero.
        None => return G::ZERO,
    };
    for digit in digits {
        res.double_in_place();
        apply(&mut res, digit);
    }
    res
}

/// Returns `true` if every limb is zero.
fn limbs_is_zero(x: &[u64]) -> bool {
    x.iter().all(|&l| l == 0)
}

/// Sets `x = (x - d) / 2` for `d` in `{-1, 0, 1}`, treating `x` as a
/// little-endian unsigned integer. `x` is odd whenever `d != 0`, so the result
/// is exact.
fn limbs_sub_signed_then_halve(x: &mut [u64], d: i8) {
    match d {
        1 => {
            // x -= 1
            let mut borrow = 1u64;
            for limb in x.iter_mut() {
                let (v, b) = limb.overflowing_sub(borrow);
                *limb = v;
                borrow = b as u64;
            }
            // `x` was odd (and so >= 1), so subtracting 1 cannot underflow.
            debug_assert_eq!(borrow, 0, "subtracting 1 underflowed the limb array");
        },
        -1 => {
            // x += 1
            let mut carry = 1u64;
            for limb in x.iter_mut() {
                let (v, c) = limb.overflowing_add(carry);
                *limb = v;
                carry = c as u64;
            }
            // `joint_sparse_form` adds an spare top limb, so this cannot carry out.
            debug_assert_eq!(carry, 0, "increment carried out of the limb array");
        },
        _ => {},
    }

    // x >>= 1
    let mut carry = 0u64;
    for limb in x.iter_mut().rev() {
        let new_carry = *limb << 63;
        *limb = (*limb >> 1) | carry;
        carry = new_carry;
    }
}

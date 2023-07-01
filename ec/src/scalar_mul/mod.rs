pub mod glv;
pub mod wnaf;

pub mod fixed_base;
pub mod variable_base;

use crate::{
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    PrimeGroup,
};
use ark_ff::{AdditiveGroup, Zero};
use ark_std::{
    ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign},
    vec::Vec,
};

/// The result of this function is only approximately `ln(a)`
/// [`Explanation of usage`]
///
/// [`Explanation of usage`]: https://github.com/scipr-lab/zexe/issues/79#issue-556220473
fn ln_without_floats(a: usize) -> usize {
    // log2(a) * ln(2)
    (ark_std::log2(a) * 69 / 100) as usize
}

/// Standard double-and-add method for multiplication by a scalar.
#[inline(always)]
pub fn sw_double_and_add_affine<P: SWCurveConfig>(
    base: &Affine<P>,
    scalar: impl AsRef<[u64]>,
) -> Projective<P> {
    let mut res = Projective::<P>::zero();
    for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
        res.double_in_place();
        if b {
            res += base
        }
    }

    res
}

/// Standard double-and-add method for multiplication by a scalar.
#[inline(always)]
pub fn sw_double_and_add_projective<P: SWCurveConfig>(
    base: &Projective<P>,
    scalar: impl AsRef<[u64]>,
) -> Projective<P> {
    let mut res = Projective::<P>::zero();
    for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
        res.double_in_place();
        if b {
            res += base
        }
    }

    res
}

pub trait ScalarMul:
    PrimeGroup
    + Add<Self::MulBase, Output = Self>
    + AddAssign<Self::MulBase>
    + for<'a> Add<&'a Self::MulBase, Output = Self>
    + for<'a> AddAssign<&'a Self::MulBase>
    + Sub<Self::MulBase, Output = Self>
    + SubAssign<Self::MulBase>
    + for<'a> Sub<&'a Self::MulBase, Output = Self>
    + for<'a> SubAssign<&'a Self::MulBase>
    + From<Self::MulBase>
{
    type MulBase: Send
        + Sync
        + Copy
        + Eq
        + core::hash::Hash
        + Mul<Self::ScalarField, Output = Self>
        + for<'a> Mul<&'a Self::ScalarField, Output = Self>
        + Neg<Output = Self::MulBase>;

    const NEGATION_IS_CHEAP: bool;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase>;
}

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused, future_incompatible, nonstandard_style, rust_2018_idioms)]
#![forbid(unsafe_code)]
#![allow(
    clippy::op_ref,
    clippy::suspicious_op_assign_impl,
    clippy::many_single_char_names
)]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate ark_std;

use ark_ff::{
    fields::{Field, PrimeField, SquareRootField},
    BitIteratorBE, UniformRand,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    vec::Vec,
};
use num_traits::Zero;
use zeroize::Zeroize;

pub mod models;
pub use self::models::*;

pub mod pairing;
pub use self::pairing::*;

pub mod msm;

pub mod wnaf;

/// Represents (elements of) a group of prime order `r`.
pub trait Group:
    'static
    + Sized
    + Eq
    + Copy
    + Default
    + Send
    + Sync
    + Hash
    + Debug
    + Display
    + Zero
    + UniformRand
    + Neg<Output = Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
    + MulAssign<<Self as Group>::ScalarField>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + core::iter::Sum<Self>
    + for<'a> core::iter::Sum<&'a Self>
    + From<<Self as Group>::NormalForm>
    + Into<<Self as Group>::NormalForm>
    + Zeroize
{
    /// The scalar field `F_r`, where `r` is the order of this group.
    type ScalarField: PrimeField + SquareRootField;

    /// The normalized, normalized representation of elements of this group.
    /// For example, in elliptic curve groups, this can be defined to be the affine representation of curve points.
    type NormalForm: GroupNormalForm<G = Self>;

    /// Returns a fixed generator of this group.
    #[must_use]
    fn generator() -> Self::NormalForm;

    /// Converts `self` into the normalized representation [`Self::NormalForm`].
    fn normalize(&self) -> Self::NormalForm {
        (*self).into()
    }

    /// Constructs [`Self`] from an element of type [`Self::NormalForm`].
    fn from_normal(other: Self::NormalForm) -> Self {
        other.into()
    }

    /// Canonicalize a batch of group elements into their normalized representation.
    fn batch_normalize(v: &[Self]) -> Vec<Self::NormalForm>;

    /// Doubles `self`.
    #[must_use]
    fn double(&self) -> Self {
        let mut copy = *self;
        copy.double_in_place();
        copy
    }

    /// Double `self` in place.
    fn double_in_place(&mut self) -> &mut Self;

    /// Compute `self + other`, where `other` has type [`Self::NormalForm`].
    /// This method is useful for elliptic curve groups, where it can
    /// be implemented via fast(er) mixed addition algorithms.
    fn add_normal(mut self, other: &Self::NormalForm) -> Self {
        self.add_normal_in_place(other);
        self
    }

    /// Set `self` to be `self + other`, where `other` has type `Self::CanonicalRepr.
    /// This method is useful for elliptic curve groups, where it can
    /// be implemented via fast(er) mixed addition algorithms.
    fn add_normal_in_place(&mut self, other: &Self::NormalForm) {
        *self += &Self::from(*other)
    }

    /// Compute `other * self`, where `other` is any type that can be converted
    /// into `<Self::ScalarField>::BigInt`. This includes `Self::ScalarField`.
    fn mul(&self, other: impl Into<<Self::ScalarField as PrimeField>::BigInt>) -> Self {
        self.mul_bits_be(ark_ff::BitIteratorBE::without_leading_zeros(other.into()))
    }

    /// Computes `other * self`, where `other` is a *big-endian*
    /// bit representation of some integer.
    fn mul_bits_be(&self, other: impl Iterator<Item = bool>) -> Self {
        let mut res = Self::zero();
        for b in other.skip_while(|b| !b) {
            // skip leading zeros
            res.double_in_place();
            if b {
                res += self;
            }
        }
        res
    }
}

pub trait GroupNormalForm:
    'static
    + Send
    + Sync
    + Copy
    + Eq
    + Debug
    + Display
    + From<Self::G>
    + Into<Self::G>
    + UniformRand
    + Neg<Output = Self>
    + core::iter::Sum<Self::G>
    + for<'a> core::iter::Sum<&'a Self::G>
    + CanonicalSerialize
    + CanonicalDeserialize
{
    type G: Group<NormalForm = Self>;
    /// Compute `other * self`, where `other` is any type that can be converted
    /// into `<Self::ScalarField>::BigInt`. This includes `Self::ScalarField`.
    fn mul(
        &self,
        other: impl Into<<<Self::G as Group>::ScalarField as PrimeField>::BigInt>,
    ) -> Self::G {
        self.mul_bits_be(ark_ff::BitIteratorBE::without_leading_zeros(other.into()))
    }

    /// Computes `other * self`, where `other` is a *big-endian*
    /// bit representation of some integer.
    fn mul_bits_be(&self, other: impl Iterator<Item = bool>) -> Self::G {
        let mut res = Self::G::zero();
        for b in other.skip_while(|b| !b) {
            // skip leading zeros
            res.double_in_place();
            if b {
                res.add_normal_in_place(self);
            }
        }
        res
    }
}

/// The additive [`Group`] defined by points on an elliptic curve.
/// Defines additional associated types and constants that are
/// useful when working with curves.
pub trait CurveGroup: Group {
    /// The cofactor of this elliptic curve.
    const COFACTOR: &'static [u64];

    /// The value `(Self::COFACTOR)^(-1)` in `Self::ScalarField`.
    const COFACTOR_INVERSE: Self::ScalarField;

    /// The base field that this elliptic curve is defined over.
    /// Unlike `Self::ScalarField`, this does not have to be a prime field.
    type BaseField: Field;

    fn mul_by_cofactor(e: &Self::NormalForm) -> Self {
        let cofactor = BitIteratorBE::without_leading_zeros(Self::COFACTOR);
        e.mul_bits_be(cofactor)
    }

    fn mul_by_cofactor_inv(e: &Self::NormalForm) -> Self {
        let cofactor_inv = BitIteratorBE::without_leading_zeros(Self::COFACTOR_INVERSE.into_repr());
        e.mul_bits_be(cofactor_inv)
    }
}

/// Preprocess a G1 element for use in a pairing.
pub fn prepare_g1<P: Pairing>(g: impl Into<P::G1>) -> P::G1Prepared {
    let g: P::G1 = g.into();
    P::G1Prepared::from(g)
}

/// Preprocess a G2 element for use in a pairing.
pub fn prepare_g2<P: Pairing>(g: impl Into<P::G2>) -> P::G2Prepared {
    let g: P::G2 = g.into();
    P::G2Prepared::from(g)
}

pub trait CurveCycle
where
    Self::E1: MulAssign<<Self::E2 as CurveGroup>::BaseField>,
    Self::E2: MulAssign<<Self::E1 as CurveGroup>::BaseField>,
{
    type E1: CurveGroup<
        BaseField = <Self::E2 as Group>::ScalarField,
        ScalarField = <Self::E2 as CurveGroup>::BaseField,
    >;
    type E2: CurveGroup;
}

pub trait PairingFriendlyCycle: CurveCycle {
    type Engine1: Pairing<G1 = Self::E1, ScalarField = <Self::E1 as Group>::ScalarField>;

    type Engine2: Pairing<G1 = Self::E2, ScalarField = <Self::E2 as Group>::ScalarField>;
}

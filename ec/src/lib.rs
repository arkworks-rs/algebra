#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]
#![allow(
    clippy::op_ref,
    clippy::suspicious_op_assign_impl,
    clippy::many_single_char_names
)]
#![doc = include_str!("../README.md")]

#[macro_use]
extern crate ark_std;

use ark_ff::{
    fields::{Field, PrimeField},
    UniformRand,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    vec::*,
};
pub use scalar_mul::{variable_base::VariableBaseMSM, ScalarMul};
use zeroize::Zeroize;

pub use ark_ff::AdditiveGroup;

pub mod models;
pub use self::models::*;

pub mod scalar_mul;

/// Provides a `HashToCurve` trait and implementations of this trait via
/// different hashing strategies.
pub mod hashing;

pub mod pairing;

/// Represents (elements of) a group of prime order `r`.
pub trait PrimeGroup: AdditiveGroup<Scalar = Self::ScalarField> {
    /// The scalar field `F_r`, where `r` is the order of this group.
    type ScalarField: PrimeField;

    /// Returns a fixed generator of this group.
    #[must_use]
    fn generator() -> Self;

    /// Performs scalar multiplication of this element.
    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self;

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

/// An opaque representation of an elliptic curve group element that is suitable
/// for efficient group arithmetic.
///
/// The point is guaranteed to be in the correct prime order subgroup.
pub trait CurveGroup:
    PrimeGroup
    + Add<Self::Affine, Output = Self>
    + AddAssign<Self::Affine>
    + Sub<Self::Affine, Output = Self>
    + SubAssign<Self::Affine>
    + VariableBaseMSM
    + ScalarMul<MulBase = Self::Affine>
    + From<Self::Affine>
    + Into<Self::Affine>
    + core::iter::Sum<Self::Affine>
    + for<'a> core::iter::Sum<&'a Self::Affine>
{
    type Config: CurveConfig<ScalarField = Self::ScalarField, BaseField = Self::BaseField>;
    /// The field over which this curve is defined.
    type BaseField: Field;
    /// The affine representation of this element.
    type Affine: AffineRepr<
            Config = Self::Config,
            Group = Self,
            ScalarField = Self::ScalarField,
            BaseField = Self::BaseField,
        > + From<Self>
        + Into<Self>;

    /// Type representing an element of the full elliptic curve group, not just the
    /// prime order subgroup.
    type FullGroup;

    /// Normalizes a slice of group elements into affine.
    #[must_use]
    fn normalize_batch(v: &[Self]) -> Vec<Self::Affine>;

    /// Converts `self` into the affine representation.
    fn into_affine(self) -> Self::Affine {
        self.into()
    }
}

/// The canonical representation of an elliptic curve group element.
/// This should represent the affine coordinates of the point corresponding
/// to this group element.
///
/// The point is guaranteed to be in the correct prime order subgroup.
pub trait AffineRepr:
    Eq
    + 'static
    + Sized
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Clone
    + Default
    + UniformRand
    + Send
    + Sync
    + Hash
    + Debug
    + Display
    + Zeroize
    + Neg
    + From<<Self as AffineRepr>::Group>
    + Into<<Self as AffineRepr>::Group>
    + Add<Self, Output = Self::Group>
    + for<'a> Add<&'a Self, Output = Self::Group>
    + Add<Self::Group, Output = Self::Group>
    + for<'a> Add<&'a Self::Group, Output = Self::Group>
    + Sub<Self, Output = Self::Group>
    + for<'a> Sub<&'a Self, Output = Self::Group>
    + Sub<Self::Group, Output = Self::Group>
    + for<'a> Sub<&'a Self::Group, Output = Self::Group>
    + Mul<Self::ScalarField, Output = Self::Group>
    + for<'a> Mul<&'a Self::ScalarField, Output = Self::Group>
{
    type Config: CurveConfig<ScalarField = Self::ScalarField, BaseField = Self::BaseField>;
    type ScalarField: PrimeField + Into<<Self::ScalarField as PrimeField>::BigInt>;
    /// The finite field over which this curve is defined.
    type BaseField: Field;

    /// The projective representation of points on this curve.
    type Group: CurveGroup<
            Config = Self::Config,
            Affine = Self,
            ScalarField = Self::ScalarField,
            BaseField = Self::BaseField,
        > + From<Self>
        + Into<Self>
        + MulAssign<Self::ScalarField>; // needed due to https://github.com/rust-lang/rust/issues/69640

    /// Returns the x and y coordinates of this affine point.
    fn xy(&self) -> Option<(Self::BaseField, Self::BaseField)>;

    /// Returns the x coordinate of this affine point.
    fn x(&self) -> Option<Self::BaseField> {
        self.xy().map(|(x, _)| x)
    }

    /// Returns the y coordinate of this affine point.
    fn y(&self) -> Option<Self::BaseField> {
        self.xy().map(|(_, y)| y)
    }

    /// Returns the point at infinity.
    fn zero() -> Self;

    /// Is `self` the point at infinity?
    fn is_zero(&self) -> bool {
        self.xy().is_none()
    }

    /// Returns a fixed generator of unknown exponent.
    #[must_use]
    fn generator() -> Self;

    /// Converts self into the projective representation.
    fn into_group(self) -> Self::Group {
        self.into()
    }

    /// Returns a group element if the set of bytes forms a valid group element,
    /// otherwise returns None. This function is primarily intended for sampling
    /// random group elements from a hash-function or RNG output.
    fn from_random_bytes(bytes: &[u8]) -> Option<Self>;

    /// Performs scalar multiplication of this element with mixed addition.
    #[must_use]
    fn mul_bigint(&self, by: impl AsRef<[u64]>) -> Self::Group;

    /// Performs cofactor clearing.
    /// The default method is simply to multiply by the cofactor.
    /// For some curve families more efficient methods exist.
    #[must_use]
    fn clear_cofactor(&self) -> Self;

    /// Multiplies this element by the cofactor and output the
    /// resulting projective element.
    #[must_use]
    fn mul_by_cofactor_to_group(&self) -> Self::Group;

    /// Multiplies this element by the cofactor.
    #[must_use]
    fn mul_by_cofactor(&self) -> Self {
        self.mul_by_cofactor_to_group().into()
    }

    /// Multiplies this element by the inverse of the cofactor in
    /// `Self::ScalarField`.
    #[must_use]
    fn mul_by_cofactor_inv(&self) -> Self {
        self.mul_bigint(Self::Config::COFACTOR_INV.into_bigint())
            .into()
    }
}

/// Wrapper trait representing a cycle of elliptic curves (E1, E2) such that
/// the base field of E1 is the scalar field of E2, and the scalar field of E1
/// is the base field of E2.
pub trait CurveCycle
where
    Self::E1: MulAssign<<Self::E2 as CurveGroup>::BaseField>,
    Self::E2: MulAssign<<Self::E1 as CurveGroup>::BaseField>,
{
    type E1: CurveGroup<
        BaseField = <Self::E2 as PrimeGroup>::ScalarField,
        ScalarField = <Self::E2 as CurveGroup>::BaseField,
    >;
    type E2: CurveGroup;
}

/// A cycle of curves where both curves are pairing-friendly.
pub trait PairingFriendlyCycle: CurveCycle {
    type Engine1: pairing::Pairing<
        G1 = Self::E1,
        G1Affine = <Self::E1 as CurveGroup>::Affine,
        ScalarField = <Self::E1 as PrimeGroup>::ScalarField,
    >;

    type Engine2: pairing::Pairing<
        G1 = Self::E2,
        G1Affine = <Self::E2 as CurveGroup>::Affine,
        ScalarField = <Self::E2 as PrimeGroup>::ScalarField,
    >;
}

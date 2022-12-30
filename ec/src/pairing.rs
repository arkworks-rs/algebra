use ark_ff::{CyclotomicMultSubgroup, Field, One, PrimeField};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::Borrow,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    io::{Read, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
    UniformRand, Zero,
};
use zeroize::Zeroize;

use crate::{AffineRepr, CurveGroup, Group, VariableBaseMSM};

/// Collection of types (mainly fields and curves) that together describe
/// how to compute a pairing over a pairing-friendly curve.
pub trait Pairing: Sized + 'static + Copy + Debug + Sync + Send + Eq {
    /// This is the base field of the G1 group and base prime field of G2.
    type BaseField: PrimeField;

    /// This is the scalar field of the G1/G2 groups.
    type ScalarField: PrimeField;

    /// An element in G1.
    type G1: CurveGroup<ScalarField = Self::ScalarField, Affine = Self::G1Affine>
        + From<Self::G1Affine>
        + Into<Self::G1Affine>
        // needed due to https://github.com/rust-lang/rust/issues/69640
        + MulAssign<Self::ScalarField>;

    type G1Affine: AffineRepr<Group = Self::G1, ScalarField = Self::ScalarField>
        + From<Self::G1>
        + Into<Self::G1>
        + Into<Self::G1Prepared>;

    /// A G1 element that has been preprocessed for use in a pairing.
    type G1Prepared: Default
        + Clone
        + Send
        + Sync
        + Debug
        + CanonicalSerialize
        + CanonicalDeserialize
        + for<'a> From<&'a Self::G1>
        + for<'a> From<&'a Self::G1Affine>
        + From<Self::G1>
        + From<Self::G1Affine>;

    /// An element of G2.
    type G2: CurveGroup<ScalarField = Self::ScalarField, Affine = Self::G2Affine>
        + From<Self::G2Affine>
        + Into<Self::G2Affine>
        // needed due to https://github.com/rust-lang/rust/issues/69640
        + MulAssign<Self::ScalarField>;

    /// The affine representation of an element in G2.
    type G2Affine: AffineRepr<Group = Self::G2, ScalarField = Self::ScalarField>
        + From<Self::G2>
        + Into<Self::G2>
        + Into<Self::G2Prepared>;

    /// A G2 element that has been preprocessed for use in a pairing.
    type G2Prepared: Default
        + Clone
        + Send
        + Sync
        + Debug
        + CanonicalSerialize
        + CanonicalDeserialize
        + for<'a> From<&'a Self::G2>
        + for<'a> From<&'a Self::G2Affine>
        + From<Self::G2>
        + From<Self::G2Affine>;

    /// The extension field that hosts the target group of the pairing.
    type TargetField: CyclotomicMultSubgroup;

    /// Computes the product of Miller loops for some number of (G1, G2) pairs.
    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self>;

    /// Computes the Miller loop over `a` and `b`.
    fn miller_loop(
        a: impl Into<Self::G1Prepared>,
        b: impl Into<Self::G2Prepared>,
    ) -> MillerLoopOutput<Self> {
        Self::multi_miller_loop([a], [b])
    }

    /// Performs final exponentiation of the result of a `Self::multi_miller_loop`.
    #[must_use]
    fn final_exponentiation(mlo: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>>;

    /// Computes a "product" of pairings.
    fn multi_pairing(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> PairingOutput<Self> {
        Self::final_exponentiation(Self::multi_miller_loop(a, b)).unwrap()
    }

    /// Performs multiple pairing operations
    fn pairing(
        p: impl Into<Self::G1Prepared>,
        q: impl Into<Self::G2Prepared>,
    ) -> PairingOutput<Self> {
        Self::multi_pairing([p], [q])
    }
}

/// Represents the target group of a pairing. This struct is a
/// wrapper around the field that the target group is embedded in.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Pairing"),
    Clone(bound = "P: Pairing"),
    Debug(bound = "P: Pairing"),
    PartialEq(bound = "P: Pairing"),
    Eq(bound = "P: Pairing"),
    PartialOrd(bound = "P: Pairing"),
    Ord(bound = "P: Pairing"),
    Default(bound = "P: Pairing"),
    Hash(bound = "P: Pairing")
)]
#[must_use]
pub struct PairingOutput<P: Pairing>(pub P::TargetField);

impl<P: Pairing> CanonicalSerialize for PairingOutput<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_with_mode(writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.0.serialized_size(compress)
    }
}

impl<P: Pairing> Valid for PairingOutput<P> {
    fn check(&self) -> Result<(), SerializationError> {
        if self.0.pow(P::ScalarField::characteristic()).is_one() {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl<P: Pairing> CanonicalDeserialize for PairingOutput<P> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let f = P::TargetField::deserialize_with_mode(reader, compress, validate).map(Self)?;
        if let Validate::Yes = validate {
            f.check()?;
        }
        Ok(f)
    }
}

impl<P: Pairing> Display for PairingOutput<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl<P: Pairing> Zero for PairingOutput<P> {
    /// The identity element, or "zero", of the group is the identity element of the multiplicative group of the underlying field, i.e., `P::TargetField::one()`.
    fn zero() -> Self {
        Self(P::TargetField::one())
    }

    fn is_zero(&self) -> bool {
        self.0.is_one()
    }
}

impl<'a, P: Pairing> Add<&'a Self> for PairingOutput<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: Pairing> AddAssign<&'a Self> for PairingOutput<P> {
    fn add_assign(&mut self, other: &'a Self) {
        self.0 *= other.0;
    }
}

impl<'a, P: Pairing> SubAssign<&'a Self> for PairingOutput<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        self.0 *= other.0.cyclotomic_inverse().unwrap();
    }
}

impl<'a, P: Pairing> Sub<&'a Self> for PairingOutput<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

ark_ff::impl_additive_ops_from_ref!(PairingOutput, Pairing);

impl<P: Pairing, T: Borrow<P::ScalarField>> MulAssign<T> for PairingOutput<P> {
    fn mul_assign(&mut self, other: T) {
        *self = self.mul_bigint(other.borrow().into_bigint());
    }
}

impl<P: Pairing, T: Borrow<P::ScalarField>> Mul<T> for PairingOutput<P> {
    type Output = Self;

    fn mul(self, other: T) -> Self {
        self.mul_bigint(other.borrow().into_bigint())
    }
}

impl<P: Pairing> Zeroize for PairingOutput<P> {
    fn zeroize(&mut self) {
        self.0.zeroize()
    }
}

impl<P: Pairing> Neg for PairingOutput<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self(self.0.cyclotomic_inverse().unwrap())
    }
}

impl<P: Pairing> Distribution<PairingOutput<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PairingOutput<P> {
        // Sample a random G1 element
        let g1 = P::G1::rand(rng);
        // Sample a random G2 element
        let g2 = P::G2::rand(rng);
        P::pairing(g1, g2)
    }
}

impl<P: Pairing> Group for PairingOutput<P> {
    type ScalarField = P::ScalarField;

    fn generator() -> Self {
        // TODO: hardcode these values.
        // Sample a random G1 element
        let g1 = P::G1::generator();
        // Sample a random G2 element
        let g2 = P::G2::generator();
        P::pairing(g1.into(), g2.into())
    }

    fn double_in_place(&mut self) -> &mut Self {
        self.0.cyclotomic_square_in_place();
        self
    }

    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self {
        Self(self.0.cyclotomic_exp(other.as_ref()))
    }

    fn mul_bits_be(&self, other: impl Iterator<Item = bool>) -> Self {
        // Convert back from bits to [u64] limbs
        let other = other
            .collect::<Vec<_>>()
            .chunks(64)
            .map(|chunk| {
                chunk
                    .iter()
                    .enumerate()
                    .fold(0, |r, (i, bit)| r | u64::from(*bit) << i)
            })
            .collect::<Vec<_>>();
        Self(self.0.cyclotomic_exp(&other))
    }
}

impl<P: Pairing> crate::ScalarMul for PairingOutput<P> {
    type MulBase = Self;
    const NEGATION_IS_CHEAP: bool = P::TargetField::INVERSE_IS_FAST;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase> {
        bases.to_vec()
    }
}

impl<P: Pairing> VariableBaseMSM for PairingOutput<P> {}

/// Represents the output of the Miller loop of the pairing.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Pairing"),
    Clone(bound = "P: Pairing"),
    Debug(bound = "P: Pairing"),
    PartialEq(bound = "P: Pairing"),
    Eq(bound = "P: Pairing"),
    PartialOrd(bound = "P: Pairing"),
    Ord(bound = "P: Pairing")
)]
#[must_use]
pub struct MillerLoopOutput<P: Pairing>(pub P::TargetField);

impl<P: Pairing> Mul<P::ScalarField> for MillerLoopOutput<P> {
    type Output = Self;

    fn mul(self, other: P::ScalarField) -> Self {
        Self(self.0.pow(other.into_bigint()))
    }
}

/// Preprocesses a G1 element for use in a pairing.
pub fn prepare_g1<E: Pairing>(g: impl Into<E::G1Affine>) -> E::G1Prepared {
    let g: E::G1Affine = g.into();
    E::G1Prepared::from(g)
}

/// Preprocesses a G2 element for use in a pairing.
pub fn prepare_g2<E: Pairing>(g: impl Into<E::G2Affine>) -> E::G2Prepared {
    let g: E::G2Affine = g.into();
    E::G2Prepared::from(g)
}

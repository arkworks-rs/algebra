use crate::*;
use ark_ff::{CyclotomicField, One, PrimeField, SquareRootField, Zero};
use ark_serialize::SerializationError;
use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use ark_std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Write},
};

pub trait Pairing: Sized + 'static + Copy + Debug + Sync + Send + Eq {
    /// This is the scalar field of `Self::G1` and `Self::G2`.
    type ScalarField: PrimeField + SquareRootField;

    /// An element of G1.
    type G1: CurveGroup<ScalarField = Self::ScalarField> + MulAssign<Self::ScalarField>; // needed due to https://github.com/rust-lang/rust/issues/69640

    /// An element of G1 that has been preprocessed for use in a pairing.
    type G1Prepared: Default
        + Clone
        + Send
        + Sync
        + Debug
        + From<Self::G1>
        + From<<Self::G1 as Group>::UniqueRepr>;

    /// An element of G2.
    type G2: CurveGroup<ScalarField = Self::ScalarField> + MulAssign<Self::ScalarField>; // needed due to https://github.com/rust-lang/rust/issues/69640

    /// An element of G2 that has been preprocessed for use in a pairing.
    type G2Prepared: Default
        + Clone
        + Send
        + Sync
        + Debug
        + From<Self::G2>
        + From<<Self::G2 as Group>::UniqueRepr>;

    /// The extension field that hosts the target group of the pairing.
    type TargetField: CyclotomicField;

    /// Perform a miller loop with some number of (G1, G2) pairs.
    #[must_use]
    fn miller_loop<'a>(
        i: impl IntoIterator<Item = &'a (Self::G1Prepared, Self::G2Prepared)>,
    ) -> MillerLoopOutput<Self>;

    /// Perform final exponentiation of the result of a miller loop.
    #[must_use]
    fn final_exponentiation(mlo: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>>;

    /// Computes a product of pairings.
    #[must_use]
    fn product_of_pairings<'a>(
        i: impl IntoIterator<Item = &'a (Self::G1Prepared, Self::G2Prepared)>,
    ) -> PairingOutput<Self> {
        Self::final_exponentiation(Self::miller_loop(i)).unwrap()
    }

    /// Performs a pairing between `p` and and `q
    #[must_use]
    fn pairing(p: Self::G1, q: Self::G2) -> PairingOutput<Self> {
        let p = Self::G1Prepared::from(p);
        let q = Self::G2Prepared::from(q);
        Self::product_of_pairings(core::iter::once(&(p, q)))
    }
}

/// Represents the target group of a pairing. This struct is a
/// wrapper around the field that the target group is embedded in.
#[derive(Derivative)]
#[derivative(
    Copy(bound = ""),
    Clone(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = ""),
    Debug(bound = ""),
    Default(bound = ""),
    Hash(bound = "")
)]
pub struct PairingOutput<P: Pairing>(pub P::TargetField);

impl<P: Pairing> CanonicalSerialize for PairingOutput<P> {
        #[allow(unused_qualifications)]
        #[inline]
        fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            self.0.serialize(writer)
        }

        #[inline]
        fn serialized_size(&self) -> usize {
            self.0.serialized_size()
        }

        #[allow(unused_qualifications)]
        #[inline]
        fn serialize_uncompressed<W: Write>(
            &self,
            writer: W,
        ) -> Result<(), SerializationError> {
            self.0.serialize_uncompressed(writer)
        }

        #[inline]
        fn uncompressed_size(&self) -> usize {
            self.0.uncompressed_size()
        }
    }

    impl<P: Pairing> CanonicalDeserialize for PairingOutput<P> {
        #[allow(unused_qualifications)]
        fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
            Self::deserialize_uncompressed(reader)
        }

        #[allow(unused_qualifications)]
        fn deserialize_uncompressed<R: Read>(
            reader: R,
        ) -> Result<Self, ark_serialize::SerializationError> {
            let f = Self::deserialize_unchecked(reader)?;
            // Check that the output is within the field.
            if f.0.pow(&P::ScalarField::characteristic()).is_one() {
                Ok(f)
            } else {
                Err(SerializationError::InvalidData)
            }
        }

        #[allow(unused_qualifications)]
        fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
            P::TargetField::deserialize_unchecked(reader).map(Self)
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
        self.0 *= other.0.inverse().unwrap();
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

impl<P: Pairing> MulAssign<P::ScalarField> for PairingOutput<P> {
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = GroupUniqueRepr::mul(self, other.into_repr())
    }
}

impl<P: Pairing> GroupUniqueRepr for PairingOutput<P> { type G = Self; }

impl<P: Pairing> Zeroize for PairingOutput<P> {
    fn zeroize(&mut self) {
        self.0.zeroize()
    }
}

impl<P: Pairing> Neg for PairingOutput<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self(self.0.inverse().unwrap())
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
    type UniqueRepr = Self;

    fn generator() -> Self::UniqueRepr {
        // TODO: hardcode these values.
        // Sample a random G1 element
        let g1 = P::G1::generator();
        // Sample a random G2 element
        let g2 = P::G2::generator();
        P::pairing(g1.into(), g2.into())
    }

    fn to_unique(&self) -> Self::UniqueRepr {
        *self
    }

    fn batch_to_unique(v: &[Self]) -> Vec<Self::UniqueRepr> {
        v.iter().copied().collect()
    }

    fn double_in_place(&mut self) -> &mut Self {
        self.0.cyclotomic_square_in_place();
        self
    }

    fn add_unique_in_place(&mut self, other: &Self::UniqueRepr) {
        // We're using the underlying field's multiplicative group.
        self.0 *= other.0
    }

    fn mul(&self, other: impl Into<<Self::ScalarField as PrimeField>::BigInt>) -> Self {
        Self(self.0.cyclotomic_exp(other.into().as_ref()))
    }

    fn mul_bits_be(&self, other: impl Iterator<Item = bool>) -> Self {
        // Convert back from bits to [u64] limbs
        let other = other
        .collect::<Vec<_>>()
        .chunks(64)
        .map(|chunk| 
            chunk.iter().enumerate().fold(0, |r, (i, bit)| r | u64::from(*bit) << i) 
        ).collect::<Vec<_>>();
        Self(self.0.cyclotomic_exp(&other))
    }
}

/// Represents the output of the Miller loop of the pairing.
pub struct MillerLoopOutput<P: Pairing>(pub P::TargetField);

impl<P: Pairing> Mul<P::ScalarField> for MillerLoopOutput<P> {
    type Output = Self;

    fn mul(self, other: P::ScalarField) -> Self {
        Self(self.0.pow(other.into_repr()))
    }
}

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::Borrow,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    io::{Read, Write},
    ops::{Add, Mul, Neg, Sub},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
};

use ark_ff::{fields::Field, AdditiveGroup, One, PrimeField, ToConstraintField, UniformRand};

use educe::Educe;
use zeroize::Zeroize;

use super::{DOCurveConfig, Projective};
use crate::{AffineRepr, CurveGroup};

/// Affine coordinates for a point on an elliptic curve in double odd
/// form, over the base field `P::BaseField`.
#[derive(Educe)]
#[educe(Copy, Clone, PartialEq, Eq, Hash)]
#[must_use]
pub struct Affine<P: DOCurveConfig> {
    #[doc(hidden)]
    pub e: P::BaseField,
    #[doc(hidden)]
    pub u: P::BaseField,
}

impl<P: DOCurveConfig> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        self.into_group() == *other
    }
}

impl<P: DOCurveConfig> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "({}, {})", self.e, self.u)
    }
}

impl<P: DOCurveConfig> Debug for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "({}, {})", self.e, self.u)
    }
}

impl<P: DOCurveConfig> Affine<P> {
    pub fn new(e: P::BaseField, u: P::BaseField) -> Self {
        let point = Self { e, u };
        assert!(point.is_on_curve());
        point
    }

    pub const fn new_unchecked(e: P::BaseField, u: P::BaseField) -> Self {
        Self { e, u }
    }

    pub const fn identity() -> Self {
        Self {
            e: P::BaseField::ONE,
            u: P::BaseField::ZERO,
        }
    }

    pub fn n() -> Self {
        Self {
            e: -P::BaseField::ONE,
            u: P::BaseField::ZERO,
        }
    }

    #[allow(dead_code)]
    pub fn get_point_from_u_unchecked(u: P::BaseField, greatest: bool) -> Option<Self> {
        Self::get_es_from_u_unchecked(u).map(|(smaller, larger)| {
            if greatest {
                Self::new_unchecked(larger, u)
            } else {
                Self::new_unchecked(smaller, u)
            }
        })
    }

    pub fn get_es_from_u_unchecked(u: P::BaseField) -> Option<(P::BaseField, P::BaseField)> {
        // Compute the curve equation x(x^2 + Ax + B).
        let e = (P::get_c() * u.square().square() - (P::COEFF_A * u.square()).double()
            + P::BaseField::ONE)
            .sqrt()?;
        let neg_e = -e;
        match e < neg_e {
            true => Some((e, neg_e)),
            false => Some((neg_e, e)),
        }
    }

    /// Checks if `self` is a valid point on the curve.
    pub fn is_on_curve(&self) -> bool {
        let e_squared = P::get_c() * self.u.square().square()
            - (P::COEFF_A * self.u.square()).double()
            + P::BaseField::ONE;
        self.e.square() == e_squared
    }
}

impl<P: DOCurveConfig> Zeroize for Affine<P> {
    fn zeroize(&mut self) {
        self.e.zeroize();
        self.u.zeroize();
    }
}

impl<P: DOCurveConfig> Distribution<Affine<P>> for Standard {
    /// Generates a uniformly random point in the prime-order subgroup.
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let u = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_u_unchecked(u, greatest) {
                return p;
            }
        }
    }
}

impl<P: DOCurveConfig> AffineRepr for Affine<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Group = Projective<P>;

    fn xy(&self) -> Option<(Self::BaseField, Self::BaseField)> {
        unimplemented!()
    }

    #[inline]
    fn generator() -> Self {
        P::GENERATOR
    }

    fn zero() -> Self {
        Self {
            e: P::BaseField::ONE,
            u: P::BaseField::ZERO
        }
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes(bytes).and_then(|u| {
            Self::get_point_from_u_unchecked(u, true)
        })
    }

    fn mul_bigint(&self, by: impl AsRef<[u64]>) -> Self::Group {
        P::mul_affine(self, by.as_ref())
    }

    /// Multiplies this element by the cofactor and output the
    /// resulting projective element.
    #[must_use]
    fn mul_by_cofactor_to_group(&self) -> Self::Group {
        P::mul_affine(self, Self::Config::COFACTOR)
    }

    /// Performs cofactor clearing.
    /// The default method is simply to multiply by the cofactor.
    /// Some curves can implement a more efficient algorithm.
    fn clear_cofactor(&self) -> Self {
        P::mul_affine(self, Self::Config::COFACTOR).into_affine()
    }
}

impl<P: DOCurveConfig> Neg for Affine<P> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.u.neg_in_place();
        self
    }
}

impl<P: DOCurveConfig, T: Borrow<Self>> Add<T> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: T) -> Projective<P> {
        let mut copy = self.into_group();
        copy += other.borrow();
        copy
    }
}

impl<P: DOCurveConfig> Add<Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: Projective<P>) -> Projective<P> {
        other + self
    }
}

impl<'a, P: DOCurveConfig> Add<&'a Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: &'a Projective<P>) -> Projective<P> {
        *other + self
    }
}

impl<P: DOCurveConfig, T: Borrow<Self>> Sub<T> for Affine<P> {
    type Output = Projective<P>;
    fn sub(self, other: T) -> Projective<P> {
        let mut copy = self.into_group();
        copy -= other.borrow();
        copy
    }
}

impl<P: DOCurveConfig> Sub<Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn sub(self, other: Projective<P>) -> Projective<P> {
        self + (-other)
    }
}

impl<'a, P: DOCurveConfig> Sub<&'a Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn sub(self, other: &'a Projective<P>) -> Projective<P> {
        self + (-*other)
    }
}

impl<P: DOCurveConfig> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::identity()
    }
}

impl<P: DOCurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Affine<P> {
    type Output = Projective<P>;

    #[inline]
    fn mul(self, other: T) -> Self::Output {
        self.mul_bigint(other.borrow().into_bigint())
    }
}

// The projective point E, Z, U, T is represented in the affine
// coordinates as (e, u) by E/Z, U/Z
impl<P: DOCurveConfig> From<Projective<P>> for Affine<P> {
    #[inline]
    fn from(p: Projective<P>) -> Affine<P> {
        use crate::ark_std::Zero;

        if p.is_zero() {
            Self::identity()
        } else if p.z.is_one() {
            Self::new_unchecked(p.e, p.u)
        } else {
            let z_i = p.z.inverse().unwrap();

            let u = p.u * &z_i;
            let e = p.e * &z_i;

            Affine::new_unchecked(e, u)
        }
    }
}

impl<P: DOCurveConfig> CanonicalSerialize for Affine<P> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        P::serialize_with_mode(self, writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        P::serialized_size(compress)
    }
}

impl<P: DOCurveConfig> Valid for Affine<P> {
    fn check(&self) -> Result<(), SerializationError> {
        if self.is_on_curve() {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl<P: DOCurveConfig> CanonicalDeserialize for Affine<P> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        P::deserialize_with_mode(reader, compress, validate)
    }
}

impl<M: DOCurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Affine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        let mut e = self.e.to_field_elements()?;
        let u = self.u.to_field_elements()?;
        e.extend_from_slice(&u);
        Some(e)
    }
}

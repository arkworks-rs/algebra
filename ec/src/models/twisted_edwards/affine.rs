use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, EdwardsFlags, SerializationError,
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
use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

use super::{Projective, TECurveConfig};
use crate::AffineRepr;

/// Affine coordinates for a point on a twisted Edwards curve, over the
/// base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: TECurveConfig"),
    Clone(bound = "P: TECurveConfig"),
    PartialEq(bound = "P: TECurveConfig"),
    Eq(bound = "P: TECurveConfig"),
    Hash(bound = "P: TECurveConfig")
)]
#[must_use]
pub struct Affine<P: TECurveConfig> {
    /// X coordinate of the point represented as a field element
    pub x: P::BaseField,
    /// Y coordinate of the point represented as a field element
    pub y: P::BaseField,
}

impl<P: TECurveConfig> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.is_identity() {
            true => write!(f, "infinity"),
            false => write!(f, "({}, {})", self.x, self.y),
        }
    }
}

impl<P: TECurveConfig> Debug for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.is_identity() {
            true => write!(f, "infinity"),
            false => write!(f, "({}, {})", self.x, self.y),
        }
    }
}

impl<P: TECurveConfig> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        self.into_group() == *other
    }
}

impl<P: TECurveConfig> Affine<P> {
    /// Construct a new group element without checking whether the coordinates
    /// specify a point in the subgroup.
    pub const fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
    }

    /// Construct a new group element in a way while enforcing that points are in
    /// the prime-order subgroup.
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        let p = Self::new_unchecked(x, y);
        assert!(p.is_on_curve());
        assert!(p.is_in_correct_subgroup_assuming_on_curve());
        p
    }

    /// Construct the identity of the group
    pub const fn identity() -> Self {
        Self::new_unchecked(P::BaseField::ZERO, P::BaseField::ONE)
    }

    /// Is this point the identity?
    pub fn is_identity(&self) -> bool {
        self.x.is_zero() && self.y.is_one()
    }

    /// Attempts to construct an affine point given an y-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest x-coordinate be selected.
    ///
    /// a * X^2 + Y^2 = 1 + d * X^2 * Y^2
    /// a * X^2 - d * X^2 * Y^2 = 1 - Y^2
    /// X^2 * (a - d * Y^2) = 1 - Y^2
    /// X^2 = (1 - Y^2) / (a - d * Y^2)
    #[allow(dead_code)]
    pub fn get_point_from_y(y: P::BaseField, greatest: bool) -> Option<Self> {
        let y2 = y.square();

        let numerator = P::BaseField::one() - y2;
        let denominator = P::COEFF_A - (y2 * P::COEFF_D);

        denominator
            .inverse()
            .map(|denom| denom * &numerator)
            .and_then(|x2| x2.sqrt())
            .map(|x| {
                let negx = -x;
                let x = if (x < negx) ^ greatest { x } else { negx };
                Self::new_unchecked(x, y)
            })
    }

    /// Checks that the current point is on the elliptic curve.
    pub fn is_on_curve(&self) -> bool {
        let x2 = self.x.square();
        let y2 = self.y.square();

        let lhs = y2 + &P::mul_by_a(&x2);
        let rhs = P::BaseField::one() + &(P::COEFF_D * &(x2 * &y2));

        lhs == rhs
    }
}

impl<P: TECurveConfig> Affine<P> {
    /// Checks if `self` is in the subgroup having order equaling that of
    /// `P::ScalarField` given it is on the curve.
    pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        P::is_in_correct_subgroup_assuming_on_curve(self)
    }
}

impl<P: TECurveConfig> AffineRepr for Affine<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Group = Projective<P>;

    fn xy(&self) -> Option<(&Self::BaseField, &Self::BaseField)> {
        (!self.is_identity()).then(|| (&self.x, &self.y))
    }

    fn generator() -> Self {
        P::GENERATOR
    }

    fn identity() -> Self {
        Self::new_unchecked(P::BaseField::ZERO, P::BaseField::ONE)
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<EdwardsFlags>(bytes).and_then(|(y, flags)| {
            // if y is valid and is zero, then parse this
            // point as infinity.
            if y.is_zero() {
                Some(Self::identity())
            } else {
                Self::get_point_from_y(y, flags.is_positive())
            }
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
        P::clear_cofactor(self)
    }
}

impl<P: TECurveConfig> Zeroize for Affine<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
    }
}

impl<P: TECurveConfig> Neg for Affine<P> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new_unchecked(-self.x, self.y)
    }
}

impl<P: TECurveConfig, T: Borrow<Self>> Add<T> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: T) -> Self::Output {
        let mut copy = self.into_group();
        copy += other.borrow();
        copy
    }
}

impl<P: TECurveConfig> Add<Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: Projective<P>) -> Projective<P> {
        other + self
    }
}

impl<'a, P: TECurveConfig> Add<&'a Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: &'a Projective<P>) -> Projective<P> {
        *other + self
    }
}

impl<P: TECurveConfig, T: Borrow<Self>> Sub<T> for Affine<P> {
    type Output = Projective<P>;
    fn sub(self, other: T) -> Self::Output {
        let mut copy = self.into_group();
        copy -= other.borrow();
        copy
    }
}

impl<P: TECurveConfig> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::identity()
    }
}

impl<P: TECurveConfig> Distribution<Affine<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let y = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_y(y, greatest) {
                return p.mul_by_cofactor();
            }
        }
    }
}

impl<'a, P: TECurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Affine<P> {
    type Output = Projective<P>;

    #[inline]
    fn mul(self, other: T) -> Self::Output {
        self.mul_bigint(other.borrow().into_bigint())
    }
}

// The projective point X, Y, T, Z is represented in the affine
// coordinates as X/Z, Y/Z.
impl<P: TECurveConfig> From<Projective<P>> for Affine<P> {
    fn from(p: Projective<P>) -> Affine<P> {
        if p.is_zero() {
            Affine::identity()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Affine::new_unchecked(p.x, p.y)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let z_inv = p.z.inverse().unwrap();
            let x = p.x * &z_inv;
            let y = p.y * &z_inv;
            Affine::new_unchecked(x, y)
        }
    }
}

impl<P: TECurveConfig> CanonicalSerialize for Affine<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_identity() {
            let flags = EdwardsFlags::default();
            // Serialize 0.
            P::BaseField::zero().serialize_with_flags(writer, flags)
        } else {
            let flags = EdwardsFlags::from_x_sign(self.x > -self.x);
            self.y.serialize_with_flags(writer, flags)
        }
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<EdwardsFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        self.x.serialize_uncompressed(&mut writer)?;
        self.y.serialize_uncompressed(&mut writer)?;
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        // x  + y
        self.x.serialized_size() + self.y.serialized_size()
    }
}

impl<P: TECurveConfig> CanonicalDeserialize for Affine<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let (y, flags): (P::BaseField, EdwardsFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        if y == P::BaseField::zero() {
            Ok(Self::identity())
        } else {
            let p = Affine::<P>::get_point_from_y(y, flags.is_positive())
                .ok_or(SerializationError::InvalidData)?;
            if !p.is_in_correct_subgroup_assuming_on_curve() {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;

        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let y: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;

        let p = Affine::<P>::new_unchecked(x, y);
        Ok(p)
    }
}

impl<M: TECurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Affine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Some(x_fe)
    }
}

// This impl block and the one following are being used to encapsulate all of
// the methods that are needed for backwards compatibility with the old
// serialization format
// See Issue #330
impl<P: TECurveConfig> Affine<P> {
    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    ///
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    #[allow(dead_code)]
    pub fn get_point_from_x_old(x: P::BaseField, greatest: bool) -> Option<Self> {
        let x2 = x.square();
        let one = P::BaseField::one();
        let numerator = P::mul_by_a(&x2) - &one;
        let denominator = P::COEFF_D * &x2 - &one;
        let y2 = denominator.inverse().map(|denom| denom * &numerator);
        y2.and_then(|y2| y2.sqrt()).map(|y| {
            let negy = -y;
            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new_unchecked(x, y)
        })
    }
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn serialize_old<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_identity() {
            let flags = EdwardsFlags::default();
            // Serialize 0.
            P::BaseField::zero().serialize_with_flags(writer, flags)
        } else {
            // Note: although this says `from_x_sign` and we are
            // using the sign of `y`. The logic works the same.
            let flags = EdwardsFlags::from_x_sign(self.y > -self.y);
            self.x.serialize_with_flags(writer, flags)
        }
    }

    #[allow(unused_qualifications)]
    #[inline]
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn serialize_uncompressed_old<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        self.x.serialize_uncompressed(&mut writer)?;
        self.y.serialize_uncompressed(&mut writer)?;
        Ok(())
    }

    #[allow(unused_qualifications)]
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn deserialize_uncompressed_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;

        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn deserialize_old<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, EdwardsFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        if x == P::BaseField::zero() {
            Ok(Self::identity())
        } else {
            let p = Affine::<P>::get_point_from_x_old(x, flags.is_positive())
                .ok_or(SerializationError::InvalidData)?;
            if !p.is_in_correct_subgroup_assuming_on_curve() {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }
    }
}

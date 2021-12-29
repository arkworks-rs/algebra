use crate::{
    models::{MontgomeryModelParameters as MontgomeryParameters, TEModelParameters as Parameters},
    AffineCurve, ProjectiveCurve,
};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, EdwardsFlags, SerializationError,
};
use ark_std::{
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    io::{Read, Result as IoResult, Write},
    ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
};
use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_ff::{
    bytes::{FromBytes, ToBytes},
    fields::{Field, PrimeField, SquareRootField},
    ToConstraintField, UniformRand,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Affine coordinates for a point on a twisted Edwards curve, over the
/// base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    PartialEq(bound = "P: Parameters"),
    Eq(bound = "P: Parameters"),
    Debug(bound = "P: Parameters"),
    Hash(bound = "P: Parameters")
)]
#[must_use]
pub struct GroupAffine<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
}

impl<P: Parameters> Display for GroupAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "GroupAffine(x={}, y={})", self.x, self.y)
    }
}

impl<P: Parameters> GroupAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
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
                Self::new(x, y)
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

impl<P: Parameters> GroupAffine<P> {
    /// Checks if `self` is in the subgroup having order equaling that of
    /// `P::ScalarField` given it is on the curve.
    pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        P::is_in_correct_subgroup_assuming_on_curve(self)
    }
}

impl<P: Parameters> Zero for GroupAffine<P> {
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one())
    }

    fn is_zero(&self) -> bool {
        self.x.is_zero() & self.y.is_one()
    }
}

impl<P: Parameters> AffineCurve for GroupAffine<P> {
    type Parameters = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Projective = GroupProjective<P>;

    fn prime_subgroup_generator() -> Self {
        Self::new(P::AFFINE_GENERATOR_COEFFS.0, P::AFFINE_GENERATOR_COEFFS.1)
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<EdwardsFlags>(bytes).and_then(|(y, flags)| {
            // if y is valid and is zero, then parse this
            // point as infinity.
            if y.is_zero() {
                Some(Self::zero())
            } else {
                Self::get_point_from_y(y, flags.is_positive())
            }
        })
    }
}

impl<P: Parameters> Zeroize for GroupAffine<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
    }
}

impl<P: Parameters> Neg for GroupAffine<P> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.x, self.y)
    }
}

ark_ff::impl_additive_ops_from_ref!(GroupAffine, Parameters);

impl<'a, P: Parameters> Add<&'a Self> for GroupAffine<P> {
    type Output = Self;
    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for GroupAffine<P> {
    fn add_assign(&mut self, other: &'a Self) {
        let y1y2 = self.y * &other.y;
        let x1x2 = self.x * &other.x;
        let dx1x2y1y2 = P::COEFF_D * &y1y2 * &x1x2;

        let d1 = P::BaseField::one() + &dx1x2y1y2;
        let d2 = P::BaseField::one() - &dx1x2y1y2;

        let x1y2 = self.x * &other.y;
        let y1x2 = self.y * &other.x;

        self.x = (x1y2 + &y1x2) / &d1;
        self.y = (y1y2 - &P::mul_by_a(&x1x2)) / &d2;
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for GroupAffine<P> {
    type Output = Self;
    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for GroupAffine<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: Parameters> MulAssign<P::ScalarField> for GroupAffine<P> {
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = self.mul(other.into_repr()).into()
    }
}

impl<P: Parameters> ToBytes for GroupAffine<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)
    }
}

impl<P: Parameters> FromBytes for GroupAffine<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        Ok(Self::new(x, y))
    }
}

impl<P: Parameters> Default for GroupAffine<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> Distribution<GroupAffine<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> GroupAffine<P> {
        loop {
            let y = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = GroupAffine::get_point_from_y(y, greatest) {
                return p.mul_by_cofactor();
            }
        }
    }
}

mod group_impl {
    use super::*;
    use crate::group::Group;

    impl<P: Parameters> Group for GroupAffine<P> {
        type ScalarField = P::ScalarField;

        #[inline]
        fn double(&self) -> Self {
            let mut tmp = *self;
            tmp += self;
            tmp
        }

        #[inline]
        fn double_in_place(&mut self) -> &mut Self {
            let mut tmp = *self;
            tmp += &*self;
            *self = tmp;
            self
        }
    }
}

//////////////////////////////////////////////////////////////////////////////

/// `GroupProjective` implements Extended Twisted Edwards Coordinates
/// as described in [\[HKCD08\]](https://eprint.iacr.org/2008/522.pdf).
///
/// This implementation uses the unified addition formulae from that paper (see
/// Section 3.1).
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    Eq(bound = "P: Parameters"),
    Debug(bound = "P: Parameters")
)]
#[must_use]
pub struct GroupProjective<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub t: P::BaseField,
    pub z: P::BaseField,
}

impl<P: Parameters> PartialEq<GroupProjective<P>> for GroupAffine<P> {
    fn eq(&self, other: &GroupProjective<P>) -> bool {
        self.into_projective() == *other
    }
}

impl<P: Parameters> PartialEq<GroupAffine<P>> for GroupProjective<P> {
    fn eq(&self, other: &GroupAffine<P>) -> bool {
        *self == other.into_projective()
    }
}

impl<P: Parameters> Display for GroupProjective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", GroupAffine::from(*self))
    }
}

impl<P: Parameters> PartialEq for GroupProjective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // x1/z1 == x2/z2  <==> x1 * z2 == x2 * z1
        (self.x * &other.z) == (other.x * &self.z) && (self.y * &other.z) == (other.y * &self.z)
    }
}

impl<P: Parameters> Hash for GroupProjective<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.into_affine().hash(state)
    }
}

impl<P: Parameters> Distribution<GroupProjective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> GroupProjective<P> {
        loop {
            let y = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = GroupAffine::get_point_from_y(y, greatest) {
                return p.mul_by_cofactor_to_projective();
            }
        }
    }
}

impl<P: Parameters> ToBytes for GroupProjective<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)?;
        self.t.write(&mut writer)?;
        self.z.write(writer)
    }
}

impl<P: Parameters> FromBytes for GroupProjective<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let t = P::BaseField::read(&mut reader)?;
        let z = P::BaseField::read(reader)?;
        Ok(Self::new(x, y, t, z))
    }
}

impl<P: Parameters> Default for GroupProjective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> GroupProjective<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, t: P::BaseField, z: P::BaseField) -> Self {
        Self { x, y, t, z }
    }
}
impl<P: Parameters> Zeroize for GroupProjective<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.t.zeroize();
        self.z.zeroize();
    }
}

impl<P: Parameters> Zero for GroupProjective<P> {
    fn zero() -> Self {
        Self::new(
            P::BaseField::zero(),
            P::BaseField::one(),
            P::BaseField::zero(),
            P::BaseField::one(),
        )
    }

    fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y == self.z && !self.y.is_zero() && self.t.is_zero()
    }
}

impl<P: Parameters> ProjectiveCurve for GroupProjective<P> {
    type Parameters = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Affine = GroupAffine<P>;

    fn prime_subgroup_generator() -> Self {
        GroupAffine::prime_subgroup_generator().into()
    }

    fn is_normalized(&self) -> bool {
        self.z.is_one()
    }

    fn batch_normalization(v: &mut [Self]) {
        // A projective curve element (x, y, t, z) is normalized
        // to its affine representation, by the conversion
        // (x, y, t, z) -> (x/z, y/z, t/z, 1)
        // Batch normalizing N twisted edwards curve elements costs:
        //     1 inversion + 6N field multiplications
        // (batch inversion requires 3N multiplications + 1 inversion)
        let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
        ark_ff::batch_inversion(&mut z_s);

        // Perform affine transformations
        ark_std::cfg_iter_mut!(v)
            .zip(z_s)
            .filter(|(g, _)| !g.is_normalized())
            .for_each(|(g, z)| {
                g.x *= &z; // x/z
                g.y *= &z;
                g.t *= &z;
                g.z = P::BaseField::one(); // z = 1
            });
    }

    fn double_in_place(&mut self) -> &mut Self {
        // See "Twisted Edwards Curves Revisited"
        // Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        // 3.3 Doubling in E^e
        // Source: https://www.hyperelliptic.org/EFD/g1p/data/twisted/extended/doubling/dbl-2008-hwcd

        // A = X1^2
        let a = self.x.square();
        // B = Y1^2
        let b = self.y.square();
        // C = 2 * Z1^2
        let c = self.z.square().double();
        // D = a * A
        let d = P::mul_by_a(&a);
        // E = (X1 + Y1)^2 - A - B
        let e = (self.x + &self.y).square() - &a - &b;
        // G = D + B
        let g = d + &b;
        // F = G - C
        let f = g - &c;
        // H = D - B
        let h = d - &b;
        // X3 = E * F
        self.x = e * &f;
        // Y3 = G * H
        self.y = g * &h;
        // T3 = E * H
        self.t = e * &h;
        // Z3 = F * G
        self.z = f * &g;

        self
    }

    fn add_assign_mixed(&mut self, other: &GroupAffine<P>) {
        // See "Twisted Edwards Curves Revisited"
        // Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        // 3.1 Unified Addition in E^e
        // Source: https://www.hyperelliptic.org/EFD/g1p/data/twisted/extended/addition/madd-2008-hwcd

        // A = X1*X2
        let a = self.x * &other.x;
        // B = Y1*Y2
        let b = self.y * &other.y;
        // C = T1*d*T2
        let c = P::COEFF_D * &self.t * &other.x * &other.y;

        // D = Z1
        let d = self.z;
        // E = (X1+Y1)*(X2+Y2)-A-B
        let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;
        // F = D-C
        let f = d - &c;
        // G = D+C
        let g = d + &c;
        // H = B-a*A
        let h = b - &P::mul_by_a(&a);
        // X3 = E*F
        self.x = e * &f;
        // Y3 = G*H
        self.y = g * &h;
        // T3 = E*H
        self.t = e * &h;
        // Z3 = F*G
        self.z = f * &g;
    }
}

impl<P: Parameters> Neg for GroupProjective<P> {
    type Output = Self;
    fn neg(mut self) -> Self {
        self.x = -self.x;
        self.t = -self.t;
        self
    }
}

ark_ff::impl_additive_ops_from_ref!(GroupProjective, Parameters);

impl<'a, P: Parameters> Add<&'a Self> for GroupProjective<P> {
    type Output = Self;
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for GroupProjective<P> {
    fn add_assign(&mut self, other: &'a Self) {
        // See "Twisted Edwards Curves Revisited" (https://eprint.iacr.org/2008/522.pdf)
        // by Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        // 3.1 Unified Addition in E^e

        // A = x1 * x2
        let a = self.x * &other.x;

        // B = y1 * y2
        let b = self.y * &other.y;

        // C = d * t1 * t2
        let c = P::COEFF_D * &self.t * &other.t;

        // D = z1 * z2
        let d = self.z * &other.z;

        // H = B - aA
        let h = b - &P::mul_by_a(&a);

        // E = (x1 + y1) * (x2 + y2) - A - B
        let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;

        // F = D - C
        let f = d - &c;

        // G = D + C
        let g = d + &c;

        // x3 = E * F
        self.x = e * &f;

        // y3 = G * H
        self.y = g * &h;

        // t3 = E * H
        self.t = e * &h;

        // z3 = F * G
        self.z = f * &g;
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for GroupProjective<P> {
    type Output = Self;
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for GroupProjective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: Parameters> MulAssign<P::ScalarField> for GroupProjective<P> {
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = self.mul(other.into_repr())
    }
}

// The affine point (X, Y) is represented in the Extended Projective coordinates
// with Z = 1.
impl<P: Parameters> From<GroupAffine<P>> for GroupProjective<P> {
    fn from(p: GroupAffine<P>) -> GroupProjective<P> {
        Self::new(p.x, p.y, p.x * &p.y, P::BaseField::one())
    }
}

// The projective point X, Y, T, Z is represented in the affine
// coordinates as X/Z, Y/Z.
impl<P: Parameters> From<GroupProjective<P>> for GroupAffine<P> {
    fn from(p: GroupProjective<P>) -> GroupAffine<P> {
        if p.is_zero() {
            GroupAffine::zero()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            GroupAffine::new(p.x, p.y)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let z_inv = p.z.inverse().unwrap();
            let x = p.x * &z_inv;
            let y = p.y * &z_inv;
            GroupAffine::new(x, y)
        }
    }
}

impl<P: Parameters> core::str::FromStr for GroupAffine<P>
where
    P::BaseField: core::str::FromStr<Err = ()>,
{
    type Err = ();

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        s = s.trim();
        if s.is_empty() {
            return Err(());
        }
        if s.len() < 3 {
            return Err(());
        }
        if !(s.starts_with('(') && s.ends_with(')')) {
            return Err(());
        }
        let mut point = Vec::new();
        for substr in s.split(|c| c == '(' || c == ')' || c == ',' || c == ' ') {
            if !substr.is_empty() {
                point.push(P::BaseField::from_str(substr)?);
            }
        }
        if point.len() != 2 {
            return Err(());
        }
        let point = Self::new(point[0], point[1]);

        if !point.is_on_curve() {
            Err(())
        } else {
            Ok(point)
        }
    }
}

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: MontgomeryParameters"),
    Clone(bound = "P: MontgomeryParameters"),
    PartialEq(bound = "P: MontgomeryParameters"),
    Eq(bound = "P: MontgomeryParameters"),
    Debug(bound = "P: MontgomeryParameters"),
    Hash(bound = "P: MontgomeryParameters")
)]
pub struct MontgomeryGroupAffine<P: MontgomeryParameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
}

impl<P: MontgomeryParameters> Display for MontgomeryGroupAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "MontgomeryGroupAffine(x={}, y={})", self.x, self.y)
    }
}

impl<P: MontgomeryParameters> MontgomeryGroupAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
    }
}

impl<P: Parameters> CanonicalSerialize for GroupAffine<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
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

impl<P: Parameters> CanonicalSerialize for GroupProjective<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialized_size()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize_uncompressed(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.uncompressed_size()
    }
}

impl<P: Parameters> CanonicalDeserialize for GroupAffine<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let (y, flags): (P::BaseField, EdwardsFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        if y == P::BaseField::zero() {
            Ok(Self::zero())
        } else {
            let p = GroupAffine::<P>::get_point_from_y(y, flags.is_positive())
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

        let p = GroupAffine::<P>::new(x, y);
        Ok(p)
    }
}

impl<P: Parameters> CanonicalDeserialize for GroupProjective<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_uncompressed(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_unchecked(reader)?;
        Ok(aff.into())
    }
}

impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for GroupAffine<M>
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

impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for GroupProjective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        GroupAffine::from(*self).to_field_elements()
    }
}

// This impl block and the one following are being used to encapsulate all of
// the methods that are needed for backwards compatibility with the old
// serialization format
// See Issue #330
impl<P: Parameters> GroupAffine<P> {
    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    ///
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
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
            Self::new(x, y)
        })
    }
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn serialize_old<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
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
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn serialize_uncompressed_old<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        self.x.serialize_uncompressed(&mut writer)?;
        self.y.serialize_uncompressed(&mut writer)?;
        Ok(())
    }

    #[allow(unused_qualifications)]
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn deserialize_uncompressed_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;

        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn deserialize_old<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, EdwardsFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        if x == P::BaseField::zero() {
            Ok(Self::zero())
        } else {
            let p = GroupAffine::<P>::get_point_from_x_old(x, flags.is_positive())
                .ok_or(SerializationError::InvalidData)?;
            if !p.is_in_correct_subgroup_assuming_on_curve() {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }
    }
}
impl<P: Parameters> GroupProjective<P> {
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn serialize_old<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize_old(writer)
    }

    #[allow(unused_qualifications)]
    #[inline]
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn serialize_uncompressed_old<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize_uncompressed(writer)
    }

    #[allow(unused_qualifications)]
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn deserialize_uncompressed_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_uncompressed(reader)?;
        Ok(aff.into())
    }
    /// This method is implemented for backwards compatibility with the old serialization format
    /// and will be deprecated and then removed in a future version.
    pub fn deserialize_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_old(reader)?;
        Ok(aff.into())
    }
}

use crate::{
    scalar_mul::{ScalarMul, VariableBaseMSM},
    AffineRepr, CurveGroup, Group,
};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, EdwardsFlags, SerializationError,
};
use ark_std::{
    borrow::Borrow,
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    io::{Read, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
};
use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Constants and convenience functions that collectively define the [Twisted Edwards model](https://www.hyperelliptic.org/EFD/g1p/auto-twisted.html)
/// of the curve. In this model, the curve equation is
/// `a * x² + y² = 1 + d * x² * y²`, for constants `a` and `d`.
pub trait TECurveConfig: super::CurveConfig {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `d` of the curve equation.
    const COEFF_D: Self::BaseField;
    /// Generator of the prime-order subgroup.
    const GENERATOR: Affine<Self>;

    /// Model parameters for the Montgomery curve that is birationally
    /// equivalent to this curve.
    type MontCurveConfig: MontCurveConfig<BaseField = Self::BaseField>;

    /// Helper method for computing `elem * Self::COEFF_A`.
    ///
    /// The default implementation should be overridden only if
    /// the product can be computed faster than standard field multiplication
    /// (eg: via doubling if `COEFF_A == 2`, or if `COEFF_A.is_zero()`).
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    /// Checks that the current point is in the prime order subgroup given
    /// the point on the curve.
    fn is_in_correct_subgroup_assuming_on_curve(item: &Affine<Self>) -> bool {
        Self::mul_affine(item, Self::ScalarField::characteristic()).is_zero()
    }

    /// Performs cofactor clearing.
    /// The default method is simply to multiply by the cofactor.
    /// For some curve families though, it is sufficient to multiply
    /// by a smaller scalar.
    fn clear_cofactor(item: &Affine<Self>) -> Affine<Self> {
        item.mul_by_cofactor()
    }

    /// Default implementation of group multiplication for projective
    /// coordinates
    fn mul_projective(base: &Projective<Self>, scalar: &[u64]) -> Projective<Self> {
        let mut res = Projective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base;
            }
        }

        res
    }

    /// Default implementation of group multiplication for affine
    /// coordinates
    fn mul_affine(base: &Affine<Self>, scalar: &[u64]) -> Projective<Self> {
        let mut res = Projective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base
            }
        }

        res
    }
}

/// Constants and convenience functions that collectively define the [Montgomery model](https://www.hyperelliptic.org/EFD/g1p/auto-montgom.html)
/// of the curve. In this model, the curve equation is
/// `b * y² = x³ + a * x² + x`, for constants `a` and `b`.
pub trait MontCurveConfig: super::CurveConfig {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `b` of the curve equation.
    const COEFF_B: Self::BaseField;

    /// Model parameters for the Twisted Edwards curve that is birationally
    /// equivalent to this curve.
    type TECurveConfig: TECurveConfig<BaseField = Self::BaseField>;
}

/// Affine coordinates for a point on a twisted Edwards curve, over the
/// base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: TECurveConfig"),
    Clone(bound = "P: TECurveConfig"),
    PartialEq(bound = "P: TECurveConfig"),
    Eq(bound = "P: TECurveConfig"),
    Debug(bound = "P: TECurveConfig"),
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
        write!(f, "Affine(x={}, y={})", self.x, self.y)
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
        Self::new_unchecked(P::BaseField::zero(), P::BaseField::one())
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

//////////////////////////////////////////////////////////////////////////////

/// `Projective` implements Extended Twisted Edwards Coordinates
/// as described in [\[HKCD08\]](https://eprint.iacr.org/2008/522.pdf).
///
/// This implementation uses the unified addition formulae from that paper (see
/// Section 3.1).
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: TECurveConfig"),
    Clone(bound = "P: TECurveConfig"),
    Eq(bound = "P: TECurveConfig"),
    Debug(bound = "P: TECurveConfig")
)]
#[must_use]
pub struct Projective<P: TECurveConfig> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub t: P::BaseField,
    pub z: P::BaseField,
}

impl<P: TECurveConfig> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        self.into_group() == *other
    }
}

impl<P: TECurveConfig> PartialEq<Affine<P>> for Projective<P> {
    fn eq(&self, other: &Affine<P>) -> bool {
        *self == other.into_group()
    }
}

impl<P: TECurveConfig> Display for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", Affine::from(*self))
    }
}

impl<P: TECurveConfig> PartialEq for Projective<P> {
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

impl<P: TECurveConfig> Hash for Projective<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.into_affine().hash(state)
    }
}

impl<P: TECurveConfig> Distribution<Projective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
        loop {
            let y = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_y(y, greatest) {
                return p.mul_by_cofactor_to_group();
            }
        }
    }
}

impl<P: TECurveConfig> Default for Projective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: TECurveConfig> Projective<P> {
    /// Construct a new group element without checking whether the coordinates
    /// specify a point in the subgroup.
    pub const fn new_unchecked(
        x: P::BaseField,
        y: P::BaseField,
        t: P::BaseField,
        z: P::BaseField,
    ) -> Self {
        Self { x, y, t, z }
    }

    /// Construct a new group element in a way while enforcing that points are in
    /// the prime-order subgroup.
    pub fn new(x: P::BaseField, y: P::BaseField, t: P::BaseField, z: P::BaseField) -> Self {
        let p = Self::new_unchecked(x, y, t, z).into_affine();
        assert!(p.is_on_curve());
        assert!(p.is_in_correct_subgroup_assuming_on_curve());
        p.into()
    }
}
impl<P: TECurveConfig> Zeroize for Projective<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.t.zeroize();
        self.z.zeroize();
    }
}

impl<P: TECurveConfig> Zero for Projective<P> {
    fn zero() -> Self {
        Self::new_unchecked(
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

impl<P: TECurveConfig> Group for Projective<P> {
    type ScalarField = P::ScalarField;

    fn generator() -> Self {
        Affine::generator().into()
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

    #[inline]
    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self {
        P::mul_projective(&self, other.as_ref())
    }
}

impl<P: TECurveConfig> CurveGroup for Projective<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type Affine = Affine<P>;
    type FullGroup = Affine<P>;

    fn normalize_batch(v: &[Self]) -> Vec<Self::Affine> {
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
            .map(|(g, z)| match g.is_zero() {
                true => Affine::identity(),
                false => {
                    let x = g.x * &z;
                    let y = g.y * &z;
                    Affine::new_unchecked(x, y)
                },
            })
            .collect()
    }
}

impl<P: TECurveConfig> Neg for Projective<P> {
    type Output = Self;
    fn neg(mut self) -> Self {
        self.x = -self.x;
        self.t = -self.t;
        self
    }
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> AddAssign<T> for Projective<P> {
    fn add_assign(&mut self, other: T) {
        let other = other.borrow();
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

impl<P: TECurveConfig, T: Borrow<Affine<P>>> Add<T> for Projective<P> {
    type Output = Self;
    fn add(mut self, other: T) -> Self {
        let other = other.borrow();
        self += other;
        self
    }
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> SubAssign<T> for Projective<P> {
    fn sub_assign(&mut self, other: T) {
        *self += -(*other.borrow());
    }
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> Sub<T> for Projective<P> {
    type Output = Self;
    fn sub(mut self, other: T) -> Self {
        self -= other.borrow();
        self
    }
}
ark_ff::impl_additive_ops_from_ref!(Projective, TECurveConfig);

impl<'a, P: TECurveConfig> Add<&'a Self> for Projective<P> {
    type Output = Self;
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: TECurveConfig> Sub<&'a Self> for Projective<P> {
    type Output = Self;
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

impl<'a, P: TECurveConfig> AddAssign<&'a Self> for Projective<P> {
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

impl<'a, P: TECurveConfig> SubAssign<&'a Self> for Projective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += -(*other);
    }
}

impl<P: TECurveConfig, T: Borrow<P::ScalarField>> MulAssign<T> for Projective<P> {
    fn mul_assign(&mut self, other: T) {
        *self = self.mul_bigint(other.borrow().into_bigint())
    }
}

impl<P: TECurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Projective<P> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: T) -> Self {
        self *= other;
        self
    }
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> ark_std::iter::Sum<T> for Projective<P> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::zero(), |acc, x| acc + x.borrow())
    }
}

// The affine point (X, Y) is represented in the Extended Projective coordinates
// with Z = 1.
impl<P: TECurveConfig> From<Affine<P>> for Projective<P> {
    fn from(p: Affine<P>) -> Projective<P> {
        Self::new_unchecked(p.x, p.y, p.x * &p.y, P::BaseField::one())
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

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: MontCurveConfig"),
    Clone(bound = "P: MontCurveConfig"),
    PartialEq(bound = "P: MontCurveConfig"),
    Eq(bound = "P: MontCurveConfig"),
    Debug(bound = "P: MontCurveConfig"),
    Hash(bound = "P: MontCurveConfig")
)]
pub struct MontgomeryAffine<P: MontCurveConfig> {
    pub x: P::BaseField,
    pub y: P::BaseField,
}

impl<P: MontCurveConfig> Display for MontgomeryAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "MontgomeryAffine(x={}, y={})", self.x, self.y)
    }
}

impl<P: MontCurveConfig> MontgomeryAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
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

impl<P: TECurveConfig> CanonicalSerialize for Projective<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = Affine::<P>::from(*self);
        aff.serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        let aff = Affine::<P>::from(*self);
        aff.serialized_size()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = Affine::<P>::from(*self);
        aff.serialize_uncompressed(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        let aff = Affine::<P>::from(*self);
        aff.uncompressed_size()
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

impl<P: TECurveConfig> CanonicalDeserialize for Projective<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = Affine::<P>::deserialize(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = Affine::<P>::deserialize_uncompressed(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = Affine::<P>::deserialize_unchecked(reader)?;
        Ok(aff.into())
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

impl<M: TECurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Projective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        Affine::from(*self).to_field_elements()
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
impl<P: TECurveConfig> Projective<P> {
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn serialize_old<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = Affine::<P>::from(*self);
        aff.serialize_old(writer)
    }

    #[allow(unused_qualifications)]
    #[inline]
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn serialize_uncompressed_old<W: Write>(
        &self,
        writer: W,
    ) -> Result<(), SerializationError> {
        let aff = Affine::<P>::from(*self);
        aff.serialize_uncompressed(writer)
    }

    #[allow(unused_qualifications)]
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn deserialize_uncompressed_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = Affine::<P>::deserialize_uncompressed(reader)?;
        Ok(aff.into())
    }
    /// This method is implemented for backwards compatibility with the old
    /// serialization format and will be deprecated and then removed in a
    /// future version.
    pub fn deserialize_old<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = Affine::<P>::deserialize_old(reader)?;
        Ok(aff.into())
    }
}

impl<P: TECurveConfig> ScalarMul for Projective<P> {
    type MulBase = Affine<P>;
}

impl<P: TECurveConfig> VariableBaseMSM for Projective<P> {}

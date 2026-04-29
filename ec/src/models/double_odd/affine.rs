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

/// Affine coordinates for a point on an elliptic curve in double-odd
/// form, over the base field `P::BaseField`.
///
/// Instead of using the (x,y)-coordinate system of the original double-odd paper (<https://doubleodd.group/doubleodd.pdf>),
/// the (e,u)-coordinate system from the follow-up paper (<https://doubleodd.group/doubleodd-jq.pdf>) was implemented.
/// This coordinate system allows for the new curve equation `e**2 = (a-4*b)*u**4 - 2a*u**2 + 1`,
/// which is of the Jacobi quartic form, allowing for faster addition/doubling formulae.
/// Additionally, these coordinates allow for more efficient en/decoding.
/// - In general: `P = (e,u) = (u**2*(x - b/x),x/y)`
/// - `P` and `P+N` are representants of the same group element.
/// - `P+N = (-e,-u)`, `-P = (e,-u)`, and `-P+N = (-e,u)`
/// - The group neutral is represented by the point at infinity `O = (1,0)` and `N = O+N = (-1,0)`
#[derive(Educe)]
#[educe(Copy, Clone, Hash)]
#[must_use]
pub struct Affine<P: DOCurveConfig> {
    #[doc(hidden)]
    pub e: P::BaseField,
    #[doc(hidden)]
    pub u: P::BaseField,
}

impl<P: DOCurveConfig> Eq for Affine<P> {}
impl<P: DOCurveConfig> PartialEq for Affine<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }
        if other.is_zero() {
            return false;
        }
        (self.e == other.e && self.u == other.u) || (self.e == -other.e && self.u == -other.u)
    }
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

    /// Returns one of the representants for the identity, namely the point-at-infinity `(1,0)`.
    ///
    /// The other representant `N=(-1,0)` of the identity could also be returned, but the
    /// implementation of formulas only requires one representant.
    pub const fn identity() -> Self {
        Self {
            e: P::BaseField::ONE,
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

    pub fn get_e_from_u(u: P::BaseField) -> Option<P::BaseField> {
        // Compute e from the curve equation `e**2 = (a-4*b)*u**4 - 2a*u**2 + 1'
        (P::get_c() * u.square().square() - (P::COEFF_A * u.square()).double() + P::BaseField::ONE)
            .sqrt()
    }

    pub fn get_es_from_u_unchecked(u: P::BaseField) -> Option<(P::BaseField, P::BaseField)> {
        let e = Self::get_e_from_u(u)?;
        let neg_e = -e;
        match e < neg_e {
            true => Some((e, neg_e)),
            false => Some((neg_e, e)),
        }
    }

    /// Checks if `self` is a valid point on the curve,
    /// using the curve equation `e**2 = (a-4*b)*u**4 - 2a*u**2 + 1`
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

    const GENERATOR: Self = P::GENERATOR;
    const ZERO: Self = Self::identity();

    fn xy(&self) -> Option<(Self::BaseField, Self::BaseField)> {
        Some((self.e, self.u))
    }

    #[inline]
    fn generator() -> Self {
        Self::GENERATOR
    }

    fn zero() -> Self {
        Self::ZERO
    }

    // Zero has two representants: 'O = (1,0)`, and `O+N = (-1,0)`.
    // These are the only two points with u=0, and is_zero assumes the point is correct,
    // so e doesn't need to be checked.
    #[inline]
    fn is_zero(&self) -> bool {
        self.u == P::BaseField::ZERO
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes(bytes)
            .and_then(|u| Self::get_point_from_u_unchecked(u, true))
    }

    fn mul_bigint(&self, by: impl AsRef<[u64]>) -> Self::Group {
        P::mul_affine(self, by.as_ref())
    }

    /// Multiplies this element by the cofactor and output the
    /// resulting projective element.
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
    /// Using Algorithm 3 from <https://doubleodd.group/doubleodd-jq.pdf>,
    /// simplified because both points are affine
    /// (n2 = 1, n5 = T1 + T2).
    fn add(self, other: T) -> Projective<P> {
        let mut copy = self.into_group();
        let other = other.borrow();
        let othert = other.u.square();
        let n1 = copy.e * other.e;
        let n3 = copy.u * other.u;
        let n4 = copy.t * othert;

        let n5 = othert + copy.t;
        let n6 = (copy.e + copy.u) * (other.e + other.u) - n1 - n3;
        let cn4 = P::get_c() * n4;
        let n7 = P::BaseField::ONE - cn4;

        let n3d = n3.double();

        copy.e = (P::BaseField::ONE + cn4) * (n1 - P::COEFF_A * n3d) + P::get_c() * n3d * n5;
        copy.z = n7.square();
        copy.t = n6.square();
        copy.u = n7 * n6;

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
    fn from(p: Projective<P>) -> Self {
        use ark_std::Zero;

        if p.is_zero() {
            Self::identity()
        } else if p.z.is_one() {
            Self::new_unchecked(p.e, p.u)
        } else {
            let z_i = p.z.inverse().unwrap();

            let u = p.u * &z_i;
            let e = p.e * &z_i;

            Self::new_unchecked(e, u)
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

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
    One, Zero,
};

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

use zeroize::Zeroize;

use super::{Projective, SWCurveConfig, SWFlags};
use crate::AffineRepr;

/// Affine coordinates for a point on an elliptic curve in short Weierstrass
/// form, over the base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: SWCurveConfig"),
    Clone(bound = "P: SWCurveConfig"),
    PartialEq(bound = "P: SWCurveConfig"),
    Eq(bound = "P: SWCurveConfig"),
    Hash(bound = "P: SWCurveConfig")
)]
#[must_use]
pub struct Affine<P: SWCurveConfig> {
    #[doc(hidden)]
    pub x: P::BaseField,
    #[doc(hidden)]
    pub y: P::BaseField,
    #[doc(hidden)]
    pub infinity: bool,
}

impl<P: SWCurveConfig> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        self.into_group() == *other
    }
}

impl<P: SWCurveConfig> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.infinity {
            true => write!(f, "infinity"),
            false => write!(f, "({}, {})", self.x, self.y),
        }
    }
}

impl<P: SWCurveConfig> Debug for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.infinity {
            true => write!(f, "infinity"),
            false => write!(f, "({}, {})", self.x, self.y),
        }
    }
}

impl<P: SWCurveConfig> Affine<P> {
    /// Constructs a group element from x and y coordinates.
    /// Performs checks to ensure that the point is on the curve and is in the right subgroup.
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        let point = Self {
            x,
            y,
            infinity: false,
        };
        assert!(point.is_on_curve());
        assert!(point.is_in_correct_subgroup_assuming_on_curve());
        point
    }

    /// Constructs a group element from x and y coordinates.
    ///
    /// # Warning
    ///
    /// Does *not* perform any checks to ensure the point is in the curve or
    /// is in the right subgroup.
    pub const fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
        Self {
            x,
            y,
            infinity: false,
        }
    }

    pub const fn identity() -> Self {
        Self {
            x: P::BaseField::ZERO,
            y: P::BaseField::ZERO,
            infinity: true,
        }
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    #[allow(dead_code)]
    pub fn get_point_from_x_unchecked(x: P::BaseField, greatest: bool) -> Option<Self> {
        Self::get_ys_from_x_unchecked(x).map(|(smaller, larger)| {
            if greatest {
                Self::new_unchecked(x, larger)
            } else {
                Self::new_unchecked(x, smaller)
            }
        })
    }

    /// Returns the two possible y-coordinates corresponding to the given x-coordinate.
    /// The corresponding points are not guaranteed to be in the prime-order subgroup,
    /// but are guaranteed to be on the curve. That is, this method returns `None`
    /// if the x-coordinate corresponds to a non-curve point.
    ///
    /// The results are sorted by lexicographical order.
    /// This means that, if `P::BaseField: PrimeField`, the results are sorted as integers.
    pub fn get_ys_from_x_unchecked(x: P::BaseField) -> Option<(P::BaseField, P::BaseField)> {
        // Compute the curve equation x^3 + Ax + B.
        // Since Rust does not optimise away additions with zero, we explicitly check
        // for that case here, and avoid multiplication by `a` if possible.
        let mut x3_plus_ax_plus_b = P::add_b(x.square() * x);
        if !P::COEFF_A.is_zero() {
            x3_plus_ax_plus_b += P::mul_by_a(x)
        };
        let y = x3_plus_ax_plus_b.sqrt()?;
        let neg_y = -y;
        match y < neg_y {
            true => Some((y, neg_y)),
            false => Some((neg_y, y)),
        }
    }

    /// Checks if `self` is a valid point on the curve.
    pub fn is_on_curve(&self) -> bool {
        if !self.infinity {
            // Rust does not optimise away addition with zero
            let mut x3b = P::add_b(self.x.square() * self.x);
            if !P::COEFF_A.is_zero() {
                x3b += P::mul_by_a(self.x);
            };
            self.y.square() == x3b
        } else {
            true
        }
    }

    pub fn to_flags(&self) -> SWFlags {
        if self.infinity {
            SWFlags::PointAtInfinity
        } else if self.y <= -self.y {
            SWFlags::YIsPositive
        } else {
            SWFlags::YIsNegative
        }
    }
}

impl<P: SWCurveConfig> Affine<P> {
    /// Checks if `self` is in the subgroup having order that equaling that of
    /// `P::ScalarField`.
    // DISCUSS Maybe these function names are too verbose?
    pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        P::is_in_correct_subgroup_assuming_on_curve(self)
    }
}

impl<P: SWCurveConfig> Zeroize for Affine<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.infinity.zeroize();
    }
}

impl<P: SWCurveConfig> Distribution<Affine<P>> for Standard {
    /// Generates a uniformly random instance of the curve.
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_x_unchecked(x, greatest) {
                return p.mul_by_cofactor();
            }
        }
    }
}

impl<P: SWCurveConfig> AffineRepr for Affine<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Group = Projective<P>;

    fn xy(&self) -> Option<(&Self::BaseField, &Self::BaseField)> {
        (!self.infinity).then(|| (&self.x, &self.y))
    }

    #[inline]
    fn generator() -> Self {
        P::GENERATOR
    }

    fn zero() -> Self {
        Self {
            x: P::BaseField::ZERO,
            y: P::BaseField::ZERO,
            infinity: true,
        }
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<SWFlags>(bytes).and_then(|(x, flags)| {
            // if x is valid and is zero and only the infinity flag is set, then parse this
            // point as infinity. For all other choices, get the original point.
            if x.is_zero() && flags.is_infinity() {
                Some(Self::identity())
            } else if let Some(y_is_positive) = flags.is_positive() {
                Self::get_point_from_x_unchecked(x, y_is_positive)
                // Unwrap is safe because it's not zero.
            } else {
                None
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

impl<P: SWCurveConfig> Neg for Affine<P> {
    type Output = Self;

    /// If `self.is_zero()`, returns `self` (`== Self::zero()`).
    /// Else, returns `(x, -y)`, where `self = (x, y)`.
    #[inline]
    fn neg(mut self) -> Self {
        self.y.neg_in_place();
        self
    }
}

impl<P: SWCurveConfig, T: Borrow<Self>> Add<T> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: T) -> Projective<P> {
        // TODO implement more efficient formulae when z1 = z2 = 1.
        let mut copy = self.into_group();
        copy += other.borrow();
        copy
    }
}

impl<P: SWCurveConfig> Add<Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: Projective<P>) -> Projective<P> {
        other + self
    }
}

impl<'a, P: SWCurveConfig> Add<&'a Projective<P>> for Affine<P> {
    type Output = Projective<P>;
    fn add(self, other: &'a Projective<P>) -> Projective<P> {
        *other + self
    }
}

impl<P: SWCurveConfig, T: Borrow<Self>> Sub<T> for Affine<P> {
    type Output = Projective<P>;
    fn sub(self, other: T) -> Projective<P> {
        let mut copy = self.into_group();
        copy -= other.borrow();
        copy
    }
}

impl<P: SWCurveConfig> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::identity()
    }
}

impl<P: SWCurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Affine<P> {
    type Output = Projective<P>;

    #[inline]
    fn mul(self, other: T) -> Self::Output {
        self.mul_bigint(other.borrow().into_bigint())
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: SWCurveConfig> From<Projective<P>> for Affine<P> {
    #[inline]
    fn from(p: Projective<P>) -> Affine<P> {
        if p.is_zero() {
            Affine::identity()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Affine::new_unchecked(p.x, p.y)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let zinv = p.z.inverse().unwrap();
            let zinv_squared = zinv.square();

            // X/Z^2
            let x = p.x * &zinv_squared;

            // Y/Z^3
            let y = p.y * &(zinv_squared * &zinv);

            Affine::new_unchecked(x, y)
        }
    }
}

impl<P: SWCurveConfig> CanonicalSerialize for Affine<P> {
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

impl<P: SWCurveConfig> Valid for Affine<P> {
    fn check(&self) -> Result<(), SerializationError> {
        if self.is_on_curve() && self.is_in_correct_subgroup_assuming_on_curve() {
            Ok(())
        } else {
            Err(SerializationError::InvalidData)
        }
    }
}

impl<P: SWCurveConfig> CanonicalDeserialize for Affine<P> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        P::deserialize_with_mode(reader, compress, validate)
    }
}

impl<M: SWCurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Affine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        let mut x = self.x.to_field_elements()?;
        let y = self.y.to_field_elements()?;
        let infinity = self.infinity.to_field_elements()?;
        x.extend_from_slice(&y);
        x.extend_from_slice(&infinity);
        Some(x)
    }
}

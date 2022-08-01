use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, SWFlags, SerializationError,
};
use ark_std::{
    borrow::Borrow,
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    io::{Read, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    vec::Vec,
};

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

use crate::{msm::VariableBaseMSM, AffineCurve, ProjectiveCurve};

use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Constants and convenience functions that collectively define the [Short Weierstrass model](https://www.hyperelliptic.org/EFD/g1p/auto-shortw.html)
/// of the curve. In this model, the curve equation is `y² = x³ + a * x + b`,
/// for constants `a` and `b`.
pub trait SWCurveConfig: super::CurveConfig {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `b` of the curve equation.
    const COEFF_B: Self::BaseField;
    /// Generator of the prime-order subgroup.
    const GENERATOR: Affine<Self>;

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

    /// Helper method for computing `elem + Self::COEFF_B`.
    ///
    /// The default implementation should be overridden only if
    /// the sum can be computed faster than standard field addition (eg: via
    /// doubling).
    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        if !Self::COEFF_B.is_zero() {
            let mut copy = *elem;
            copy += &Self::COEFF_B;
            return copy;
        }
        *elem
    }

    /// Check if the provided curve point is in the prime-order subgroup.
    ///
    /// The default implementation multiplies `item` by the order `r` of the
    /// prime-order subgroup, and checks if the result is one.
    /// Implementors can choose to override this default impl
    /// if the given curve has faster methods
    /// for performing this check (for example, via leveraging curve
    /// isomorphisms).
    fn is_in_correct_subgroup_assuming_on_curve(item: &Affine<Self>) -> bool {
        Self::mul_affine(item, Self::ScalarField::characteristic()).is_zero()
    }

    /// Performs cofactor clearing.
    /// The default method is simply to multiply by the cofactor.
    /// Some curves can implement a more efficient algorithm.
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
    /// coordinates.
    fn mul_affine(base: &Affine<Self>, scalar: &[u64]) -> Projective<Self> {
        let mut res = Projective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res.add_assign_mixed(base)
            }
        }

        res
    }
}

/// Affine coordinates for a point on an elliptic curve in short Weierstrass
/// form, over the base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: SWCurveConfig"),
    Clone(bound = "P: SWCurveConfig"),
    PartialEq(bound = "P: SWCurveConfig"),
    Eq(bound = "P: SWCurveConfig"),
    Debug(bound = "P: SWCurveConfig"),
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
        self.into_projective() == *other
    }
}

impl<P: SWCurveConfig> PartialEq<Affine<P>> for Projective<P> {
    fn eq(&self, other: &Affine<P>) -> bool {
        *self == other.into_projective()
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
    pub fn get_point_from_x(x: P::BaseField, greatest: bool) -> Option<Self> {
        // Compute x^3 + ax + b
        // Rust does not optimise away addition with zero
        let x3b = if P::COEFF_A.is_zero() {
            P::add_b(&(x.square() * &x))
        } else {
            P::add_b(&((x.square() * &x) + &P::mul_by_a(&x)))
        };

        x3b.sqrt().map(|y| {
            let negy = -y;

            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new_unchecked(x, y)
        })
    }

    /// Checks if `self` is a valid point on the curve.
    pub fn is_on_curve(&self) -> bool {
        if !self.infinity {
            // Rust does not optimise away addition with zero
            let mut x3b = P::add_b(&(self.x.square() * self.x));
            if !P::COEFF_A.is_zero() {
                x3b += &P::mul_by_a(&self.x);
            };
            self.y.square() == x3b
        } else {
            true
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

impl<P: SWCurveConfig> Zero for Affine<P> {
    /// Returns the point at infinity. Note that in affine coordinates,
    /// the point at infinity does not lie on the curve, and this is indicated
    /// by setting the `infinity` flag to true.
    #[inline]
    fn zero() -> Self {
        Self::identity()
    }

    /// Checks if `self` is the point at infinity.
    #[inline]
    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }
}

impl<P: SWCurveConfig> Add<Self> for Affine<P> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut copy = self;
        copy += &other;
        copy
    }
}

impl<'a, P: SWCurveConfig> AddAssign<&'a Self> for Affine<P> {
    fn add_assign(&mut self, other: &'a Self) {
        let mut s_proj = Projective::from(*self);
        s_proj.add_assign_mixed(other);
        *self = s_proj.into();
    }
}

impl<P: SWCurveConfig> Distribution<Affine<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_x(x, greatest) {
                return p.mul_by_cofactor();
            }
        }
    }
}

impl<P: SWCurveConfig> AffineCurve for Affine<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Projective = Projective<P>;

    fn xy(&self) -> Option<(&Self::BaseField, &Self::BaseField)> {
        (!self.infinity).then(|| (&self.x, &self.y))
    }

    #[inline]
    fn prime_subgroup_generator() -> Self {
        P::GENERATOR
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<SWFlags>(bytes).and_then(|(x, flags)| {
            // if x is valid and is zero and only the infinity flag is set, then parse this
            // point as infinity. For all other choices, get the original point.
            if x.is_zero() && flags.is_infinity() {
                Some(Self::zero())
            } else if let Some(y_is_positive) = flags.is_positive() {
                Self::get_point_from_x(x, y_is_positive)
                // Unwrap is safe because it's not zero.
            } else {
                None
            }
        })
    }

    fn mul_bigint<S: AsRef<[u64]>>(&self, by: S) -> Self::Projective {
        P::mul_affine(self, by.as_ref())
    }

    /// Multiplies this element by the cofactor and output the
    /// resulting projective element.
    #[must_use]
    fn mul_by_cofactor_to_projective(&self) -> Self::Projective {
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
        self.y = -self.y;
        self
    }
}

impl<P: SWCurveConfig> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: SWCurveConfig> core::iter::Sum<Self> for Affine<P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Projective::<P>::zero(), |sum, x| sum.add_mixed(&x))
            .into()
    }
}

impl<'a, P: SWCurveConfig> core::iter::Sum<&'a Self> for Affine<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Projective::<P>::zero(), |sum, x| sum.add_mixed(x))
            .into()
    }
}

/// Jacobian coordinates for a point on an elliptic curve in short Weierstrass
/// form, over the base field `P::BaseField`. This struct implements arithmetic
/// via the Jacobian formulae
#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: SWCurveConfig"),
    Clone(bound = "P: SWCurveConfig"),
    Debug(bound = "P: SWCurveConfig")
)]
#[must_use]
pub struct Projective<P: SWCurveConfig> {
    /// `X / Z` projection of the affine `X`
    pub x: P::BaseField,
    /// `Y / Z` projection of the affine `Y`
    pub y: P::BaseField,
    /// Projective multiplicative inverse. Will be `0` only at infinity.
    pub z: P::BaseField,
}

impl<P: SWCurveConfig> Display for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", Affine::from(*self))
    }
}

impl<P: SWCurveConfig> Eq for Projective<P> {}
impl<P: SWCurveConfig> PartialEq for Projective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // The points (X, Y, Z) and (X', Y', Z')
        // are equal when (X * Z^2) = (X' * Z'^2)
        // and (Y * Z^3) = (Y' * Z'^3).
        let z1z1 = self.z.square();
        let z2z2 = other.z.square();

        if self.x * &z2z2 != other.x * &z1z1 {
            false
        } else {
            self.y * &(z2z2 * &other.z) == other.y * &(z1z1 * &self.z)
        }
    }
}

impl<P: SWCurveConfig> Hash for Projective<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.into_affine().hash(state)
    }
}

impl<P: SWCurveConfig> Distribution<Projective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_x(x, greatest) {
                return p.mul_by_cofactor_to_projective();
            }
        }
    }
}

impl<P: SWCurveConfig> Default for Projective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: SWCurveConfig> Projective<P> {
    /// Construct a new group element without checking whether the coordinates
    /// specify a point in the subgroup.
    pub const fn new_unchecked(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        Self { x, y, z }
    }

    /// Construct a new group element in a way while enforcing that points are in
    /// the prime-order subgroup.
    pub fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        let p = Self::new_unchecked(x, y, z).into_affine();
        assert!(p.is_on_curve());
        assert!(p.is_in_correct_subgroup_assuming_on_curve());
        p.into()
    }
}

impl<P: SWCurveConfig> Zeroize for Projective<P> {
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.z.zeroize();
    }
}

impl<P: SWCurveConfig> Zero for Projective<P> {
    /// Returns the point at infinity, which always has Z = 0.
    #[inline]
    fn zero() -> Self {
        Self::new_unchecked(
            P::BaseField::one(),
            P::BaseField::one(),
            P::BaseField::zero(),
        )
    }

    /// Checks whether `self.z.is_zero()`.
    #[inline]
    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }
}

impl<P: SWCurveConfig> ProjectiveCurve for Projective<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Affine = Affine<P>;

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Affine::prime_subgroup_generator().into()
    }

    #[inline]
    fn is_normalized(&self) -> bool {
        self.is_zero() || self.z.is_one()
    }

    /// Normalizes a slice of projective elements so that
    /// conversion to affine is cheap.
    ///
    /// In more detail, this method converts a curve point in Jacobian
    /// coordinates (x, y, z) into an equivalent representation (x/z^2,
    /// y/z^3, 1).
    ///
    /// For `N = v.len()`, this costs 1 inversion + 6N field multiplications + N
    /// field squarings.
    ///
    /// (Where batch inversion comprises 3N field multiplications + 1 inversion
    /// of these operations)
    #[inline]
    fn batch_normalization(v: &mut [Self]) {
        let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
        ark_ff::batch_inversion(&mut z_s);

        // Perform affine transformations
        ark_std::cfg_iter_mut!(v)
            .zip(z_s)
            .filter(|(g, _)| !g.is_normalized())
            .for_each(|(g, z)| {
                let z2 = z.square(); // 1/z
                g.x *= &z2; // x/z^2
                g.y *= &(z2 * &z); // y/z^3
                g.z = P::BaseField::one(); // z = 1
            });
    }

    /// Sets `self = 2 * self`. Note that Jacobian formulae are incomplete, and
    /// so doubling cannot be computed as `self + self`. Instead, this
    /// implementation uses the following specialized doubling formulae:
    /// * [`P::A` is zero](http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l)
    /// * [`P::A` is not zero](https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl)
    fn double_in_place(&mut self) -> &mut Self {
        if self.is_zero() {
            return self;
        }

        if P::COEFF_A.is_zero() {
            // A = X1^2
            let mut a = self.x.square();

            // B = Y1^2
            let b = self.y.square();

            // C = B^2
            let mut c = b.square();

            // D = 2*((X1+B)2-A-C)
            let d = ((self.x + &b).square() - &a - &c).double();

            // E = 3*A
            let e = a + &*a.double_in_place();

            // F = E^2
            let f = e.square();

            // Z3 = 2*Y1*Z1
            self.z *= &self.y;
            self.z.double_in_place();

            // X3 = F-2*D
            self.x = f - &d - &d;

            // Y3 = E*(D-X3)-8*C
            self.y = (d - &self.x) * &e - &*c.double_in_place().double_in_place().double_in_place();
            self
        } else {
            // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            // XX = X1^2
            let xx = self.x.square();

            // YY = Y1^2
            let yy = self.y.square();

            // YYYY = YY^2
            let mut yyyy = yy.square();

            // ZZ = Z1^2
            let zz = self.z.square();

            // S = 2*((X1+YY)^2-XX-YYYY)
            let s = ((self.x + &yy).square() - &xx - &yyyy).double();

            // M = 3*XX+a*ZZ^2
            let m = xx + &xx + &xx + &P::mul_by_a(&zz.square());

            // T = M^2-2*S
            let t = m.square() - &s.double();

            // X3 = T
            self.x = t;
            // Y3 = M*(S-T)-8*YYYY
            let old_y = self.y;
            self.y = m * &(s - &t) - &*yyyy.double_in_place().double_in_place().double_in_place();
            // Z3 = (Y1+Z1)^2-YY-ZZ
            self.z = (old_y + &self.z).square() - &yy - &zz;
            self
        }
    }

    /// When `other.is_normalized()` (i.e., `other.z == 1`), we can use a more
    /// efficient [formula](http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl)
    /// to compute `self + other`.
    fn add_assign_mixed(&mut self, other: &Affine<P>) {
        match other.is_zero() {
            true => {},
            false => {
                if self.is_zero() {
                    self.x = other.x;
                    self.y = other.y;
                    self.z = P::BaseField::one();
                    return;
                }

                // Z1Z1 = Z1^2
                let z1z1 = self.z.square();

                // U2 = X2*Z1Z1
                let u2 = z1z1 * other.x;

                // S2 = Y2*Z1*Z1Z1
                let s2 = (self.z * other.y) * &z1z1;

                if self.x == u2 && self.y == s2 {
                    // The two points are equal, so we double.
                    self.double_in_place();
                } else {
                    // If we're adding -a and a together, self.z becomes zero as H becomes zero.

                    // H = U2-X1
                    let h = u2 - &self.x;

                    // HH = H^2
                    let hh = h.square();

                    // I = 4*HH
                    let mut i = hh;
                    i.double_in_place().double_in_place();

                    // J = H*I
                    let mut j = h * &i;

                    // r = 2*(S2-Y1)
                    let r = (s2 - &self.y).double();

                    // V = X1*I
                    let v = self.x * &i;

                    // X3 = r^2 - J - 2*V
                    self.x = r.square();
                    self.x -= &j;
                    self.x -= &v;
                    self.x -= &v;

                    // Y3 = r*(V-X3)-2*Y1*J
                    j *= &self.y; // J = 2*Y1*J
                    j.double_in_place();
                    self.y = v - &self.x;
                    self.y *= &r;
                    self.y -= &j;

                    // Z3 = (Z1+H)^2-Z1Z1-HH
                    self.z += &h;
                    self.z.square_in_place();
                    self.z -= &z1z1;
                    self.z -= &hh;
                }
            },
        }
    }

    #[inline]
    fn mul_bigint<S: AsRef<[u64]>>(self, other: S) -> Self {
        P::mul_projective(&self, other.as_ref())
    }
}

impl<P: SWCurveConfig> Neg for Projective<P> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.y = -self.y;
        self
    }
}

ark_ff::impl_additive_ops_from_ref!(Projective, SWCurveConfig);

impl<'a, P: SWCurveConfig> Add<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: SWCurveConfig> AddAssign<&'a Self> for Projective<P> {
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square();

        // Z2Z2 = Z2^2
        let z2z2 = other.z.square();

        // U1 = X1*Z2Z2
        let u1 = self.x * &z2z2;

        // U2 = X2*Z1Z1
        let u2 = other.x * &z1z1;

        // S1 = Y1*Z2*Z2Z2
        let s1 = self.y * &other.z * &z2z2;

        // S2 = Y2*Z1*Z1Z1
        let s2 = other.y * &self.z * &z1z1;

        if u1 == u2 && s1 == s2 {
            // The two points are equal, so we double.
            self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-U1
            let h = u2 - &u1;

            // I = (2*H)^2
            let i = (h.double()).square();

            // J = H*I
            let j = h * &i;

            // r = 2*(S2-S1)
            let r = (s2 - &s1).double();

            // V = U1*I
            let v = u1 * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square() - &j - &(v.double());

            // Y3 = r*(V - X3) - 2*S1*J
            self.y = r * &(v - &self.x) - &*(s1 * &j).double_in_place();

            // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
            self.z = ((self.z + &other.z).square() - &z1z1 - &z2z2) * &h;
        }
    }
}

impl<'a, P: SWCurveConfig> Sub<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

impl<'a, P: SWCurveConfig> SubAssign<&'a Self> for Projective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: SWCurveConfig, T: Borrow<P::ScalarField>> MulAssign<T> for Projective<P> {
    fn mul_assign(&mut self, other: T) {
        *self = self.mul_bigint(other.borrow().into_bigint())
    }
}

impl<'a, P: SWCurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Projective<P> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: T) -> Self {
        self *= other;
        self
    }
}

// The affine point X, Y is represented in the Jacobian
// coordinates with Z = 1.
impl<P: SWCurveConfig> From<Affine<P>> for Projective<P> {
    #[inline]
    fn from(p: Affine<P>) -> Projective<P> {
        match p.infinity {
            true => Self::zero(),
            false => Self {
                x: p.x,
                y: p.y,
                z: P::BaseField::one(),
            },
        }
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: SWCurveConfig> From<Projective<P>> for Affine<P> {
    #[inline]
    fn from(p: Projective<P>) -> Affine<P> {
        if p.is_zero() {
            Affine::zero()
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
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let (x, flags) = match self.infinity {
            true => (P::BaseField::zero(), SWFlags::infinity()),
            false => (self.x, SWFlags::from_y_sign(self.y > -self.y)),
        };
        x.serialize_with_flags(writer, flags)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let (x, y, flags) = match self.infinity {
            true => (
                P::BaseField::zero(),
                P::BaseField::zero(),
                SWFlags::infinity(),
            ),
            false => (self.x, self.y, SWFlags::from_y_sign(self.y > -self.y)),
        };
        x.serialize(&mut writer)?;
        y.serialize_with_flags(&mut writer, flags)?;
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        // The size of the serialization is independent of the values
        // of `x` and `y`, and depends only on the size of the modulus.
        P::BaseField::zero().serialized_size()
            + P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
    }
}

impl<P: SWCurveConfig> CanonicalSerialize for Projective<P> {
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

impl<P: SWCurveConfig> CanonicalDeserialize for Affine<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
        if flags.is_infinity() {
            Ok(Self::zero())
        } else {
            let p = Affine::<P>::get_point_from_x(x, flags.is_positive().unwrap())
                .ok_or(SerializationError::InvalidData)?;
            if !p.is_in_correct_subgroup_assuming_on_curve() {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(
        reader: R,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;

        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let (y, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        match flags.is_infinity() {
            true => Ok(Self::zero()),
            false => Ok(Self::new_unchecked(x, y)),
        }
    }
}

impl<P: SWCurveConfig> CanonicalDeserialize for Projective<P> {
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

impl<M: SWCurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Projective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        Affine::from(*self).to_field_elements()
    }
}

impl<P: SWCurveConfig> VariableBaseMSM for Projective<P> {
    type MSMBase = Affine<P>;

    type Scalar = <Self as ProjectiveCurve>::ScalarField;

    #[inline]
    fn _double_in_place(&mut self) -> &mut Self {
        self.double_in_place()
    }

    #[inline]
    fn _add_assign_mixed(&mut self, other: &Self::MSMBase) {
        self.add_assign_mixed(other)
    }
}

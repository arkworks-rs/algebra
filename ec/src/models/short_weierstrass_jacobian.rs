use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, SWFlags, SerializationError,
};
use ark_std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Write},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
};

use ark_ff::{
    fields::{BitIteratorBE, Field, PrimeField, SquareRootField},
    ToConstraintField, UniformRand,
};

use crate::{models::SWModelParameters as Parameters, CurveGroup, Group};

use num_traits::{One, Zero};
use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub use affine::*;
pub use projective::*;

mod affine {
    use super::*;
    /// SWAffine coordinates for a point on an elliptic curve in short Weierstrass form,
    /// over the base field `P::BaseField`.
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
    pub struct SWAffine<P: Parameters> {
        pub(super) x: P::BaseField,
        pub(super) y: P::BaseField,
        infinity: bool,
        #[derivative(Debug = "ignore")]
        _params: PhantomData<P>,
    }

    impl<P: Parameters> PartialEq<SWProjective<P>> for SWAffine<P> {
        fn eq(&self, other: &SWProjective<P>) -> bool {
            SWProjective::from(*self) == *other
        }
    }

    impl<P: Parameters> PartialEq<SWAffine<P>> for SWProjective<P> {
        fn eq(&self, other: &SWAffine<P>) -> bool {
            *self == Self::from(*other)
        }
    }

    impl<P: Parameters> Display for SWAffine<P> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if self.infinity {
                write!(f, "SWAffine(Infinity)")
            } else {
                write!(f, "SWAffine(x={}, y={})", self.x, self.y)
            }
        }
    }

    impl<P: Parameters> SWAffine<P> {
        /// Construct a new point from the provided coordinates.
        /// This method checks that the resulting point is in the prime order subgroup.
        ///
        /// Note that this method cannot be used to construct the point at infinity;
        /// to do that, simply invoke `Self::zero()`.
        pub fn new(x: P::BaseField, y: P::BaseField) -> Option<Self> {
            let result = Self::new_unchecked(x, y);
            if !(result.is_on_curve() && result.is_in_correct_subgroup_assuming_on_curve()) {
                None
            } else {
                Some(result)
            }
        }

        /// Construct a new point from the provided coordinates.
        /// This method *does not* check that the resulting point is in the prime order subgroup; if you want that, invoke `Self::new`.
        ///
        /// Note that this method cannot be used to construct the point at infinity;
        /// to do that, simply invoke `Self::zero()`.
        pub fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
            Self {
                x,
                y,
                infinity: false,
                _params: PhantomData,
            }
        }

        /// Returns the x-coordinate of this curve point.
        #[inline(always)]
        pub fn x(&self) -> P::BaseField {
            self.x
        }

        /// Returns the y-coordinate of this curve point.
        #[inline(always)]
        pub fn y(&self) -> P::BaseField {
            self.y
        }

        /// Is self the point at infinity? This returns the same result as `Self::is_zero()`.
        #[inline(always)]
        pub fn is_zero(&self) -> bool {
            self.infinity
        }

        /// Returns the point at infinity. Note that in affine coordinates,
        /// the point at infinity does not lie on the curve.
        #[inline]
        pub fn zero() -> Self {
            Self {
                x: P::BaseField::zero(),
                y: P::BaseField::one(),
                infinity: true,
                _params: PhantomData,
            }
        }

        /// Multiply [`self`] by the cofactor of the curve, [`P::COFACTOR`].
        pub fn scale_by_cofactor(&self) -> SWProjective<P> {
            let cofactor = BitIteratorBE::without_leading_zeros(P::COFACTOR);
            self.mul_bits(cofactor)
        }

        /// Multiplies `self` by the scalar represented by `bits`. `bits` must be a big-endian
        /// bit-wise decomposition of the scalar.
        pub(crate) fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> SWProjective<P> {
            let mut res = SWProjective::zero();
            // Skip leading zeros.
            for i in bits.skip_while(|b| !b) {
                res.double_in_place();
                if i {
                    res.add_unique_in_place(&self)
                }
            }
            res
        }

        /// Attempts to construct an affine point given an x-coordinate. The
        /// point is not guaranteed to be in the prime order subgroup.
        ///
        /// If and only if [`greatest`] is set will the lexicographically
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

        /// Checks if [`self`] is a valid point on the curve.
        pub fn is_on_curve(&self) -> bool {
            if self.is_zero() {
                true
            } else {
                // Check that the point is on the curve
                let y2 = self.y.square();
                // Rust does not optimise away addition with zero
                let x3b = if P::COEFF_A.is_zero() {
                    P::add_b(&(self.x.square() * &self.x))
                } else {
                    P::add_b(&((self.x.square() * &self.x) + &P::mul_by_a(&self.x)))
                };
                y2 == x3b
            }
        }

        /// Checks if [`self`] is in the subgroup having order that equaling that of
        /// [`P::ScalarField`].
        pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
            self.mul_bits(BitIteratorBE::new(P::ScalarField::characteristic()))
                .is_zero()
        }

        /// Return the generator of the prime order subgroup.
        #[inline]
        pub fn generator() -> Self {
            Self::new_unchecked(P::AFFINE_GENERATOR_COEFFS.0, P::AFFINE_GENERATOR_COEFFS.1)
        }

        #[inline]
        pub fn mul_by_cofactor_to_projective(&self) -> SWProjective<P> {
            self.scale_by_cofactor()
        }

        pub fn mul_by_cofactor_inv(&self) -> Self {
            self.mul(P::COFACTOR_INV.into()).into()
        }
    }

    impl<P: Parameters> Zeroize for SWAffine<P> {
        // The phantom data does not contain element-specific data
        // and thus does not need to be zeroized.
        fn zeroize(&mut self) {
            self.x.zeroize();
            self.y.zeroize();
            self.infinity.zeroize();
        }
    }

    impl<P: Parameters> Mul<<P::ScalarField as PrimeField>::BigInt> for SWAffine<P> {
        type Output = SWProjective<P>;

        #[inline]
        fn mul(self, by: <P::ScalarField as PrimeField>::BigInt) -> SWProjective<P> {
            let bits = BitIteratorBE::without_leading_zeros(by);
            self.mul_bits(bits)
        }
    }

    impl<P: Parameters> Distribution<SWAffine<P>> for Standard {
        #[inline]
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> SWAffine<P> {
            loop {
                let x = P::BaseField::rand(rng);
                let greatest = rng.gen();
                if let Some(p) = SWAffine::get_point_from_x(x, greatest) {
                    return p.scale_by_cofactor().into();
                }
            }
        }
    }

    impl<P: Parameters> Neg for SWAffine<P> {
        type Output = Self;

        /// If `self.is_zero()`, returns `self` (`== Self::zero()`).
        /// Else, returns `(x, -y)`, where `self = (x, y)`.
        #[inline]
        fn neg(mut self) -> Self {
            if !self.is_zero() {
                self.y = -self.y;
            }
            self
        }
    }

    impl<P: Parameters> Default for SWAffine<P> {
        #[inline]
        fn default() -> Self {
            Self::zero()
        }
    }

    impl<P: Parameters> core::iter::Sum<Self> for SWAffine<P> {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.fold(SWProjective::<P>::zero(), |sum, x| sum.add_unique(&x))
                .into()
        }
    }

    impl<'a, P: Parameters> core::iter::Sum<&'a Self> for SWAffine<P> {
        fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
            iter.fold(SWProjective::<P>::zero(), |sum, x| sum.add_unique(x))
                .into()
        }
    }

    impl<P: Parameters> core::iter::Sum<SWProjective<P>> for SWAffine<P> {
        fn sum<I: Iterator<Item = SWProjective<P>>>(iter: I) -> Self {
            iter.map(SWProjective::from).sum::<SWProjective<P>>().into()
        }
    }

    impl<'a, P: Parameters> core::iter::Sum<&'a SWProjective<P>> for SWAffine<P> {
        fn sum<I: Iterator<Item = &'a SWProjective<P>>>(iter: I) -> Self {
            iter.copied()
                .map(SWProjective::from)
                .sum::<SWProjective<P>>()
                .into()
        }
    }

    impl<P: Parameters> CanonicalSerialize for SWAffine<P> {
        #[allow(unused_qualifications)]
        #[inline]
        fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            if self.is_zero() {
                let flags = SWFlags::infinity();
                // Serialize 0.
                P::BaseField::zero().serialize_with_flags(writer, flags)
            } else {
                let flags = SWFlags::from_y_sign(self.y > -self.y);
                self.x.serialize_with_flags(writer, flags)
            }
        }

        #[inline]
        fn serialized_size(&self) -> usize {
            P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
        }

        #[allow(unused_qualifications)]
        #[inline]
        fn serialize_uncompressed<W: Write>(
            &self,
            mut writer: W,
        ) -> Result<(), SerializationError> {
            let flags = if self.is_zero() {
                SWFlags::infinity()
            } else {
                SWFlags::default()
            };
            self.x.serialize(&mut writer)?;
            self.y.serialize_with_flags(&mut writer, flags)?;
            Ok(())
        }

        #[inline]
        fn uncompressed_size(&self) -> usize {
            self.x.serialized_size() + self.y.serialized_size_with_flags::<SWFlags>()
        }
    }

    impl<P: Parameters> CanonicalDeserialize for SWAffine<P> {
        #[allow(unused_qualifications)]
        fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let (x, flags): (P::BaseField, SWFlags) =
                CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
            if flags.is_infinity() {
                Ok(Self::zero())
            } else {
                let p = SWAffine::<P>::get_point_from_x(x, flags.is_positive().unwrap())
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

            if !(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()) {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }

        #[allow(unused_qualifications)]
        fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
            let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
            let (y, flags): (P::BaseField, SWFlags) =
                CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
            if flags.is_infinity() {
                Ok(Self::zero())
            } else {
                Ok(Self::new_unchecked(x, y))
            }
        }
    }
    impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for SWAffine<M>
    where
        M::BaseField: ToConstraintField<ConstraintF>,
    {
        #[inline]
        fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
            let mut x_fe = self.x.to_field_elements()?;
            let y_fe = self.y.to_field_elements()?;
            let infinity_fe = self.infinity.to_field_elements()?;
            x_fe.extend_from_slice(&y_fe);
            x_fe.extend_from_slice(&infinity_fe);
            Some(x_fe)
        }
    }
}

mod projective {
    use super::*;

    /// Jacobian coordinates for a point on an elliptic curve in short Weierstrass form,
    /// over the base field `P::BaseField`. This struct implements arithmetic
    /// via the Jacobian formulae
    #[derive(Derivative)]
    #[derivative(
        Copy(bound = "P: Parameters"),
        Clone(bound = "P: Parameters"),
        Debug(bound = "P: Parameters"),
    )]
    #[must_use]
    pub struct SWProjective<P: Parameters> {
        x: P::BaseField,
        y: P::BaseField,
        z: P::BaseField,
        #[derivative(Debug = "ignore")]
        _params: PhantomData<P>,
    }

    impl<P: Parameters> Hash for SWProjective<P> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            SWAffine::from(*self).hash(state)
        }
    }

    impl<P: Parameters> Display for SWProjective<P> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}", SWAffine::from(*self))
        }
    }

    impl<P: Parameters> Eq for SWProjective<P> {}
    impl<P: Parameters> PartialEq for SWProjective<P> {
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

    impl<P: Parameters> Distribution<SWProjective<P>> for Standard {
        #[inline]
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> SWProjective<P> {
            loop {
                let x = P::BaseField::rand(rng);
                let greatest = rng.gen();

                if let Some(p) = SWAffine::get_point_from_x(x, greatest) {
                    return p.scale_by_cofactor().into();
                }
            }
        }
    }

    impl<P: Parameters> Default for SWProjective<P> {
        #[inline]
        fn default() -> Self {
            Self::zero()
        }
    }

    impl<P: Parameters> SWProjective<P> {
        /// Construct a [`Self`] *without* validating that the coordinates form a valid point.
        pub(crate) fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
            Self {
                x,
                y,
                z,
                _params: PhantomData,
            }
        }

        /// Can [`self`] be converted to [`SWAffine`] cheaply?
        #[inline]
        pub fn is_normalized(&self) -> bool {
            self.is_zero() || self.z.is_one()
        }
    }

    impl<P: Parameters> Zeroize for SWProjective<P> {
        fn zeroize(&mut self) {
            // `PhantomData` does not contain any data and thus does not need to be zeroized.
            self.x.zeroize();
            self.y.zeroize();
            self.z.zeroize();
        }
    }

    impl<P: Parameters> Zero for SWProjective<P> {
        /// Returns the point at infinity, which always has Z = 0.
        #[inline]
        fn zero() -> Self {
            Self::new(
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

    impl<P: Parameters> CurveGroup for SWProjective<P> {
        const COFACTOR: &'static [u64] = P::COFACTOR;

        const COFACTOR_INVERSE: Self::ScalarField = P::COFACTOR_INV;

        type BaseField = P::BaseField;
    }

    impl<P: Parameters> Group for SWProjective<P> {
        type ScalarField = P::ScalarField;
        type UniqueRepr = SWAffine<P>;

        #[inline]
        fn generator() -> Self::UniqueRepr {
            SWAffine::generator()
        }

        /// Converts [`self`] into the unique representation.
        fn to_unique(&self) -> Self::UniqueRepr {
            (*self).into()
        }

        /// Canonicalize a slice of projective elements into their unique representation.
        ///
        /// In more detail, this method converts a curve point in Jacobian coordinates
        /// (x, y, z) into an equivalent representation (x/z^2, y/z^3, 1).
        ///
        /// For `N = v.len()`, this costs 1 inversion + 6N field multiplications + N field squarings.
        ///
        /// (Where batch inversion comprises 3N field multiplications + 1 inversion of these operations)
        fn batch_to_unique(v: &[Self]) -> Vec<Self::UniqueRepr> {
            let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
            ark_ff::batch_inversion(&mut z_s);

            // Perform affine transformations
            ark_std::cfg_iter!(v)
                .zip(z_s)
                .filter(|(g, _)| !g.is_normalized())
                .map(|(g, z)| {
                    let mut g = *g;
                    let z2 = z.square(); // 1/z
                    g.x *= &z2; // x/z^2
                    g.y *= &(z2 * &z); // y/z^3
                    g.z = P::BaseField::one(); // z = 1
                    g.to_unique()
                })
                .collect()
        }

        /// Sets `self = 2 * self`. Note that Jacobian formulae are incomplete, and
        /// so doubling cannot be computed as `self + self`. Instead, this implementation
        /// uses the following specialized doubling formulae:
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
                self.y =
                    (d - &self.x) * &e - &*c.double_in_place().double_in_place().double_in_place();
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
                self.y =
                    m * &(s - &t) - &*yyyy.double_in_place().double_in_place().double_in_place();
                // Z3 = (Y1+Z1)^2-YY-ZZ
                self.z = (old_y + &self.z).square() - &yy - &zz;
                self
            }
        }

        /// Add an affine element to `self` in place using the more efficient [formula](http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl)
        fn add_unique_in_place(&mut self, other: &SWAffine<P>) {
            if other.is_zero() {
                return;
            }

            if self.is_zero() {
                self.x = other.x;
                self.y = other.y;
                self.z = P::BaseField::one();
                return;
            }

            // Z1Z1 = Z1^2
            let z1z1 = self.z.square();

            // U2 = X2*Z1Z1
            let u2 = other.x * &z1z1;

            // S2 = Y2*Z1*Z1Z1
            let s2 = (other.y * &self.z) * &z1z1;

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
        }
    }

    impl<P: Parameters> Neg for SWProjective<P> {
        type Output = Self;

        #[inline]
        fn neg(self) -> Self {
            if !self.is_zero() {
                Self::new(self.x, -self.y, self.z)
            } else {
                self
            }
        }
    }

    ark_ff::impl_additive_ops_from_ref!(SWProjective, Parameters);

    impl<'a, P: Parameters> Add<&'a Self> for SWProjective<P> {
        type Output = Self;

        #[inline]
        fn add(mut self, other: &'a Self) -> Self {
            self += other;
            self
        }
    }

    impl<'a, P: Parameters> AddAssign<&'a Self> for SWProjective<P> {
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

    impl<'a, P: Parameters> Sub<&'a Self> for SWProjective<P> {
        type Output = Self;

        #[inline]
        fn sub(mut self, other: &'a Self) -> Self {
            self -= other;
            self
        }
    }

    impl<'a, P: Parameters> SubAssign<&'a Self> for SWProjective<P> {
        fn sub_assign(&mut self, other: &'a Self) {
            *self += &(-(*other));
        }
    }

    impl<P: Parameters> MulAssign<P::ScalarField> for SWProjective<P> {
        fn mul_assign(&mut self, other: P::ScalarField) {
            *self = self.mul(other.into_repr())
        }
    }

    // The affine point X, Y is represented in the Jacobian
    // coordinates with Z = 1.
    impl<P: Parameters> From<SWAffine<P>> for SWProjective<P> {
        #[inline]
        fn from(p: SWAffine<P>) -> SWProjective<P> {
            if p.is_zero() {
                Self::zero()
            } else {
                Self::new(p.x, p.y, P::BaseField::one())
            }
        }
    }

    // The projective point X, Y, Z is represented in the affine
    // coordinates as X/Z^2, Y/Z^3.
    impl<P: Parameters> From<SWProjective<P>> for SWAffine<P> {
        #[inline]
        fn from(p: SWProjective<P>) -> SWAffine<P> {
            if p.is_zero() {
                SWAffine::zero()
            } else if p.z.is_one() {
                // If Z is one, the point is already normalized.
                SWAffine::new_unchecked(p.x, p.y)
            } else {
                // Z is nonzero, so it must have an inverse in a field.
                let zinv = p.z.inverse().unwrap();
                let zinv_squared = zinv.square();

                // X/Z^2
                let x = p.x * &zinv_squared;

                // Y/Z^3
                let y = p.y * &(zinv_squared * &zinv);

                SWAffine::new_unchecked(x, y)
            }
        }
    }

    impl<P: Parameters> CanonicalSerialize for SWProjective<P> {
        #[allow(unused_qualifications)]
        #[inline]
        fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            let aff = SWAffine::<P>::from(self.clone());
            aff.serialize(writer)
        }

        #[inline]
        fn serialized_size(&self) -> usize {
            let aff = SWAffine::<P>::from(self.clone());
            aff.serialized_size()
        }

        #[allow(unused_qualifications)]
        #[inline]
        fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            let aff = SWAffine::<P>::from(self.clone());
            aff.serialize_uncompressed(writer)
        }

        #[inline]
        fn uncompressed_size(&self) -> usize {
            let aff = SWAffine::<P>::from(self.clone());
            aff.uncompressed_size()
        }
    }

    impl<P: Parameters> CanonicalDeserialize for SWProjective<P> {
        #[allow(unused_qualifications)]
        fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = SWAffine::<P>::deserialize(reader)?;
            Ok(aff.into())
        }

        #[allow(unused_qualifications)]
        fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = SWAffine::<P>::deserialize_uncompressed(reader)?;
            Ok(aff.into())
        }

        #[allow(unused_qualifications)]
        fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = SWAffine::<P>::deserialize_unchecked(reader)?;
            Ok(aff.into())
        }
    }

    impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for SWProjective<M>
    where
        M::BaseField: ToConstraintField<ConstraintF>,
    {
        #[inline]
        fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
            SWAffine::from(*self).to_field_elements()
        }
    }
}

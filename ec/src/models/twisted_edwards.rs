use crate::{
    models::{MontgomeryModelParameters as MontgomeryParameters, TEModelParameters as Parameters},
    CurveGroup, Group,
};
use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, EdwardsFlags, SerializationError,
};
use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use ark_std::{
    fmt::{Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    io::{Read, Write},
    marker::PhantomData,
    ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign},
    vec::Vec,
};
use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_ff::{
    fields::{BitIteratorBE, Field, PrimeField, SquareRootField},
    ToConstraintField, UniformRand,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub use affine::*;
pub use projective::*;

pub use montgomery_affine::*;

mod affine {
    use crate::GroupNormalForm;

    use super::*;
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
    pub struct TEAffine<P: Parameters> {
        pub(super) x: P::BaseField,
        pub(super) y: P::BaseField,
        #[derivative(Debug = "ignore")]
        _params: PhantomData<P>,
    }

    impl<P: Parameters> Display for TEAffine<P> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "TEAffine(x={}, y={})", self.x, self.y)
        }
    }

    impl<P: Parameters> TEAffine<P> {
        /// Construct a new point from the provided coordinates.
        ///
        /// This method checks that the resulting point is in the prime order subgroup.
        pub fn new(x: P::BaseField, y: P::BaseField) -> Option<Self> {
            let result = Self::new_unchecked(x, y);
            if !(result.is_on_curve() && result.is_in_correct_subgroup_assuming_on_curve()) {
                None
            } else {
                Some(result)
            }
        }

        /// Construct a new point from the provided coordinates.
        ///
        /// This method *does not* check that the resulting point is in the prime order subgroup.
        pub fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
            Self {
                x,
                y,
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

        #[must_use]
        pub fn scale_by_cofactor(&self) -> TEProjective<P> {
            self.mul_bits(BitIteratorBE::new(P::COFACTOR))
        }

        /// Multiplies `self` by the scalar represented by `bits`. `bits` must be a big-endian
        /// bit-wise decomposition of the scalar.
        pub(crate) fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> TEProjective<P> {
            let mut res = TEProjective::zero();
            for i in bits.skip_while(|b| !b) {
                res.double_in_place();
                if i {
                    res.add_normal_in_place(&self)
                }
            }
            res
        }

        /// Attempts to construct an affine point given an x-coordinate. The
        /// point is not guaranteed to be in the prime order subgroup.
        ///
        /// If and only if `greatest` is set will the lexicographically
        /// largest y-coordinate be selected.
        #[allow(dead_code)]
        pub fn get_point_from_x(x: P::BaseField, greatest: bool) -> Option<Self> {
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

        /// Checks that the current point is on the elliptic curve.
        pub fn is_on_curve(&self) -> bool {
            let x2 = self.x.square();
            let y2 = self.y.square();

            let lhs = y2 + &P::mul_by_a(&x2);
            let rhs = P::BaseField::one() + &(P::COEFF_D * &(x2 * &y2));

            lhs == rhs
        }

        /// Checks that the current point is in the prime order subgroup given
        /// the point on the curve.
        pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
            self.mul_bits(BitIteratorBE::new(P::ScalarField::characteristic()))
                .is_zero()
        }

        pub fn zero() -> Self {
            Self::new_unchecked(P::BaseField::zero(), P::BaseField::one())
        }

        pub fn is_zero(&self) -> bool {
            self.x.is_zero() & self.y.is_one()
        }

        /// Return the generator of this prime order group.
        #[inline]
        pub fn generator() -> Self {
            Self::new_unchecked(P::AFFINE_GENERATOR_COEFFS.0, P::AFFINE_GENERATOR_COEFFS.1)
        }

        #[inline]
        pub fn mul_by_cofactor_to_projective(&self) -> TEProjective<P> {
            self.scale_by_cofactor()
        }

        pub fn mul_by_cofactor_inv(&self) -> Self {
            self.mul(P::COFACTOR_INV).into()
        }
    }

    impl<P: Parameters> GroupNormalForm for TEAffine<P> {
        type G = TEProjective<P>;
    }

    impl<P: Parameters> Zeroize for TEAffine<P> {
        // The phantom data does not contain element-specific data
        // and thus does not need to be zeroized.
        fn zeroize(&mut self) {
            self.x.zeroize();
            self.y.zeroize();
        }
    }

    impl<P: Parameters> Neg for TEAffine<P> {
        type Output = Self;

        fn neg(self) -> Self {
            Self::new_unchecked(-self.x, self.y)
        }
    }

    impl<P: Parameters> core::iter::Sum<Self> for TEAffine<P> {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.fold(TEProjective::<P>::zero(), |sum, x| sum.add_normal(&x))
                .into()
        }
    }

    impl<'a, P: Parameters> core::iter::Sum<&'a Self> for TEAffine<P> {
        fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
            iter.fold(TEProjective::<P>::zero(), |sum, x| sum.add_normal(x))
                .into()
        }
    }

    impl<P: Parameters> core::iter::Sum<TEProjective<P>> for TEAffine<P> {
        fn sum<I: Iterator<Item = TEProjective<P>>>(iter: I) -> Self {
            iter.map(TEProjective::from).sum::<TEProjective<P>>().into()
        }
    }

    impl<'a, P: Parameters> core::iter::Sum<&'a TEProjective<P>> for TEAffine<P> {
        fn sum<I: Iterator<Item = &'a TEProjective<P>>>(iter: I) -> Self {
            iter.copied()
                .map(TEProjective::from)
                .sum::<TEProjective<P>>()
                .into()
        }
    }

    impl<P: Parameters> Default for TEAffine<P> {
        #[inline]
        fn default() -> Self {
            Self::zero()
        }
    }

    impl<P: Parameters> Distribution<TEAffine<P>> for Standard {
        #[inline]
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> TEAffine<P> {
            loop {
                let x = P::BaseField::rand(rng);
                let greatest = rng.gen();

                if let Some(p) = TEAffine::get_point_from_x(x, greatest) {
                    return p.scale_by_cofactor().into();
                }
            }
        }
    }

    impl<P: Parameters> CanonicalSerialize for TEAffine<P> {
        #[allow(unused_qualifications)]
        #[inline]
        fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            if self.is_zero() {
                let flags = EdwardsFlags::default();
                // Serialize 0.
                P::BaseField::zero().serialize_with_flags(writer, flags)
            } else {
                let flags = EdwardsFlags::from_y_sign(self.y > -self.y);
                self.x.serialize_with_flags(writer, flags)
            }
        }

        #[inline]
        fn serialized_size(&self) -> usize {
            P::BaseField::zero().serialized_size_with_flags::<EdwardsFlags>()
        }

        #[allow(unused_qualifications)]
        #[inline]
        fn serialize_uncompressed<W: Write>(
            &self,
            mut writer: W,
        ) -> Result<(), SerializationError> {
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

    impl<P: Parameters> CanonicalDeserialize for TEAffine<P> {
        #[allow(unused_qualifications)]
        fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
            let (x, flags): (P::BaseField, EdwardsFlags) =
                CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
            if x == P::BaseField::zero() {
                Ok(Self::zero())
            } else {
                let p = TEAffine::<P>::get_point_from_x(x, flags.is_positive())
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

            if !(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve()) {
                return Err(SerializationError::InvalidData);
            }
            Ok(p)
        }

        #[allow(unused_qualifications)]
        fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
            let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
            let y: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;

            let p = TEAffine::<P>::new_unchecked(x, y);
            Ok(p)
        }
    }

    impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for TEAffine<M>
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
}

//////////////////////////////////////////////////////////////////////////////

mod projective {
    use super::*;
    /// `TEProjective` implements Extended Twisted Edwards Coordinates
    /// as described in [\[HKCD08\]](https://eprint.iacr.org/2008/522.pdf).
    ///
    /// This implementation uses the unified addition formulae from that paper (see Section 3.1).
    #[derive(Derivative)]
    #[derivative(
        Copy(bound = "P: Parameters"),
        Clone(bound = "P: Parameters"),
        Eq(bound = "P: Parameters"),
        Debug(bound = "P: Parameters")
    )]
    #[must_use]
    pub struct TEProjective<P: Parameters> {
        x: P::BaseField,
        y: P::BaseField,
        t: P::BaseField,
        z: P::BaseField,
        #[derivative(Debug = "ignore")]
        _params: PhantomData<P>,
    }

    impl<P: Parameters> Hash for TEProjective<P> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            TEAffine::from(*self).hash(state)
        }
    }

    impl<P: Parameters> PartialEq<TEProjective<P>> for TEAffine<P> {
        fn eq(&self, other: &TEProjective<P>) -> bool {
            TEProjective::from(*self) == *other
        }
    }

    impl<P: Parameters> PartialEq<TEAffine<P>> for TEProjective<P> {
        fn eq(&self, other: &TEAffine<P>) -> bool {
            *self == TEProjective::from(*other)
        }
    }

    impl<P: Parameters> Display for TEProjective<P> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}", TEAffine::from(*self))
        }
    }

    impl<P: Parameters> PartialEq for TEProjective<P> {
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

    impl<P: Parameters> Distribution<TEProjective<P>> for Standard {
        #[inline]
        fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> TEProjective<P> {
            loop {
                let x = P::BaseField::rand(rng);
                let greatest = rng.gen();

                if let Some(p) = TEAffine::get_point_from_x(x, greatest) {
                    return p.scale_by_cofactor();
                }
            }
        }
    }

    impl<P: Parameters> Default for TEProjective<P> {
        #[inline]
        fn default() -> Self {
            Self::zero()
        }
    }

    impl<P: Parameters> TEProjective<P> {
        pub(crate) fn new_unchecked(
            x: P::BaseField,
            y: P::BaseField,
            t: P::BaseField,
            z: P::BaseField,
        ) -> Self {
            Self {
                x,
                y,
                t,
                z,
                _params: PhantomData,
            }
        }

        /// Can `self` be converted to [`TEAffine`] cheaply?
        #[inline]
        pub fn is_normalized(&self) -> bool {
            self.is_zero() || self.z.is_one()
        }
    }
    impl<P: Parameters> Zeroize for TEProjective<P> {
        // The phantom data does not contain element-specific data
        // and thus does not need to be zeroized.
        fn zeroize(&mut self) {
            self.x.zeroize();
            self.y.zeroize();
            self.t.zeroize();
            self.z.zeroize();
        }
    }

    impl<P: Parameters> Zero for TEProjective<P> {
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

    impl<P: Parameters> CurveGroup for TEProjective<P> {
        const COFACTOR: &'static [u64] = P::COFACTOR;

        const COFACTOR_INVERSE: Self::ScalarField = P::COFACTOR_INV;

        type BaseField = P::BaseField;
    }

    impl<P: Parameters> Group for TEProjective<P> {
        type ScalarField = P::ScalarField;
        type NormalForm = TEAffine<P>;

        fn generator() -> Self::NormalForm {
            TEAffine::generator()
        }

        /// Canonicalize a slice of projective elements into their normalized representation.
        ///
        /// For `N = v.len()`, this costs  1 inversion + 5N field multiplications
        /// For `N = v.len()`, this costs 1 inversion + 5N field multiplications.
        ///
        /// (Where batch inversion comprises 3N field multiplications + 1 inversion of these operations)
        fn batch_normalize(v: &[Self]) -> Vec<Self::NormalForm> {
            // A projective curve element (x, y, t, z) is normalized
            // to its affine representation, by the conversion
            // (x, y, t, z) -> (x/z, y/z, t/z, 1)
            let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
            ark_ff::batch_inverse_in_place(&mut z_s);

            // Perform affine transformations
            ark_std::cfg_iter!(v)
                .zip(z_s)
                .map(|(g, z)| {
                    let mut g = *g;
                    if !g.is_normalized() {
                        g.x *= &z; // x/z
                        g.y *= &z;
                    }
                    if g.is_zero() {
                        TEAffine::zero()
                    } else {
                        TEAffine::new_unchecked(g.x, g.y)
                    }
                })
                .collect()
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

        fn add_normal_in_place(&mut self, other: &TEAffine<P>) {
            // See "Twisted Edwards Curves Revisited"
            // Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
            // 3.1 Unified Addition in E^e
            // Source: https://www.hyperelliptic.org/EFD/g1p/data/twisted/extended/addition/madd-2008-hwcd

            // A = X1*X2
            let a = self.x * &other.x();
            // B = Y1*Y2
            let b = self.y * &other.y();
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

    impl<P: Parameters> Neg for TEProjective<P> {
        type Output = Self;
        fn neg(mut self) -> Self {
            self.x = -self.x;
            self.t = -self.t;
            self
        }
    }

    ark_ff::impl_additive_ops_from_ref!(TEProjective, Parameters);

    impl<'a, P: Parameters> Add<&'a Self> for TEProjective<P> {
        type Output = Self;
        fn add(mut self, other: &'a Self) -> Self {
            self += other;
            self
        }
    }

    impl<'a, P: Parameters> AddAssign<&'a Self> for TEProjective<P> {
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

    impl<'a, P: Parameters> Sub<&'a Self> for TEProjective<P> {
        type Output = Self;
        fn sub(mut self, other: &'a Self) -> Self {
            self -= other;
            self
        }
    }

    impl<'a, P: Parameters> SubAssign<&'a Self> for TEProjective<P> {
        fn sub_assign(&mut self, other: &'a Self) {
            *self += &(-(*other));
        }
    }

    impl<P: Parameters> MulAssign<P::ScalarField> for TEProjective<P> {
        fn mul_assign(&mut self, other: P::ScalarField) {
            *self = self.mul(other.into_repr())
        }
    }

    /// The affine point (X, Y) is represented in the Extended Projective coordinates
    /// with Z = 1.
    impl<P: Parameters> From<TEAffine<P>> for TEProjective<P> {
        fn from(p: TEAffine<P>) -> TEProjective<P> {
            Self::new_unchecked(p.x, p.y, p.x * &p.y, P::BaseField::one())
        }
    }

    // The projective point X, Y, T, Z is represented in the affine
    // coordinates as X/Z, Y/Z.
    impl<P: Parameters> From<TEProjective<P>> for TEAffine<P> {
        fn from(p: TEProjective<P>) -> TEAffine<P> {
            if p.is_zero() {
                TEAffine::zero()
            } else if p.z.is_one() {
                // If Z is one, the point is already normalized.
                TEAffine::new_unchecked(p.x, p.y)
            } else {
                // Z is nonzero, so it must have an inverse in a field.
                let z_inv = p.z.inverse().unwrap();
                let x = p.x * &z_inv;
                let y = p.y * &z_inv;
                TEAffine::new_unchecked(x, y)
            }
        }
    }

    impl<P: Parameters> CanonicalSerialize for TEProjective<P> {
        #[allow(unused_qualifications)]
        #[inline]
        fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            let aff = TEAffine::<P>::from(self.clone());
            aff.serialize(writer)
        }

        #[inline]
        fn serialized_size(&self) -> usize {
            let aff = TEAffine::<P>::from(self.clone());
            aff.serialized_size()
        }

        #[allow(unused_qualifications)]
        #[inline]
        fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
            let aff = TEAffine::<P>::from(self.clone());
            aff.serialize_uncompressed(writer)
        }

        #[inline]
        fn uncompressed_size(&self) -> usize {
            let aff = TEAffine::<P>::from(self.clone());
            aff.uncompressed_size()
        }
    }

    impl<P: Parameters> CanonicalDeserialize for TEProjective<P> {
        #[allow(unused_qualifications)]
        fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = TEAffine::<P>::deserialize(reader)?;
            Ok(aff.into())
        }

        #[allow(unused_qualifications)]
        fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = TEAffine::<P>::deserialize_uncompressed(reader)?;
            Ok(aff.into())
        }

        #[allow(unused_qualifications)]
        fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
            let aff = TEAffine::<P>::deserialize_unchecked(reader)?;
            Ok(aff.into())
        }
    }

    impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for TEProjective<M>
    where
        M::BaseField: ToConstraintField<ConstraintF>,
    {
        #[inline]
        fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
            TEAffine::from(*self).to_field_elements()
        }
    }
}

mod montgomery_affine {
    use super::*;
    #[derive(Derivative)]
    #[derivative(
        Copy(bound = "P: MontgomeryParameters"),
        Clone(bound = "P: MontgomeryParameters"),
        PartialEq(bound = "P: MontgomeryParameters"),
        Eq(bound = "P: MontgomeryParameters"),
        Debug(bound = "P: MontgomeryParameters"),
        Hash(bound = "P: MontgomeryParameters")
    )]
    pub struct MontgomeryAffine<P: MontgomeryParameters> {
        x: P::BaseField,
        y: P::BaseField,
        infinity: bool,
        #[derivative(Debug = "ignore")]
        _params: PhantomData<P>,
    }

    impl<P: MontgomeryParameters> Display for MontgomeryAffine<P> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "MontgomeryAffine(x={}, y={})", self.x, self.y)
        }
    }

    impl<P: MontgomeryParameters> MontgomeryAffine<P> {
        pub fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
            Self {
                x,
                y,
                infinity: false,
                _params: PhantomData,
            }
        }
    }
}

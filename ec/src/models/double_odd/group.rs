use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::Borrow,
    fmt::{Debug, Display, Formatter, Result as FmtResult},
    hash::{Hash, Hasher},
    io::{Read, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    rand::{
        distributions::{Distribution, Standard},
        Rng,
    },
    vec::Vec,
    Zero,
};
use educe::Educe;

use ark_ff::{fields::Field, AdditiveGroup, PrimeField, ToConstraintField, UniformRand};

use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::{Affine, DOCurveConfig};
use crate::{
    scalar_mul::{variable_base::VariableBaseMSM, ScalarMul},
    AffineRepr, CurveGroup, PrimeGroup,
};

/// Fractional coordinates as utilised in <https://doubleodd.group/doubleodd-jq.pdf>,
/// but first defined in <https://www.sciencedirect.com/science/article/pii/S0020019007001433>.
/// Affine point (e,u) is represented as (E:Z:U:T) such that:
/// - Z != 0
/// - e = E/Z
/// - u = U/Z
/// - u**2 / T/Z
#[derive(Educe)]
#[educe(Copy, Clone)]
#[must_use]
pub struct Projective<P: DOCurveConfig> {
    /// `E / Z` projection of the affine `e`
    pub e: P::BaseField,
    /// Projective multiplicative inverse.
    pub z: P::BaseField,
    /// `U / Z` projection of the affine `u`
    pub u: P::BaseField,
    /// Additional formula for faster addition: `T = U^2/Z`
    pub t: P::BaseField,
}

impl<P: DOCurveConfig> Display for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", Affine::from(*self))
    }
}

impl<P: DOCurveConfig> Debug for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.is_zero() {
            true => write!(f, "infinity"),
            false => write!(f, "({}, {}, {}, {})", self.e, self.z, self.u, self.t),
        }
    }
}

impl<P: DOCurveConfig> Eq for Projective<P> {}
impl<P: DOCurveConfig> PartialEq for Projective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }
        if other.is_zero() {
            return false;
        }
        self.e * other.u == other.e * self.u
    }
}

impl<P: DOCurveConfig> PartialEq<Affine<P>> for Projective<P> {
    fn eq(&self, other: &Affine<P>) -> bool {
        *self == other.into_group()
    }
}

impl<P: DOCurveConfig> Hash for Projective<P> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.into_affine().hash(state)
    }
}

impl<P: DOCurveConfig> Distribution<Projective<P>> for Standard {
    /// Generates a uniformly random instance of the curve.
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
        loop {
            let u = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::get_point_from_u_unchecked(u, greatest) {
                return p.into();
            }
        }
    }
}

impl<P: DOCurveConfig> Default for Projective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: DOCurveConfig> Projective<P> {
    /// Constructs a new group element without checking whether the coordinates
    /// specify a point in the subgroup.
    pub const fn new_unchecked(
        e: P::BaseField,
        z: P::BaseField,
        u: P::BaseField,
        t: P::BaseField,
    ) -> Self {
        Self { e, z, u, t }
    }

    /// Constructs a new group element in a way while enforcing that points are in
    /// the prime-order subgroup.
    pub fn new(e: P::BaseField, z: P::BaseField, u: P::BaseField, t: P::BaseField) -> Self {
        let p = Self::new_unchecked(e, z, u, t);
        assert!(p.into_affine().is_on_curve(), "not_on_curve");
        p
    }
}

impl<P: DOCurveConfig> Zeroize for Projective<P> {
    fn zeroize(&mut self) {
        self.e.zeroize();
        self.u.zeroize();
        self.z.zeroize();
        self.t.zeroize();
    }
}

impl<P: DOCurveConfig> Zero for Projective<P> {
    /// Returns one of the representants for the identity, namely the point-at-infinity `(1,1,0,0)`.
    ///
    /// The other representant `N=(-1,1,0,0)` of the identity could also be returned, but the
    /// implementation of formulas only requires one representant.
    #[inline]
    fn zero() -> Self {
        Self::new_unchecked(
            P::BaseField::ONE,
            P::BaseField::ONE,
            P::BaseField::ZERO,
            P::BaseField::ZERO,
        )
    }

    #[inline]
    // Zero has two representants: 'O = (X,X,0,0)`, and `O+N = (X,-X,0,0)`.
    // These are the only two points with U=0, and is_zero assumes the point is correct,
    // so E and Z don't need to be checked.
    fn is_zero(&self) -> bool {
        self.u == P::BaseField::ZERO
    }
}

impl<P: DOCurveConfig> AdditiveGroup for Projective<P> {
    type Scalar = P::ScalarField;

    const ZERO: Self = Self::new_unchecked(
        P::BaseField::ONE,
        P::BaseField::ONE,
        P::BaseField::ZERO,
        P::BaseField::ZERO,
    );

    // Implements extended coordinates doubling as per the DO website:
    // https://doubleodd.group/formulas-eu.html#extended-coordinates
    // https://web.archive.org/web/20240718235643/https://doubleodd.group/formulas-eu.html#extended-coordinates
    fn double_in_place(&mut self) -> &mut Self {
        self.z = -P::get_c().double() * self.t.square(); // Self.z == -2cT^2
        self.t = self.e;
        self.e.square_in_place(); // Self.e == E^2
        self.z += self.e; // Self.z == E^2 -2cT^2
        self.z += (P::COEFF_A * self.u.square()).double(); // Self.z == W' == E^2 + 2aU^2 -2cT^2

        self.t *= self.u;
        self.t.double_in_place(); // Self.t == J'= 2EU

        self.u = self.t; // Self.u == Self.t == J'
        self.t.square_in_place(); // Self.t == T' = J'^2

        self.u *= self.z; // U' = J' * W'
        self.z.square_in_place(); // Self.z == W'^2

        self.e.square_in_place(); // Self.e == X' == E^4
        self.e.double_in_place(); // Self.e == 2X'
        self.e += -self.z + (P::COEFF_A * self.t); // E' = 2X' - Z' + aT'

        self
    }
}

impl<P: DOCurveConfig> PrimeGroup for Projective<P> {
    type ScalarField = P::ScalarField;

    #[inline]
    fn generator() -> Self {
        Affine::generator().into()
    }

    #[inline]
    fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self {
        P::mul_projective(self, other.as_ref())
    }
}

impl<P: DOCurveConfig> CurveGroup for Projective<P> {
    type Config = P;
    type BaseField = P::BaseField;
    type Affine = Affine<P>;
    type FullGroup = Affine<P>;

    #[inline]
    fn normalize_batch(v: &[Self]) -> Vec<Self::Affine> {
        let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
        ark_ff::batch_inversion(&mut z_s);

        // Perform affine transformations
        ark_std::cfg_iter!(v)
            .zip(z_s)
            .map(|(g, z)| match g.is_zero() {
                true => Affine::identity(),
                false => {
                    let e = g.e * z;
                    let u = g.u * z;

                    Affine::new_unchecked(e, u)
                },
            })
            .collect()
    }
}

impl<P: DOCurveConfig> Neg for Projective<P> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.u = -self.u;
        self
    }
}

impl<P: DOCurveConfig, T: Borrow<Affine<P>>> AddAssign<T> for Projective<P> {
    /// Using Algorithm 3 from <https://doubleodd.group/doubleodd-jq.pdf>,
    /// simplified because the second point is affine
    /// (n2 = Z1, n5 = Z1*T2 + T1).
    fn add_assign(&mut self, other: T) {
        let other = other.borrow();
        let othert = other.u.square();
        let n1 = self.e * other.e;
        let n2 = self.z;
        let n3 = self.u * other.u;
        let n4 = self.t * othert;

        let n5 = self.z * othert + self.t;
        let n6 = (self.e + self.u) * (other.e + other.u) - n1 - n3;
        let c = P::get_c();
        let cn4 = c * n4;
        let n7 = n2 - cn4;

        let n3d = n3.double();

        self.e = (n2 + cn4) * (n1 - P::COEFF_A * n3d) + c * n3d * n5;
        self.z = n7.square();
        self.t = n6.square();
        self.u = n7 * n6;
    }
}

impl<P: DOCurveConfig, T: Borrow<Affine<P>>> Add<T> for Projective<P> {
    type Output = Self;
    fn add(mut self, other: T) -> Self {
        let other = other.borrow();
        self += other;
        self
    }
}

impl<P: DOCurveConfig, T: Borrow<Affine<P>>> SubAssign<T> for Projective<P> {
    fn sub_assign(&mut self, other: T) {
        *self += -(*other.borrow());
    }
}

impl<P: DOCurveConfig, T: Borrow<Affine<P>>> Sub<T> for Projective<P> {
    type Output = Self;
    fn sub(mut self, other: T) -> Self {
        self -= other.borrow();
        self
    }
}

ark_ff::impl_additive_ops_from_ref!(Projective, DOCurveConfig);

impl<'a, P: DOCurveConfig> Add<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: DOCurveConfig> AddAssign<&'a Self> for Projective<P> {
    /// Using Algorithm 3 from <https://doubleodd.group/doubleodd-jq.pdf>.
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }

        let n1 = self.e * other.e;
        let n2 = self.z * other.z;
        let n3 = self.u * other.u;
        let n4 = self.t * other.t;

        let n5 = (self.z + self.t) * (other.z + other.t) - n2 - n4;
        self.t = (self.e + self.u) * (other.e + other.u) - n1 - n3;
        let c = P::get_c();
        let cn4 = c * n4;
        self.z = n2 - cn4;

        let n3d = n3.double();

        self.e = (n2 + cn4) * (n1 - P::COEFF_A * n3d) + c * n3d * n5;
        self.u = self.z * self.t;
        self.z.square_in_place();
        self.t.square_in_place();
    }
}

impl<'a, P: DOCurveConfig> Sub<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

impl<'a, P: DOCurveConfig> SubAssign<&'a Self> for Projective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: DOCurveConfig, T: Borrow<P::ScalarField>> MulAssign<T> for Projective<P> {
    fn mul_assign(&mut self, other: T) {
        *self = self.mul_bigint(other.borrow().into_bigint())
    }
}

impl<P: DOCurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Projective<P> {
    type Output = Self;

    #[inline]
    fn mul(mut self, other: T) -> Self {
        self *= other;
        self
    }
}

impl<P: DOCurveConfig> From<Affine<P>> for Projective<P> {
    #[inline]
    fn from(p: Affine<P>) -> Self {
        let u = p.u;
        let e = p.e;
        let z = P::BaseField::ONE;
        let t = u.square();

        Self::new_unchecked(e, z, u, t)
    }
}

impl<P: DOCurveConfig> CanonicalSerialize for Projective<P> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        let aff = Affine::<P>::from(*self);
        P::serialize_with_mode(&aff, writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        P::serialized_size(compress)
    }
}

impl<P: DOCurveConfig> Valid for Projective<P> {
    fn check(&self) -> Result<(), SerializationError> {
        self.into_affine().check()
    }

    fn batch_check<'a>(
        batch: impl Iterator<Item = &'a Self> + Send,
    ) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        let batch = batch.copied().collect::<Vec<_>>();
        let batch = Self::normalize_batch(&batch);
        Affine::batch_check(batch.iter())
    }
}

impl<P: DOCurveConfig> CanonicalDeserialize for Projective<P> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let aff = P::deserialize_with_mode(reader, compress, validate)?;
        Ok(aff.into())
    }
}

impl<M: DOCurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Projective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        Affine::from(*self).to_field_elements()
    }
}

impl<P: DOCurveConfig> ScalarMul for Projective<P> {
    type MulBase = Affine<P>;
    const NEGATION_IS_CHEAP: bool = true;

    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase> {
        Self::normalize_batch(bases)
    }
}

impl<P: DOCurveConfig> VariableBaseMSM for Projective<P> {
    type Bucket = Self;
    const ZERO_BUCKET: Self = Self::ZERO;

    fn msm(bases: &[Self::MulBase], bigints: &[Self::ScalarField]) -> Result<Self, usize> {
        P::msm(bases, bigints)
    }
}

impl<P: DOCurveConfig, T: Borrow<Affine<P>>> core::iter::Sum<T> for Projective<P> {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::zero(), |sum, x| sum + x.borrow())
    }
}

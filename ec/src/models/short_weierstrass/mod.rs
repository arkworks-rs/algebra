use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};

use ark_ff::{fields::Field, PrimeField};

use crate::{scalar_mul::variable_base::VariableBaseMSM, AffineRepr, Group};

use num_traits::Zero;

mod affine;
pub use affine::*;

mod group;
pub use group::*;

mod serialization_flags;
pub use serialization_flags::*;

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
    fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
        if Self::COEFF_A.is_zero() {
            Self::BaseField::ZERO
        } else {
            elem * Self::COEFF_A
        }
    }

    /// Helper method for computing `elem + Self::COEFF_B`.
    ///
    /// The default implementation should be overridden only if
    /// the sum can be computed faster than standard field addition (eg: via
    /// doubling).
    #[inline(always)]
    fn add_b(elem: Self::BaseField) -> Self::BaseField {
        if Self::COEFF_B.is_zero() {
            elem
        } else {
            elem + &Self::COEFF_B
        }
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
                res += base
            }
        }

        res
    }

    /// Default implementation for multi scalar multiplication
    fn model_msm_bigint(
        bases: &[Affine<Self>],
        bigints: &[<Self::ScalarField as PrimeField>::BigInt],
    ) -> Projective<Self> {
        VariableBaseMSM::default_msm_bigint(bases, bigints)
    }

    /// If uncompressed, serializes both x and y coordinates as well as a bit for whether it is
    /// infinity. If compressed, serializes x coordinate with two bits to encode whether y is
    /// positive, negative, or infinity.
    #[inline]
    fn serialize_with_mode<W: Write>(
        item: &Affine<Self>,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        let (x, y, flags) = match item.infinity {
            true => (
                Self::BaseField::zero(),
                Self::BaseField::zero(),
                SWFlags::infinity(),
            ),
            false => (item.x, item.y, item.to_flags()),
        };

        match compress {
            Compress::Yes => x.serialize_with_flags(writer, flags),
            Compress::No => {
                x.serialize_with_mode(&mut writer, compress)?;
                y.serialize_with_flags(&mut writer, flags)
            },
        }
    }

    /// If `validate` is `Yes`, calls `check()` to make sure the element is valid.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Affine<Self>, SerializationError> {
        let (x, y, flags) = match compress {
            Compress::Yes => {
                let (x, flags): (_, SWFlags) =
                    CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
                match flags {
                    SWFlags::PointAtInfinity => (
                        Affine::<Self>::identity().x,
                        Affine::<Self>::identity().y,
                        flags,
                    ),
                    _ => {
                        let is_positive = flags.is_positive().unwrap();
                        let (y, neg_y) = Affine::<Self>::get_ys_from_x_unchecked(x)
                            .ok_or(SerializationError::InvalidData)?;
                        if is_positive {
                            (x, y, flags)
                        } else {
                            (x, neg_y, flags)
                        }
                    },
                }
            },
            Compress::No => {
                let x: Self::BaseField =
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
                let (y, flags): (_, SWFlags) =
                    CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
                (x, y, flags)
            },
        };
        if flags.is_infinity() {
            Ok(Affine::<Self>::identity())
        } else {
            let point = Affine::<Self>::new_unchecked(x, y);
            if let Validate::Yes = validate {
                point.check()?;
            }
            Ok(point)
        }
    }

    #[inline]
    fn serialized_size(compress: Compress) -> usize {
        let zero = Self::BaseField::zero();
        match compress {
            Compress::Yes => zero.serialized_size_with_flags::<SWFlags>(),
            Compress::No => zero.compressed_size() + zero.serialized_size_with_flags::<SWFlags>(),
        }
    }
}

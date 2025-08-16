use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};

use ark_ff::{AdditiveGroup, Field, Zero};

mod affine;
pub use affine::*;

mod group;
pub use group::*;

use crate::VariableBaseMSM;

/// Constants and convenience functions that collectively define the [Double-Odd curve](https://doubleodd.group).
/// In this model, the curve equation is `y² = x(x² + ax + b)`, (b and (a² - 4b) not squares in field)
/// for constants `a` and `b`.
pub trait DOCurveConfig: super::CurveConfig {
    /// Coefficient `a` of the curve equation.
    const COEFF_A: Self::BaseField;
    /// Coefficient `b` of the curve equation.
    const COEFF_B: Self::BaseField;
    /// Generator of the prime-order subgroup.
    const GENERATOR: Affine<Self>;

    fn get_c() -> Self::BaseField {
        Self::COEFF_A.square() - Self::COEFF_B.double().double()
    }

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

    fn msm(
        bases: &[Affine<Self>],
        scalars: &[Self::ScalarField],
    ) -> Result<Projective<Self>, usize> {
        (bases.len() == scalars.len())
            .then(|| VariableBaseMSM::msm_unchecked(bases, scalars))
            .ok_or_else(|| bases.len().min(scalars.len()))
    }

    #[inline]
    fn serialize_with_mode<W: Write>(
        item: &Affine<Self>,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        match compress {
            Compress::Yes => {
                let mut buffer = ark_std::vec::Vec::new();
                item.e.serialize_uncompressed(&mut buffer)?;
                if buffer[0] & 1u8 == 1u8 {
                    -item.u
                } else {
                    item.u
                }
                .serialize_uncompressed(writer)
            },
            Compress::No => {
                item.e.serialize_with_mode(&mut writer, compress)?;
                item.u.serialize_with_mode(&mut writer, compress)
            },
        }
    }

    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Affine<Self>, SerializationError> {
        let (e, u) = match compress {
            Compress::Yes => {
                let u: Self::BaseField = CanonicalDeserialize::deserialize_uncompressed(reader)?;
                let e: Self::BaseField =
                    Affine::<Self>::get_e_from_u(u).ok_or(SerializationError::InvalidData)?;
                (e, u)
            },
            Compress::No => {
                let e: Self::BaseField =
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
                let u: Self::BaseField =
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
                (e, u)
            },
        };

        let mut buffer = ark_std::vec::Vec::new();
        e.serialize_uncompressed(&mut buffer)?;

        let e = if buffer[0] & 1u8 == 1u8 { -e } else { e };

        let point = Affine::new_unchecked(e, u);
        if validate == Validate::Yes {
            point.check()?;
        }
        Ok(point)
    }

    #[inline]
    fn serialized_size(compress: Compress) -> usize {
        let zero = Self::BaseField::zero();
        match compress {
            Compress::Yes => zero.compressed_size(),
            Compress::No => zero.compressed_size() * 2,
        }
    }
}

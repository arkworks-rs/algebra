use ark_ec::{short_weierstrass::Affine, AffineRepr};
use ark_ff::{BigInteger384, PrimeField};
use ark_serialize::SerializationError;

use crate::{g1::Config as G1Config, g2::Config as G2Config, Fq, Fq2, G1Affine, G2Affine};

pub const G1_SERIALIZED_SIZE: usize = 48;
pub const G2_SERIALIZED_SIZE: usize = 96;

pub struct EncodingFlags {
    pub is_compressed: bool,
    pub is_infinity: bool,
    pub is_lexographically_largest: bool,
}

impl EncodingFlags {
    /// Fetches the flags from the byte-string
    pub fn get_flags(bytes: &[u8]) -> Result<Self, SerializationError> {
        let compression_flag_set = (bytes[0] >> 7) & 1;
        let infinity_flag_set = (bytes[0] >> 6) & 1;
        let sort_flag_set = (bytes[0] >> 5) & 1;

        let is_compressed = compression_flag_set == 1;
        let is_infinity = infinity_flag_set == 1;
        let is_lexographically_largest = sort_flag_set == 1;

        if is_lexographically_largest && (!is_compressed || is_infinity) {
            return Err(SerializationError::InvalidData);
        }

        Ok(Self {
            is_compressed,
            is_infinity,
            is_lexographically_largest,
        })
    }

    /// Encodes the flags into the byte-string
    pub fn encode_flags(&self, bytes: &mut [u8]) {
        if self.is_compressed {
            bytes[0] |= 1 << 7;
        }

        if self.is_infinity {
            bytes[0] |= 1 << 6;
        }

        if self.is_compressed && !self.is_infinity && self.is_lexographically_largest {
            bytes[0] |= 1 << 5;
        }
    }

    /// Removes the flags from the byte-string.
    ///
    /// This reverses the effects of `encode_flags`.
    pub fn remove_flags(bytes: &mut [u8]) {
        bytes[0] &= 0b0001_1111;
    }
}

pub(crate) fn deserialize_fq(bytes: [u8; 48]) -> Option<Fq> {
    let mut tmp = BigInteger384::new([0, 0, 0, 0, 0, 0]);

    // Note: The following unwraps are if the compiler cannot convert
    // the byte slice into [u8;8], we know this is infallible since we
    // are providing the indices at compile time and bytes has a fixed size
    tmp.0[5] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
    tmp.0[4] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
    tmp.0[3] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
    tmp.0[2] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());
    tmp.0[1] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap());
    tmp.0[0] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap());

    Fq::from_bigint(tmp)
}

pub(crate) fn serialize_fq(field: Fq) -> [u8; 48] {
    let mut result = [0u8; 48];

    let rep = field.into_bigint();

    result[0..8].copy_from_slice(&rep.0[5].to_be_bytes());
    result[8..16].copy_from_slice(&rep.0[4].to_be_bytes());
    result[16..24].copy_from_slice(&rep.0[3].to_be_bytes());
    result[24..32].copy_from_slice(&rep.0[2].to_be_bytes());
    result[32..40].copy_from_slice(&rep.0[1].to_be_bytes());
    result[40..48].copy_from_slice(&rep.0[0].to_be_bytes());

    result
}

fn read_bytes_with_offset(bytes: &[u8], offset: usize, mask: bool) -> [u8; G1_SERIALIZED_SIZE] {
    let mut tmp = [0; G1_SERIALIZED_SIZE];
    // read `G1_SERIALIZED_SIZE` bytes
    tmp.copy_from_slice(&bytes[offset * G1_SERIALIZED_SIZE..G1_SERIALIZED_SIZE * (offset + 1)]);

    if mask {
        EncodingFlags::remove_flags(&mut tmp);
    }
    tmp
}

pub(crate) fn read_g1_compressed<R: ark_serialize::Read>(
    mut reader: R,
) -> Result<Affine<G1Config>, ark_serialize::SerializationError> {
    let mut bytes = [0u8; G1_SERIALIZED_SIZE];
    reader
        .read_exact(&mut bytes)
        .ok()
        .ok_or(SerializationError::InvalidData)?;

    // Obtain the three flags from the start of the byte sequence
    let flags = EncodingFlags::get_flags(&bytes[..])?;

    // We expect to be deserializing a compressed point
    if !flags.is_compressed {
        return Err(SerializationError::UnexpectedFlags);
    }

    // Attempt to obtain the x-coordinate
    let x_bytes = read_bytes_with_offset(&bytes, 0, true);

    if flags.is_infinity {
        // Check that the `x` co-ordinate was `0`
        if x_bytes != [0u8; 48] {
            return Err(SerializationError::InvalidData);
        }

        return Ok(G1Affine::zero());
    }

    let x = deserialize_fq(x_bytes).ok_or(SerializationError::InvalidData)?;
    let p = G1Affine::get_point_from_x_unchecked(x, flags.is_lexographically_largest)
        .ok_or(SerializationError::InvalidData)?;

    Ok(p)
}

pub(crate) fn read_g1_uncompressed<R: ark_serialize::Read>(
    mut reader: R,
) -> Result<Affine<G1Config>, ark_serialize::SerializationError> {
    let mut bytes = [0u8; 2 * G1_SERIALIZED_SIZE];
    reader
        .read_exact(&mut bytes)
        .map_err(|_| SerializationError::InvalidData)?;

    // Obtain the three flags from the start of the byte sequence
    let flags = EncodingFlags::get_flags(&bytes[..])?;

    // we expect to be deserializing an uncompressed point
    if flags.is_compressed {
        return Err(SerializationError::UnexpectedFlags);
    }

    let x_bytes = read_bytes_with_offset(&bytes, 0, true);
    let y_bytes = read_bytes_with_offset(&bytes, 1, false);

    if flags.is_infinity {
        if x_bytes != [0u8; 48] || y_bytes != [0u8; 48] {
            return Err(SerializationError::InvalidData);
        }
        return Ok(G1Affine::zero());
    }

    // Attempt to obtain the x-coordinate
    let x = deserialize_fq(x_bytes).ok_or(SerializationError::InvalidData)?;
    // Attempt to obtain the y-coordinate
    let y = deserialize_fq(y_bytes).ok_or(SerializationError::InvalidData)?;
    let p = G1Affine::new_unchecked(x, y);

    Ok(p)
}

pub(crate) fn read_g2_compressed<R: ark_serialize::Read>(
    mut reader: R,
) -> Result<Affine<G2Config>, ark_serialize::SerializationError> {
    let mut bytes = [0u8; G2_SERIALIZED_SIZE];
    reader
        .read_exact(&mut bytes)
        .map_err(|_| SerializationError::InvalidData)?;

    // Obtain the three flags from the start of the byte sequence
    let flags = EncodingFlags::get_flags(&bytes)?;

    // we expect to be deserializing a compressed point
    if !flags.is_compressed {
        return Err(SerializationError::UnexpectedFlags);
    }

    let xc1_bytes = read_bytes_with_offset(&bytes, 0, true);
    let xc0_bytes = read_bytes_with_offset(&bytes, 1, false);

    if flags.is_infinity {
        if xc1_bytes != [0u8; 48] || xc0_bytes != [0u8; 48] {
            return Err(SerializationError::InvalidData);
        }
        return Ok(G2Affine::zero());
    }

    // Attempt to obtain the x-coordinate
    let xc1 = deserialize_fq(xc1_bytes).ok_or(SerializationError::InvalidData)?;
    let xc0 = deserialize_fq(xc0_bytes).ok_or(SerializationError::InvalidData)?;
    let x = Fq2::new(xc0, xc1);

    let p = G2Affine::get_point_from_x_unchecked(x, flags.is_lexographically_largest)
        .ok_or(SerializationError::InvalidData)?;

    Ok(p)
}

pub(crate) fn read_g2_uncompressed<R: ark_serialize::Read>(
    mut reader: R,
) -> Result<Affine<G2Config>, ark_serialize::SerializationError> {
    let mut bytes = [0u8; 2 * G2_SERIALIZED_SIZE];
    reader
        .read_exact(&mut bytes)
        .map_err(|_| SerializationError::InvalidData)?;

    // Obtain the three flags from the start of the byte sequence
    let flags = EncodingFlags::get_flags(&bytes)?;

    // we expect to be deserializing an uncompressed point
    if flags.is_compressed {
        return Err(SerializationError::UnexpectedFlags);
    }

    let xc1_bytes = read_bytes_with_offset(&bytes, 0, true);
    let xc0_bytes = read_bytes_with_offset(&bytes, 1, false);

    let yc1_bytes = read_bytes_with_offset(&bytes, 2, false);
    let yc0_bytes = read_bytes_with_offset(&bytes, 3, false);

    if flags.is_infinity {
        if xc1_bytes != [0u8; 48]
            || xc0_bytes != [0u8; 48]
            || yc1_bytes != [0u8; 48]
            || yc0_bytes != [0u8; 48]
        {
            return Err(SerializationError::InvalidData);
        }
        return Ok(G2Affine::zero());
    }

    let xc1 = deserialize_fq(xc1_bytes).ok_or(SerializationError::InvalidData)?;
    let xc0 = deserialize_fq(xc0_bytes).ok_or(SerializationError::InvalidData)?;
    let yc1 = deserialize_fq(yc1_bytes).ok_or(SerializationError::InvalidData)?;
    let yc0 = deserialize_fq(yc0_bytes).ok_or(SerializationError::InvalidData)?;

    // Attempt to obtain the x-coordinate
    let x = Fq2::new(xc0, xc1);

    // Attempt to obtain the y-coordinate
    let y = Fq2::new(yc0, yc1);

    let p = G2Affine::new_unchecked(x, y);

    Ok(p)
}

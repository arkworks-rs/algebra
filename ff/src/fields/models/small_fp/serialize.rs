use crate::fields::models::small_fp::small_fp_backend::{SmallFp, SmallFpConfig};
use crate::{BigInt, PrimeField, Zero};
use ark_serialize::{
    buffer_byte_size, CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Compress, EmptyFlags, Flags, SerializationError, Valid, Validate,
};
use ark_std::vec;

impl<P: SmallFpConfig> CanonicalSerializeWithFlags for SmallFp<P> {
    fn serialize_with_flags<W: ark_std::io::Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }

        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`. If `F::BIT_SIZE < 8`,
        // this is at most `N * 8 + 1`
        let output_byte_size = buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE);
        let mut w = writer;

        // Write out `self` to a temporary buffer.
        // The size of the buffer is $byte_size + 1 because `F::BIT_SIZE`
        // is at most 8 bits.

        if output_byte_size <= 8 {
            // Fields with type smaller than u64
            // Writes exactly the minimal required number of bytes
            let bigint = self.into_bigint();
            let value = bigint.0[0];
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&value.to_le_bytes());
            bytes[output_byte_size - 1] |= flags.u8_bitmask();
            w.write_all(&bytes[..output_byte_size])?;
        } else {
            // For larger fields, use the approach from `FpConfig`
            let mut bytes = crate::const_helpers::SerBuffer::zeroed();
            bytes.copy_from_u64_slice(&self.into_bigint().0);
            // Mask out the bits of the last byte that correspond to the flag.
            bytes[output_byte_size - 1] |= flags.u8_bitmask();
            bytes.write_up_to(&mut w, output_byte_size)?;
        }
        Ok(())
    }

    // Let `m = 8 * n` for some `n` be the smallest multiple of 8 greater
    // than `P::MODULUS_BIT_SIZE`.
    // If `(m - P::MODULUS_BIT_SIZE) >= F::BIT_SIZE` , then this method returns `n`;
    // otherwise, it returns `n + 1`.
    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        buffer_byte_size(Self::MODULUS_BIT_SIZE as usize + F::BIT_SIZE)
    }
}

impl<P: SmallFpConfig> CanonicalSerialize for SmallFp<P> {
    #[inline]
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        self.serialized_size_with_flags::<EmptyFlags>()
    }
}

impl<P: SmallFpConfig> CanonicalDeserializeWithFlags for SmallFp<P> {
    fn deserialize_with_flags<R: ark_std::io::Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError> {
        // All reasonable `Flags` should be less than 8 bits in size
        // (256 values are enough for anyone!)
        if F::BIT_SIZE > 8 {
            return Err(SerializationError::NotEnoughSpace);
        }
        // Calculate the number of bytes required to represent a field element
        // serialized with `flags`.
        let output_byte_size = Self::zero().serialized_size_with_flags::<F>();
        let mut r = reader;

        if output_byte_size <= 8 {
            // Fields with type smaller than u64
            let mut bytes = vec![0u8; output_byte_size];
            r.read_exact(&mut bytes)?;
            let flags = F::from_u8_remove_flags(&mut bytes[output_byte_size - 1])
                .ok_or(SerializationError::UnexpectedFlags)?;

            let mut limb_bytes = [0u8; 8];
            limb_bytes[..output_byte_size.min(8)]
                .copy_from_slice(&bytes[..output_byte_size.min(8)]);
            let limb = u64::from_le_bytes(limb_bytes);
            let bigint = BigInt::<2>::new([limb, 0]);

            Self::from_bigint(bigint)
                .map(|v| (v, flags))
                .ok_or(SerializationError::InvalidData)
        } else {
            // For larger fields, use the approach from `FpConfig`
            let mut masked_bytes = crate::const_helpers::SerBuffer::zeroed();
            masked_bytes.read_exact_up_to(&mut r, output_byte_size)?;
            let flags = F::from_u8_remove_flags(&mut masked_bytes[output_byte_size - 1])
                .ok_or(SerializationError::UnexpectedFlags)?;

            let self_integer = masked_bytes.to_bigint();
            Self::from_bigint(self_integer)
                .map(|v| (v, flags))
                .ok_or(SerializationError::InvalidData)
        }
    }
}

impl<P: SmallFpConfig> Valid for SmallFp<P> {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl<P: SmallFpConfig> CanonicalDeserialize for SmallFp<P> {
    fn deserialize_with_mode<R: ark_std::io::Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Self::deserialize_with_flags::<R, EmptyFlags>(reader).map(|(r, _)| r)
    }
}

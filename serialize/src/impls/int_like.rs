use crate::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    io::{Read, Write},
    vec::*,
};
use num_bigint::BigUint;

impl Valid for bool {
    const TRIVIAL_CHECK: bool = true;
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalSerialize for bool {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        writer.write_all(&[*self as u8])?;
        Ok(())
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        1
    }
}

impl CanonicalDeserialize for bool {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        match u8::deserialize_with_mode(reader, compress, validate)? {
            0u8 => Ok(false),
            1u8 => Ok(true),
            _ => Err(SerializationError::InvalidData),
        }
    }
}

macro_rules! impl_uint {
    ($type:ty) => {
        impl CanonicalSerialize for $type {
            #[inline]
            fn serialize_with_mode<W: Write>(
                &self,
                mut writer: W,
                _compress: Compress,
            ) -> Result<(), SerializationError> {
                Ok(writer.write_all(&self.to_le_bytes())?)
            }

            #[inline]
            fn serialized_size(&self, _compress: Compress) -> usize {
                core::mem::size_of::<$type>()
            }
        }

        impl Valid for $type {
            const TRIVIAL_CHECK: bool = true;

            #[inline]
            fn check(&self) -> Result<(), SerializationError> {
                Ok(())
            }

            #[inline]
            fn batch_check<'a>(
                _batch: impl Iterator<Item = &'a Self>,
            ) -> Result<(), SerializationError>
            where
                Self: 'a,
            {
                Ok(())
            }
        }

        impl CanonicalDeserialize for $type {
            #[inline]
            fn deserialize_with_mode<R: Read>(
                mut reader: R,
                _compress: Compress,
                _validate: Validate,
            ) -> Result<Self, SerializationError> {
                let mut bytes = [0u8; core::mem::size_of::<$type>()];
                reader.read_exact(&mut bytes)?;
                Ok(<$type>::from_le_bytes(bytes))
            }
        }
    };
}

impl_uint!(u8);
impl_uint!(u16);
impl_uint!(u32);
impl_uint!(u64);
impl_uint!(i8);
impl_uint!(i16);
impl_uint!(i32);
impl_uint!(i64);

impl CanonicalSerialize for usize {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        Ok(writer.write_all(&(*self as u64).to_le_bytes())?)
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        core::mem::size_of::<u64>()
    }
}

impl Valid for usize {
    const TRIVIAL_CHECK: bool = true;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(_batch: impl Iterator<Item = &'a Self>) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

impl CanonicalDeserialize for usize {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = [0u8; core::mem::size_of::<u64>()];
        reader.read_exact(&mut bytes)?;
        Ok(<u64>::from_le_bytes(bytes) as Self)
    }
}

impl CanonicalSerialize for isize {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        Ok(writer.write_all(&(*self as i64).to_le_bytes())?)
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        core::mem::size_of::<i64>()
    }
}

impl Valid for isize {
    const TRIVIAL_CHECK: bool = true;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(_batch: impl Iterator<Item = &'a Self>) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

impl CanonicalDeserialize for isize {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut bytes = [0u8; core::mem::size_of::<i64>()];
        reader.read_exact(&mut bytes)?;
        Ok(<i64>::from_le_bytes(bytes) as Self)
    }
}

impl CanonicalSerialize for BigUint {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.to_bytes_le().serialize_with_mode(writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.to_bytes_le().serialized_size(compress)
    }
}

impl CanonicalDeserialize for BigUint {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self::from_bytes_le(&Vec::<u8>::deserialize_with_mode(
            reader, compress, validate,
        )?))
    }
}

impl Valid for BigUint {
    const TRIVIAL_CHECK: bool = true;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(_batch: impl Iterator<Item = &'a Self>) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

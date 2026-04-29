use crate::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};

macro_rules! impl_tuple {
    ($( $ty: ident : $no: tt, )*) => {
        impl<$($ty, )*> Valid for ($($ty,)*) where
            $($ty: Valid,)*
        {
            const TRIVIAL_CHECK: bool = (
                $( < $ty as Valid >::TRIVIAL_CHECK ) & *
            );

            #[inline]
            fn check(&self) -> Result<(), SerializationError> {
                if Self::TRIVIAL_CHECK {
                    Ok(())
                } else {
                    $( self.$no.check()?; )*
                    Ok(())
                }
            }
        }

        #[allow(unused)]
        impl<$($ty, )*> CanonicalSerialize for ($($ty,)*) where
            $($ty: CanonicalSerialize,)*
        {
            #[inline]
            fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
                $(self.$no.serialize_with_mode(&mut writer, compress)?;)*
                Ok(())
            }

            #[inline]
            fn serialized_size(&self, compress: Compress) -> usize {
                [$(
                    self.$no.serialized_size(compress),
                )*].iter().sum()
            }
        }

        impl<$($ty, )*> CanonicalDeserialize for ($($ty,)*) where
            $($ty: CanonicalDeserialize,)*
        {
            #[inline]
            #[allow(unused)]
            fn deserialize_with_mode<R: Read>(mut reader: R, compress: Compress, validate: Validate) -> Result<Self, SerializationError> {
                Ok(($(
                    $ty::deserialize_with_mode(&mut reader, compress, validate)?,
                )*))
            }
        }
    }
}

impl Valid for () {
    const TRIVIAL_CHECK: bool = true;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }

    fn batch_check<'a>(_: impl Iterator<Item = &'a Self> + Send) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

impl CanonicalSerialize for () {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        _writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn serialized_size(&self, _compress: Compress) -> usize {
        0
    }
}

impl CanonicalDeserialize for () {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        _reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(())
    }
}

impl_tuple!(A:0,);
impl_tuple!(A:0, B:1,);
impl_tuple!(A:0, B:1, C:2,);
impl_tuple!(A:0, B:1, C:2, D:3,);
impl_tuple!(A:0, B:1, C:2, D:3, E:4,);

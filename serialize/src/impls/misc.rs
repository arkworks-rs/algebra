use crate::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::*,
    io::{Read, Write},
    marker::PhantomData,
    rc::Rc,
    vec::*,
};

impl<T: CanonicalSerialize> CanonicalSerialize for Option<T> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.is_some().serialize_with_mode(&mut writer, compress)?;
        if let Some(item) = self {
            item.serialize_with_mode(&mut writer, compress)?;
        }

        Ok(())
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        1 + self
            .as_ref()
            .map(|s| s.serialized_size(compress))
            .unwrap_or(0)
    }
}

impl<T: Valid> Valid for Option<T> {
    const TRIVIAL_CHECK: bool = T::TRIVIAL_CHECK;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Some(v) => v.check(),
            None => Ok(()),
        }
    }

    #[inline]
    fn batch_check<'a>(
        batch: impl Iterator<Item = &'a Self> + Send,
    ) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        match Self::TRIVIAL_CHECK {
            true => Ok(()),
            false => T::batch_check(batch.map(Self::as_ref).filter(Option::is_some).flatten()),
        }
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for Option<T> {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let is_some = bool::deserialize_with_mode(&mut reader, compress, validate)?;
        let data = is_some
            .then(|| T::deserialize_with_mode(&mut reader, compress, validate))
            .transpose()?;

        Ok(data)
    }
}

// No-op
impl<T> CanonicalSerialize for PhantomData<T> {
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

impl<T: Sync> Valid for PhantomData<T> {
    const TRIVIAL_CHECK: bool = true;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(_: impl Iterator<Item = &'a Self> + Send) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

impl<T: Send + Sync> CanonicalDeserialize for PhantomData<T> {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        _reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Self)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for &T {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        (*self).serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        (*self).serialized_size(compress)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for &mut T {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        (**self).serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        (**self).serialized_size(compress)
    }
}

impl<T: ?Sized + CanonicalSerialize + ToOwned> CanonicalSerialize for Rc<T> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.as_ref().serialize_with_mode(&mut writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.as_ref().serialized_size(compress)
    }
}

#[cfg(target_has_atomic = "ptr")]
impl<T: ?Sized + CanonicalSerialize + ToOwned> CanonicalSerialize for ark_std::sync::Arc<T> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.as_ref().serialize_with_mode(&mut writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.as_ref().serialized_size(compress)
    }
}

#[cfg(target_has_atomic = "ptr")]
impl<T: ?Sized + Valid + Sync + Send> Valid for ark_std::sync::Arc<T> {
    const TRIVIAL_CHECK: bool = T::TRIVIAL_CHECK;

    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        self.as_ref().check()
    }

    #[inline]
    fn batch_check<'a>(
        batch: impl Iterator<Item = &'a Self> + Send,
    ) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        match T::TRIVIAL_CHECK {
            true => Ok(()),
            false => T::batch_check(batch.map(|v| v.as_ref())),
        }
    }
}

#[cfg(target_has_atomic = "ptr")]
impl<T: CanonicalDeserialize + ToOwned + Sync + Send> CanonicalDeserialize
    for ark_std::sync::Arc<T>
{
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        T::deserialize_with_mode(reader, compress, validate).map(Self::new)
    }
}

impl<T: ?Sized + CanonicalSerialize + ToOwned> CanonicalSerialize for Cow<'_, T> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.as_ref().serialize_with_mode(&mut writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.as_ref().serialized_size(compress)
    }
}

impl<T> Valid for Cow<'_, T>
where
    T: ?Sized + ToOwned + Sync + Valid + Send,
    <T as ToOwned>::Owned: CanonicalDeserialize + Send,
{
    const TRIVIAL_CHECK: bool = <<T as ToOwned>::Owned>::TRIVIAL_CHECK;
    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        match Self::TRIVIAL_CHECK {
            true => Ok(()),
            false => <<T as ToOwned>::Owned>::check(&self.as_ref().to_owned()),
        }
    }

    #[inline]
    fn batch_check<'a>(
        batch: impl Iterator<Item = &'a Self> + Send,
    ) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        match Self::TRIVIAL_CHECK {
            true => return Ok(()),
            false => {
                let t: Vec<_> = batch.map(|v| v.as_ref().to_owned()).collect();
                <<T as ToOwned>::Owned>::batch_check(t.iter())
            },
        }
    }
}

impl<T> CanonicalDeserialize for Cow<'_, T>
where
    T: ?Sized + ToOwned + Valid + Sync + Send,
    <T as ToOwned>::Owned: CanonicalDeserialize + Valid + Send,
{
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(Cow::Owned(<T as ToOwned>::Owned::deserialize_with_mode(
            reader, compress, validate,
        )?))
    }
}

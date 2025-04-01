use ark_std::ops::{Deref, DerefMut};
use ark_std::string::ToString;

use crate::*;

/// A serde-compatible wrapper that forces compression and skips validation.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct CompressedUnchecked<T>(pub T);

/// A serde-compatible wrapper that skips compression and skips validation.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct UncompressedUnchecked<T>(pub T);

/// A serde-compatible wrapper that forces compression and validates.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct CompressedChecked<T>(pub T);

/// A serde-compatible wrapper that skips compression and forces validation.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct UncompressedChecked<T>(pub T);

#[cfg(feature = "serde")]
impl<T> serde::Serialize for CompressedUnchecked<T>
where
    T: CanonicalSerialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut buf = ark_std::vec![];
        self.0
            .serialize_with_mode(&mut buf, Compress::Yes)
            .map_err(|e| serde::ser::Error::custom(e.to_string()))?;
        serializer.serialize_bytes(&buf)
    }
}

#[cfg(feature = "serde")]
impl<T> serde::Serialize for UncompressedUnchecked<T>
where
    T: CanonicalSerialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut buf = ark_std::vec![];
        self.0
            .serialize_with_mode(&mut buf, Compress::No)
            .map_err(|e| serde::ser::Error::custom(e.to_string()))?;
        serializer.serialize_bytes(&buf)
    }
}

#[cfg(feature = "serde")]
impl<T> serde::Serialize for CompressedChecked<T>
where
    T: CanonicalSerialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut buf = ark_std::vec![];
        self.0
            .serialize_with_mode(&mut buf, Compress::Yes)
            .map_err(|e| serde::ser::Error::custom(e.to_string()))?;
        serializer.serialize_bytes(&buf)
    }
}

#[cfg(feature = "serde")]
impl<T> serde::Serialize for UncompressedChecked<T>
where
    T: CanonicalSerialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut buf = ark_std::vec![];
        self.0
            .serialize_with_mode(&mut buf, Compress::No)
            .map_err(|e| serde::ser::Error::custom(e.to_string()))?;
        serializer.serialize_bytes(&buf)
    }
}
#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for CompressedUnchecked<T>
where
    T: CanonicalDeserialize,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let buf = <ark_std::vec::Vec<u8>>::deserialize(deserializer)?;
        let t = T::deserialize_with_mode(&buf[..], Compress::Yes, Validate::No)
            .map_err(|e| serde::de::Error::custom(e.to_string()))?;
        Ok(CompressedUnchecked(t))
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for UncompressedUnchecked<T>
where
    T: CanonicalDeserialize,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let buf = <ark_std::vec::Vec<u8>>::deserialize(deserializer)?;
        let t = T::deserialize_with_mode(&buf[..], Compress::No, Validate::No)
            .map_err(|e| serde::de::Error::custom(e.to_string()))?;
        Ok(UncompressedUnchecked(t))
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for CompressedChecked<T>
where
    T: CanonicalDeserialize,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let buf = <ark_std::vec::Vec<u8>>::deserialize(deserializer)?;
        let t = T::deserialize_with_mode(&buf[..], Compress::Yes, Validate::Yes)
            .map_err(|e| serde::de::Error::custom(e.to_string()))?;
        Ok(CompressedChecked(t))
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for UncompressedChecked<T>
where
    T: CanonicalDeserialize,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let buf = <ark_std::vec::Vec<u8>>::deserialize(deserializer)?;
        let t = T::deserialize_with_mode(&buf[..], Compress::No, Validate::Yes)
            .map_err(|e| serde::de::Error::custom(e.to_string()))?;
        Ok(UncompressedChecked(t))
    }
}

impl<T> Deref for CompressedUnchecked<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> Deref for UncompressedUnchecked<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> Deref for CompressedChecked<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> Deref for UncompressedChecked<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for CompressedUnchecked<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> DerefMut for UncompressedUnchecked<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> DerefMut for CompressedChecked<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> DerefMut for UncompressedChecked<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for CompressedUnchecked<T> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_compressed(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.0.serialized_size(Compress::Yes)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for UncompressedUnchecked<T> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_uncompressed(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.0.serialized_size(Compress::No)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for CompressedChecked<T> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_compressed(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.0.serialized_size(Compress::Yes)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for UncompressedChecked<T> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        _compress: Compress,
    ) -> Result<(), SerializationError> {
        self.0.serialize_uncompressed(writer)
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        self.0.serialized_size(Compress::No)
    }
}

impl<T: Valid> Valid for CompressedUnchecked<T> {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: Valid> Valid for UncompressedUnchecked<T> {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: Valid> Valid for CompressedChecked<T> {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: Valid> Valid for UncompressedChecked<T> {
    fn check(&self) -> Result<(), SerializationError> {
        self.0.check()
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for CompressedUnchecked<T> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(CompressedUnchecked(T::deserialize_with_mode(
            reader,
            Compress::Yes,
            Validate::No,
        )?))
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for UncompressedUnchecked<T> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(UncompressedUnchecked(T::deserialize_with_mode(
            reader,
            Compress::No,
            Validate::No,
        )?))
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for CompressedChecked<T> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(CompressedChecked(T::deserialize_with_mode(
            reader,
            Compress::Yes,
            Validate::Yes,
        )?))
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for UncompressedChecked<T> {
    fn deserialize_with_mode<R: Read>(
        reader: R,
        _compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        Ok(UncompressedChecked(T::deserialize_with_mode(
            reader,
            Compress::No,
            Validate::Yes,
        )?))
    }
}

use ark_std::ops::{Deref, DerefMut};

#[cfg(feature = "serde")]
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

macro_rules! impl_deref {
    ($type:ty) => {
        impl<T> Deref for $type {
            type Target = T;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl<T> DerefMut for $type {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
    };
}

macro_rules! impl_serde {
    ($type:ty, $compress:expr, $validate:expr) => {
        #[cfg(feature = "serde")]
        impl<T> serde::Serialize for $type
        where
            T: CanonicalSerialize,
        {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                let mut buf = ark_std::vec![];
                self.0
                    .serialize_with_mode(&mut buf, $compress)
                    .map_err(|e| serde::ser::Error::custom(e.to_string()))?;
                serializer.serialize_bytes(&buf)
            }
        }

        #[cfg(feature = "serde")]
        impl<'de, T> serde::Deserialize<'de> for $type
        where
            T: CanonicalDeserialize,
        {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let buf = <ark_std::vec::Vec<u8>>::deserialize(deserializer)?;
                let t = T::deserialize_with_mode(&buf[..], $compress, $validate)
                    .map_err(|e| serde::de::Error::custom(e.to_string()))?;
                Ok(Self(t))
            }
        }
    };
}

macro_rules! impl_canonical {
    ($type:ty, $compress:expr, $validate:expr) => {
        impl<T: CanonicalSerialize> CanonicalSerialize for $type {
            fn serialize_with_mode<W: Write>(
                &self,
                writer: W,
                _compress: Compress,
            ) -> Result<(), SerializationError> {
                match $compress {
                    Compress::Yes => self.0.serialize_compressed(writer),
                    Compress::No => self.0.serialize_uncompressed(writer),
                }
            }

            fn serialized_size(&self, _compress: Compress) -> usize {
                self.0.serialized_size($compress)
            }
        }

        impl<T: CanonicalDeserialize> CanonicalDeserialize for $type {
            fn deserialize_with_mode<R: Read>(
                reader: R,
                _compress: Compress,
                _validate: Validate,
            ) -> Result<Self, SerializationError> {
                Ok(Self(T::deserialize_with_mode(
                    reader, $compress, $validate,
                )?))
            }
        }
    };
}

macro_rules! impl_valid {
    ($type:ty) => {
        impl<T: Valid> Valid for $type {
            fn check(&self) -> Result<(), SerializationError> {
                self.0.check()
            }
        }
    };
}

impl_deref!(CompressedUnchecked<T>);
impl_deref!(UncompressedUnchecked<T>);
impl_deref!(CompressedChecked<T>);
impl_deref!(UncompressedChecked<T>);

impl_serde!(CompressedUnchecked<T>, Compress::Yes, Validate::No);
impl_serde!(UncompressedUnchecked<T>, Compress::No, Validate::No);
impl_serde!(CompressedChecked<T>, Compress::Yes, Validate::Yes);
impl_serde!(UncompressedChecked<T>, Compress::No, Validate::Yes);

impl_canonical!(CompressedUnchecked<T>, Compress::Yes, Validate::No);
impl_canonical!(UncompressedUnchecked<T>, Compress::No, Validate::No);
impl_canonical!(CompressedChecked<T>, Compress::Yes, Validate::Yes);
impl_canonical!(UncompressedChecked<T>, Compress::No, Validate::Yes);

impl_valid!(CompressedUnchecked<T>);
impl_valid!(UncompressedUnchecked<T>);
impl_valid!(CompressedChecked<T>);
impl_valid!(UncompressedChecked<T>);

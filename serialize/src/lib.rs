#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![deny(unsafe_code)]
#![doc = include_str!("../README.md")]
mod error;
mod flags;
mod impls;

pub mod serde;

pub use ark_std::io::{Read, Write};

pub use error::*;
pub use flags::*;
pub use serde::{
    CompressedChecked, CompressedUnchecked, UncompressedChecked, UncompressedUnchecked,
};

#[cfg(test)]
mod test;

#[cfg(feature = "derive")]
#[doc(hidden)]
pub use ark_serialize_derive::*;

use digest::{generic_array::GenericArray, Digest, OutputSizeUser};

/// Serializes the given `CanonicalSerialize` items in sequence. `serialize_to_vec![a, b, c, d, e]`
/// is identical to the value of `buf` after `(a, b, c, d, e).serialize_compressed(&mut buf)`.
#[macro_export]
macro_rules! serialize_to_vec {
    ($($x:expr),*) => ({
        let mut buf = ::ark_std::vec![];
        {$crate::serialize_to_vec!(@inner buf, $($x),*)}.map(|_| buf)
    });

    (@inner $buf:expr, $y:expr, $($x:expr),*) => ({
        {
            $crate::CanonicalSerialize::serialize_uncompressed(&$y, &mut $buf)
        }.and({$crate::serialize_to_vec!(@inner $buf, $($x),*)})
    });

    (@inner $buf:expr, $x:expr) => ({
        $crate::CanonicalSerialize::serialize_uncompressed(&$x, &mut $buf)
    });
}

/// Whether to use a compressed version of the serialization algorithm. Specific behavior depends
/// on implementation. If no compressed version exists (e.g. on `Fp`), mode is ignored.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Compress {
    Yes,
    No,
}

/// Whether to validate the element after deserializing it. Specific behavior depends on
/// implementation. If no validation algorithm exists (e.g. on `Fp`), mode is ignored.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Validate {
    Yes,
    No,
}

pub trait Valid: Sync {
    /// Whether the `check` method is trivial (i.e. always returns `Ok(())`). If this is `true`,
    /// the `batch_check` method will skip all checks and return `Ok(())`.
    /// This should be set to `true` for types where `check` is trivial, e.g.
    /// integers, field elements, etc.
    /// This is `false` by default.
    /// This is primarily an optimization to skip unnecessary checks in `batch_check`.
    const TRIVIAL_CHECK: bool = false;

    /// Checks whether `self` is valid. If `self` is valid, returns `Ok(())`. Otherwise, returns
    /// an error describing the failure.
    /// This method is called by `deserialize_with_mode` if `validate` is `Validate::Yes`.
    fn check(&self) -> Result<(), SerializationError>;

    /// Checks whether all items in `batch` are valid. If all items are valid, returns `Ok(())`.
    /// Otherwise, returns an error describing the first failure.
    #[inline]
    fn batch_check<'a>(
        batch: impl Iterator<Item = &'a Self> + Send,
    ) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        if Self::TRIVIAL_CHECK {
            Ok(())
        } else {
            #[cfg(feature = "parallel")]
            {
                use rayon::{iter::ParallelBridge, prelude::ParallelIterator};
                batch.par_bridge().try_for_each(|e| e.check())?;
            }
            #[cfg(not(feature = "parallel"))]
            {
                for item in batch {
                    item.check()?;
                }
            }
            Ok(())
        }
    }
}

/// Serializer in little endian format.
/// This trait can be derived if all fields of a struct implement
/// `CanonicalSerialize` and the `derive` feature is enabled.
///
/// # Example
/// ```
/// // The `derive` feature must be set for the derivation to work.
/// use ark_serialize::*;
///
/// # #[cfg(feature = "derive")]
/// #[derive(CanonicalSerialize)]
/// struct TestStruct {
///     a: u64,
///     b: (u64, (u64, u64)),
/// }
/// ```
pub trait CanonicalSerialize {
    /// The general serialize method that takes in customization flags.
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError>;

    /// Returns the size in bytes of the serialized version of `self` with the given compression mode.
    fn serialized_size(&self, compress: Compress) -> usize;

    /// Serializes `self` into `writer` using the compressed form if applicable.
    fn serialize_compressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::Yes)
    }

    /// Returns the size in bytes of the compressed serialized version of `self`.
    fn compressed_size(&self) -> usize {
        self.serialized_size(Compress::Yes)
    }

    /// Serializes `self` into `writer` using the uncompressed form.
    fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.serialize_with_mode(writer, Compress::No)
    }

    /// Returns the size in bytes of the uncompressed serialized version of `self`.
    fn uncompressed_size(&self) -> usize {
        self.serialized_size(Compress::No)
    }
}

/// Deserializer in little endian format.
/// This trait can be derived if all fields of a struct implement
/// `CanonicalDeserialize` and the `derive` feature is enabled.
///
/// # Example
/// ```
/// // The `derive` feature must be set for the derivation to work.
/// use ark_serialize::*;
///
/// # #[cfg(feature = "derive")]
/// #[derive(CanonicalDeserialize)]
/// struct TestStruct {
///     a: u64,
///     b: (u64, (u64, u64)),
/// }
/// ```
pub trait CanonicalDeserialize: Valid + Sized {
    /// The general deserialize method that takes in customization flags.
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError>;

    /// Reads `Self` from `reader` using the compressed form if applicable.
    /// Performs validation if applicable.
    fn deserialize_compressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_mode(reader, Compress::Yes, Validate::Yes)
    }

    /// Reads `Self` from `reader` using the compressed form if applicable, without validating the
    /// deserialized value.
    ///
    /// # Note
    ///
    /// This should be used with caution, as it may lead to invalid values being used in
    /// subsequent computations, which may have security implications depending on the context.
    ///
    /// It should only be used when the caller can guarantee that the input is valid, e.g. if it was
    /// generated by a trusted source.
    fn deserialize_compressed_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_mode(reader, Compress::Yes, Validate::No)
    }

    /// Reads `Self` from `reader` using the uncompressed form. Performs validation if applicable.
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_mode(reader, Compress::No, Validate::Yes)
    }

    /// Reads `Self` from `reader` using the uncompressed form, without validating the deserialized
    /// value.
    ///
    /// # Note
    ///
    /// This should be used with caution, as it may lead to invalid values being used in
    /// subsequent computations, which may have security implications depending on the context.
    ///
    /// It should only be used when the caller can guarantee that the input is valid, e.g. if it was
    /// generated by a trusted source.
    fn deserialize_uncompressed_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        Self::deserialize_with_mode(reader, Compress::No, Validate::No)
    }
}

/// Serializer in little endian format allowing to encode flags.
pub trait CanonicalSerializeWithFlags: CanonicalSerialize {
    /// Serializes `self` and `flags` into `writer`.
    fn serialize_with_flags<W: Write, F: Flags>(
        &self,
        writer: W,
        flags: F,
    ) -> Result<(), SerializationError>;

    /// Serializes `self` and `flags` into `writer`.
    fn serialized_size_with_flags<F: Flags>(&self) -> usize;
}

/// Deserializer in little endian format allowing flags to be encoded.
pub trait CanonicalDeserializeWithFlags: Sized {
    /// Reads `Self` and `Flags` from `reader`.
    /// Returns empty flags by default.
    fn deserialize_with_flags<R: Read, F: Flags>(
        reader: R,
    ) -> Result<(Self, F), SerializationError>;
}

// This private struct works around Serialize taking the pre-existing
// std::io::Write instance of most digest::Digest implementations by value
struct HashMarshaller<'a, H: Digest>(&'a mut H);

impl<H: Digest> ark_std::io::Write for HashMarshaller<'_, H> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> ark_std::io::Result<usize> {
        Digest::update(self.0, buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> ark_std::io::Result<()> {
        Ok(())
    }
}

/// [`CanonicalSerialize`] induces a natural way to hash a value:
/// serialize it and hash the resulting byte string.
///
/// This is a convenience trait that combines the two steps.
pub trait CanonicalSerializeHashExt: CanonicalSerialize {
    fn hash<H: Digest>(&self) -> GenericArray<u8, <H as OutputSizeUser>::OutputSize> {
        let mut hasher = H::new();
        self.serialize_compressed(HashMarshaller(&mut hasher))
            .expect("HashMarshaller::flush should be infaillible!");
        hasher.finalize()
    }

    fn hash_uncompressed<H: Digest>(&self) -> GenericArray<u8, <H as OutputSizeUser>::OutputSize> {
        let mut hasher = H::new();
        self.serialize_uncompressed(HashMarshaller(&mut hasher))
            .expect("HashMarshaller::flush should be infaillible!");
        hasher.finalize()
    }
}

/// [`CanonicalSerializeHashExt`] is a (blanket) extension trait of
/// `CanonicalSerialize`: all types implementing the latter
/// automatically implement the former.
impl<T: CanonicalSerialize> CanonicalSerializeHashExt for T {}

#[inline]
pub const fn buffer_bit_byte_size(modulus_bits: usize) -> (usize, usize) {
    let byte_size = buffer_byte_size(modulus_bits);
    ((byte_size * 8), byte_size)
}

/// Converts the number of bits required to represent a number
/// into the number of bytes required to represent it.
#[inline]
pub const fn buffer_byte_size(modulus_bits: usize) -> usize {
    modulus_bits.div_ceil(8)
}

use crate::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
    borrow::*,
    collections::{BTreeMap, BTreeSet, LinkedList, VecDeque},
    io::{Read, Write},
    string::*,
    vec::*,
};

macro_rules! impl_valid_seq {
    ($type:ty  $( ; $($extra:tt)+ )?) => {
        impl<T: Valid $( , $($extra)+ )? > Valid for $type {
            const TRIVIAL_CHECK: bool = T::TRIVIAL_CHECK;

            #[inline]
            fn check(&self) -> Result<(), SerializationError> {
                if Self::TRIVIAL_CHECK {
                    Ok(())
                } else {
                    T::batch_check(self.iter())
                }
            }

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
                    T::batch_check(batch.flat_map(|v| v.iter()))
                }
            }
        }

    };
}

macro_rules! impl_canonical_serialize_seq {
    ($type:ty) => {
        impl<T: CanonicalSerialize> CanonicalSerialize for $type {
            #[inline]
            fn serialize_with_mode<W: Write>(
                &self,
                mut writer: W,
                compress: Compress,
            ) -> Result<(), SerializationError> {
                let len = self.len() as u64;
                len.serialize_with_mode(&mut writer, compress)?;
                for item in self.iter() {
                    item.borrow().serialize_with_mode(&mut writer, compress)?;
                }
                Ok(())
            }

            #[inline]
            fn serialized_size(&self, compress: Compress) -> usize {
                8 + self
                    .iter()
                    .map(|item| item.borrow().serialized_size(compress))
                    .sum::<usize>()
            }
        }
    };
}

macro_rules! impl_canonical_deserialize_seq {
    ($type:ty $( ; $($t_bounds:tt)+ )?) => {
        impl<T> CanonicalDeserialize for $type
        where
            T: CanonicalDeserialize $(+ $($t_bounds)+ )?
        {
            #[inline]
            fn deserialize_with_mode<R: Read>(mut reader: R, compress: Compress, validate: Validate) -> Result<Self, SerializationError> {
                let len = u64::deserialize_with_mode(&mut reader, compress, validate)?
                    .try_into()
                    .map_err(|_| SerializationError::NotEnoughSpace)?;

                let values = (0..len)
                    .map(|_| T::deserialize_with_mode(&mut reader, compress, Validate::No))
                    .collect::<Result<Self, SerializationError>>()?;

                if validate == Validate::Yes {
                    T::batch_check(values.iter())?;
                }
                Ok(values)
            }
        }
    };
}

impl<T: CanonicalSerialize, const N: usize> CanonicalSerialize for [T; N] {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        for item in self {
            item.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.iter()
            .map(|item| item.serialized_size(compress))
            .sum::<usize>()
    }
}
impl_valid_seq!([T; N]; const N: usize);

impl<T: CanonicalDeserialize, const N: usize> CanonicalDeserialize for [T; N] {
    #[inline]
    #[allow(unsafe_code)]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        use core::mem::MaybeUninit;
        let mut data: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
        for elem in &mut data[..] {
            elem.write(T::deserialize_with_mode(&mut reader, compress, validate)?);
        }
        Ok(data.map(|x| unsafe { x.assume_init() }))
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for Vec<T> {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.as_slice().serialize_with_mode(&mut writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.as_slice().serialized_size(compress)
    }
}

impl_valid_seq!(Vec<T>);
impl_canonical_deserialize_seq!(Vec<T>);

impl_canonical_serialize_seq!(VecDeque<T>);
impl_valid_seq!(VecDeque<T>);
impl_canonical_deserialize_seq!(VecDeque<T>);

impl_canonical_serialize_seq!(LinkedList<T>);
impl_valid_seq!(LinkedList<T>);
impl_canonical_deserialize_seq!(LinkedList<T>);

impl_canonical_serialize_seq!([T]);
impl_canonical_serialize_seq!(&[T]);
impl_canonical_serialize_seq!(&mut [T]);

impl_canonical_serialize_seq!(ark_std::boxed::Box<[T]>);
impl_valid_seq!(ark_std::boxed::Box<[T]>);
impl_canonical_deserialize_seq!(ark_std::boxed::Box<[T]>);

impl_canonical_serialize_seq!(BTreeSet<T>);
impl_valid_seq!(BTreeSet<T>);
impl_canonical_deserialize_seq!(BTreeSet<T>; Ord);

#[cfg(feature = "std")]
impl_canonical_serialize_seq!(std::collections::HashSet<T>);
#[cfg(feature = "std")]
impl_valid_seq!(std::collections::HashSet<T>);
#[cfg(feature = "std")]
impl_canonical_deserialize_seq!(std::collections::HashSet<T>; core::hash::Hash + Eq);

impl CanonicalSerialize for String {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.as_bytes().serialize_with_mode(&mut writer, compress)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.as_bytes().serialized_size(compress)
    }
}

impl Valid for String {
    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for String {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let bytes = <Vec<u8>>::deserialize_with_mode(reader, compress, validate)?;
        Self::from_utf8(bytes).map_err(|_| SerializationError::InvalidData)
    }
}

impl<K, V> CanonicalSerialize for BTreeMap<K, V>
where
    K: CanonicalSerialize,
    V: CanonicalSerialize,
{
    /// Serializes a `BTreeMap` as `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize_with_mode(&mut writer, compress)?;
        for (k, v) in self {
            k.serialize_with_mode(&mut writer, compress)?;
            v.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        8 + self
            .iter()
            .map(|(k, v)| k.serialized_size(compress) + v.serialized_size(compress))
            .sum::<usize>()
    }
}

impl<K: Valid, V: Valid> Valid for BTreeMap<K, V> {
    const TRIVIAL_CHECK: bool = K::TRIVIAL_CHECK & V::TRIVIAL_CHECK;
    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        if Self::TRIVIAL_CHECK {
            return Ok(());
        }
        if !K::TRIVIAL_CHECK {
            K::batch_check(self.keys())?;
        }
        if !V::TRIVIAL_CHECK {
            V::batch_check(self.values())?;
        }
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(batch: impl Iterator<Item = &'a Self>) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        if Self::TRIVIAL_CHECK {
            return Ok(());
        }
        let (keys, values): (Vec<_>, Vec<_>) = batch.map(|b| (b.keys(), b.values())).unzip();
        if !K::TRIVIAL_CHECK {
            K::batch_check(keys.into_iter().flatten())?;
        }
        if !V::TRIVIAL_CHECK {
            V::batch_check(values.into_iter().flatten())?;
        }
        Ok(())
    }
}

impl<K, V> CanonicalDeserialize for BTreeMap<K, V>
where
    K: Ord + CanonicalDeserialize,
    V: CanonicalDeserialize,
{
    /// Deserializes a `BTreeMap` from `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let len = u64::deserialize_with_mode(&mut reader, compress, validate)?;
        (0..len)
            .map(|_| {
                Ok((
                    K::deserialize_with_mode(&mut reader, compress, validate)?,
                    V::deserialize_with_mode(&mut reader, compress, validate)?,
                ))
            })
            .collect()
    }
}

#[cfg(feature = "std")]
impl<K, V> CanonicalSerialize for std::collections::HashMap<K, V>
where
    K: CanonicalSerialize,
    V: CanonicalSerialize,
{
    /// Serializes a `HashMap` as `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize_with_mode(&mut writer, compress)?;
        for (k, v) in self {
            k.serialize_with_mode(&mut writer, compress)?;
            v.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        8 + self
            .iter()
            .map(|(k, v)| k.serialized_size(compress) + v.serialized_size(compress))
            .sum::<usize>()
    }
}

#[cfg(feature = "std")]
impl<K: Valid, V: Valid> Valid for std::collections::HashMap<K, V> {
    const TRIVIAL_CHECK: bool = K::TRIVIAL_CHECK & V::TRIVIAL_CHECK;
    #[inline]
    fn check(&self) -> Result<(), SerializationError> {
        if Self::TRIVIAL_CHECK {
            return Ok(());
        }
        if !K::TRIVIAL_CHECK {
            K::batch_check(self.keys())?;
        }
        if !V::TRIVIAL_CHECK {
            V::batch_check(self.values())?;
        }
        Ok(())
    }

    #[inline]
    fn batch_check<'a>(batch: impl Iterator<Item = &'a Self>) -> Result<(), SerializationError>
    where
        Self: 'a,
    {
        if Self::TRIVIAL_CHECK {
            return Ok(());
        }
        let (keys, values): (Vec<_>, Vec<_>) = batch.map(|b| (b.keys(), b.values())).unzip();
        if !K::TRIVIAL_CHECK {
            K::batch_check(keys.into_iter().flatten())?;
        }
        if !V::TRIVIAL_CHECK {
            V::batch_check(values.into_iter().flatten())?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<K, V> CanonicalDeserialize for std::collections::HashMap<K, V>
where
    K: core::hash::Hash + Eq + CanonicalDeserialize,
    V: CanonicalDeserialize,
{
    /// Deserializes a `HashMap` from `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let len = u64::deserialize_with_mode(&mut reader, compress, validate)?;
        (0..len)
            .map(|_| {
                Ok((
                    K::deserialize_with_mode(&mut reader, compress, validate)?,
                    V::deserialize_with_mode(&mut reader, compress, validate)?,
                ))
            })
            .collect()
    }
}

use super::*;
use ark_std::{
    collections::{BTreeMap, BTreeSet, LinkedList, VecDeque},
    rand::RngCore,
    string::*,
    vec,
    vec::*,
};
use num_bigint::BigUint;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
struct Dummy;

impl CanonicalSerialize for Dummy {
    #[inline]
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match compress {
            Compress::Yes => 100u8.serialize_compressed(&mut writer),
            Compress::No => [100u8, 200u8].serialize_compressed(&mut writer),
        }
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        match compress {
            Compress::Yes => 1,
            Compress::No => 2,
        }
    }
}

impl Valid for Dummy {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl CanonicalDeserialize for Dummy {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        reader: R,
        compress: Compress,
        _validate: Validate,
    ) -> Result<Self, SerializationError> {
        match compress {
            Compress::Yes => assert_eq!(u8::deserialize_compressed(reader)?, 100u8),
            Compress::No => {
                assert_eq!(<[u8; 2]>::deserialize_compressed(reader)?, [100u8, 200u8])
            },
        }
        Ok(Dummy)
    }
}

fn test_serialize<T: PartialEq + core::fmt::Debug + CanonicalSerialize + CanonicalDeserialize>(
    data: T,
) {
    for compress in [Compress::Yes, Compress::No] {
        for validate in [Validate::Yes, Validate::No] {
            let mut serialized = vec![0; data.serialized_size(compress)];
            data.serialize_with_mode(&mut serialized[..], compress)
                .unwrap();
            let de = T::deserialize_with_mode(&serialized[..], compress, validate).unwrap();
            assert_eq!(data, de);
        }
    }
}

fn test_hash<T: CanonicalSerialize, H: Digest + core::fmt::Debug>(data: T) {
    let h1 = data.hash::<H>();

    let mut hash = H::new();
    let mut serialized = vec![0; data.serialized_size(Compress::Yes)];
    data.serialize_compressed(&mut serialized[..]).unwrap();
    hash.update(&serialized);
    let h2 = hash.finalize();

    assert_eq!(h1, h2);

    let h3 = data.hash_uncompressed::<H>();

    let mut hash = H::new();
    serialized = vec![0; data.uncompressed_size()];
    data.serialize_uncompressed(&mut serialized[..]).unwrap();
    hash.update(&serialized);
    let h4 = hash.finalize();

    assert_eq!(h3, h4);
}

// Serialize T, randomly mutate the data, and deserialize it.
// Ensure it fails.
// Up to the caller to provide a valid mutation criterion
// to ensure that this test always fails.
// This method requires a concrete instance of the data to be provided,
// to get the serialized size.
fn ensure_non_malleable_encoding<
    T: PartialEq + core::fmt::Debug + CanonicalSerialize + CanonicalDeserialize,
>(
    data: T,
    valid_mutation: fn(&[u8]) -> bool,
) {
    let mut r = ark_std::test_rng();
    let mut serialized = vec![0; data.compressed_size()];
    r.fill_bytes(&mut serialized);
    while !valid_mutation(&serialized) {
        r.fill_bytes(&mut serialized);
    }
    let de = T::deserialize_compressed(&serialized[..]);
    assert!(de.is_err());

    let mut serialized = vec![0; data.uncompressed_size()];
    r.fill_bytes(&mut serialized);
    while !valid_mutation(&serialized) {
        r.fill_bytes(&mut serialized);
    }
    let de = T::deserialize_uncompressed(&serialized[..]);
    assert!(de.is_err());
}

#[test]
fn test_array() {
    test_serialize([1u64, 2, 3, 4, 5]);
    test_serialize([1u8; 33]);
}

#[test]
fn test_array_bad_input() {
    // Does not panic on invalid data:
    let serialized = vec![0u8; 1];
    assert!(<[u8; 2]>::deserialize_compressed(&serialized[..]).is_err());
}

#[test]
fn test_vec() {
    test_serialize(vec![1u64, 2, 3, 4, 5]);
    test_serialize(Vec::<u64>::new());
}

#[test]
fn test_vecdeque() {
    test_serialize([1u64, 2, 3, 4, 5].into_iter().collect::<VecDeque<_>>());
    test_serialize(VecDeque::<u64>::new());
}

#[test]
fn test_linkedlist() {
    test_serialize([1u64, 2, 3, 4, 5].into_iter().collect::<LinkedList<_>>());
    test_serialize(LinkedList::<u64>::new());
}

#[test]
fn test_uint() {
    test_serialize(192830918usize);
    test_serialize(192830918u64);
    test_serialize(192830918u32);
    test_serialize(22313u16);
    test_serialize(123u8);
}

#[test]
fn test_string() {
    test_serialize(String::from("arkworks"));
}

#[test]
fn test_tuple() {
    test_serialize(());
    test_serialize((123u64, Dummy));
    test_serialize((123u64, 234u32, Dummy));
}

#[test]
fn test_tuple_vec() {
    test_serialize(vec![
        (Dummy, Dummy, Dummy),
        (Dummy, Dummy, Dummy),
        (Dummy, Dummy, Dummy),
    ]);
    test_serialize(vec![
        (86u8, 98u64, Dummy),
        (86u8, 98u64, Dummy),
        (86u8, 98u64, Dummy),
    ]);
}

#[test]
fn test_option() {
    test_serialize(Some(Dummy));
    test_serialize(None::<Dummy>);

    test_serialize(Some(10u64));
    test_serialize(None::<u64>);
}

#[test]
fn test_bool() {
    test_serialize(true);
    test_serialize(false);

    let valid_mutation = |data: &[u8]| -> bool { data.len() == 1 && data[0] > 1 };
    for _ in 0..10 {
        ensure_non_malleable_encoding(true, valid_mutation);
        ensure_non_malleable_encoding(false, valid_mutation);
    }
}

#[test]
fn test_rc_arc() {
    use ark_std::sync::Arc;
    test_serialize(Arc::new(Dummy));
    test_serialize(Arc::new(10u64));
}

#[test]
fn test_btreemap() {
    let mut map = BTreeMap::new();
    map.insert(0u64, Dummy);
    map.insert(5u64, Dummy);
    test_serialize(map);
    let mut map = BTreeMap::new();
    map.insert(10u64, vec![1u8, 2u8, 3u8]);
    map.insert(50u64, vec![4u8, 5u8, 6u8]);
    test_serialize(map);
}

#[test]
fn test_btreeset() {
    let mut set = BTreeSet::new();
    set.insert(Dummy);
    set.insert(Dummy);
    test_serialize(set);
    let mut set = BTreeSet::new();
    set.insert(vec![1u8, 2u8, 3u8]);
    set.insert(vec![4u8, 5u8, 6u8]);
    test_serialize(set);
}

#[test]
fn test_phantomdata() {
    test_serialize(core::marker::PhantomData::<Dummy>);
}

#[test]
fn test_sha2() {
    test_hash::<_, sha2::Sha256>(Dummy);
    test_hash::<_, sha2::Sha512>(Dummy);
}

#[test]
fn test_blake2() {
    test_hash::<_, blake2::Blake2b512>(Dummy);
    test_hash::<_, blake2::Blake2s256>(Dummy);
}

#[test]
fn test_sha3() {
    test_hash::<_, sha3::Sha3_256>(Dummy);
    test_hash::<_, sha3::Sha3_512>(Dummy);
}

#[test]
fn test_biguint() {
    let biguint = BigUint::from(123456u64);
    test_serialize(biguint.clone());

    let mut expected = (biguint.to_bytes_le().len() as u64).to_le_bytes().to_vec();
    expected.extend_from_slice(&biguint.to_bytes_le());

    let mut bytes = Vec::new();
    biguint
        .serialize_with_mode(&mut bytes, Compress::Yes)
        .unwrap();
    assert_eq!(bytes, expected);

    let mut bytes = Vec::new();
    biguint
        .serialize_with_mode(&mut bytes, Compress::No)
        .unwrap();
    assert_eq!(bytes, expected);
}

#[test]
fn test_serialize_macro() {
    // Make a bunch of distinctly typed values
    let val1 = [vec![1u8, 2u8, 3u8], vec![4u8, 5u8, 6u8]]
        .into_iter()
        .collect::<BTreeSet<_>>();
    let val2: core::marker::PhantomData<Dummy> = core::marker::PhantomData;
    let val3 = Some(10u64);
    let val4 = 192830918usize;
    let val5 = [1u64, 2, 3, 4, 5].into_iter().collect::<LinkedList<_>>();

    // Make sure the serialization macro matches just serializing them as a tuple
    let mut tuple_bytes = Vec::new();
    (
        val1.clone(),
        val2.clone(),
        val3.clone(),
        val4.clone(),
        val5.clone(),
    )
        .serialize_uncompressed(&mut tuple_bytes)
        .unwrap();
    let macro_bytes = serialize_to_vec![val1, val2, val3, val4, val5].unwrap();

    assert_eq!(tuple_bytes, macro_bytes);
}

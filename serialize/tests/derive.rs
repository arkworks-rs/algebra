#![cfg(feature = "derive")]

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug, PartialEq)]
struct Unit;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug, PartialEq)]
struct EmptyNamed {}

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug, PartialEq)]
struct EmptyTuple();

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug, PartialEq)]
struct WithEmpty {
    a: u64,
    b: Unit,
}

fn roundtrip<T: CanonicalSerialize + CanonicalDeserialize + core::fmt::Debug + PartialEq>(t: T) {
    let mut buf = Vec::new();
    t.serialize_compressed(&mut buf).unwrap();
    assert_eq!(buf.len(), t.compressed_size());
    assert_eq!(T::deserialize_compressed(&buf[..]).unwrap(), t);
}

#[test]
fn derive_on_fieldless_structs() {
    assert!(Unit::TRIVIAL_CHECK);
    assert!(EmptyNamed::TRIVIAL_CHECK);
    assert!(EmptyTuple::TRIVIAL_CHECK);
    assert_eq!(Unit.compressed_size(), 0);

    roundtrip(Unit);
    roundtrip(EmptyNamed {});
    roundtrip(EmptyTuple());
    roundtrip(WithEmpty { a: 7, b: Unit });
}

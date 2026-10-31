//! The derive output must not depend on `Result`/`Ok` from the caller's scope.
#![cfg(feature = "derive")]

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[allow(dead_code)]
type Result<T> = core::result::Result<T, ()>;

#[allow(dead_code)]
enum Shadow {
    Ok,
}
#[allow(unused_imports)]
use Shadow::Ok;

#[derive(CanonicalSerialize, CanonicalDeserialize, PartialEq, Debug)]
struct Named {
    a: u64,
    b: u32,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, PartialEq, Debug)]
struct Tuple(u64, u8);

#[test]
fn derive_with_shadowed_result_and_ok() {
    let named = Named { a: 7, b: 9 };
    let mut bytes = vec![];
    named.serialize_compressed(&mut bytes).unwrap();
    assert_eq!(Named::deserialize_compressed(&bytes[..]).unwrap(), named);

    let tuple = Tuple(1, 2);
    let mut bytes = vec![];
    tuple.serialize_compressed(&mut bytes).unwrap();
    assert_eq!(Tuple::deserialize_compressed(&bytes[..]).unwrap(), tuple);
}

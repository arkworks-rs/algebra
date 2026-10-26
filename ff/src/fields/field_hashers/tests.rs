use ark_test_curves::{
    ark_ff::{
        field_hashers::{DefaultFieldHasher, HashToField},
        PrimeField,
    },
    secp256k1::Fq,
};
use sha2::Sha256;

#[derive(serde_derive::Deserialize)]
struct SuiteVector {
    dst: String,
    vectors: Vec<Vector>,
}

#[derive(serde_derive::Deserialize)]
struct Vector {
    msg: String,
    u: Vec<String>,
}

/// RFC 9380 suite on a field where the element length `L = 48` differs from the
/// SHA-256 input block size of 64 bytes. The BLS12-381 suites cannot detect a
/// wrong `Z_pad` length because there `L` equals the block size.
///
/// The vectors are `poc/vectors/secp256k1_XMD:SHA-256_SSWU_RO_.json` from
/// <https://github.com/cfrg/draft-irtf-cfrg-hash-to-curve>, the same values
/// as RFC 9380 Appendix J.8.1.
#[test]
fn hash_to_field_matches_rfc9380_secp256k1() {
    let suite: SuiteVector =
        serde_json::from_str(include_str!("testdata/secp256k1_XMD-SHA-256_SSWU_RO_.json")).unwrap();
    let hasher = <DefaultFieldHasher<Sha256> as HashToField<Fq>>::new(suite.dst.as_bytes());

    for vector in suite.vectors {
        let got: [Fq; 2] = hasher.hash_to_field(vector.msg.as_bytes());
        let want: Vec<Fq> = vector
            .u
            .iter()
            .map(|element| {
                Fq::from_be_bytes_mod_order(&hex::decode(element.trim_start_matches("0x")).unwrap())
            })
            .collect();
        assert_eq!(got.as_slice(), want.as_slice(), "msg = {:?}", vector.msg);
    }
}

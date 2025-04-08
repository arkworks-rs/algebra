use ark_algebra_test_templates::*;
use ark_ec::{
    hashing::{
        curve_maps::svdw::{SVDWConfig, SVDWMap},
        map_to_curve_hasher::MapToCurveBasedHasher,
        HashToCurve,
    },
    short_weierstrass::Projective,
};
use ark_ff::field_hashers::DefaultFieldHasher;
use ark_ff::fields::Field;
use ark_std::Zero;

use crate::{Bn254, G1Projective, G2Projective};

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bn254>; msm);
test_pairing!(pairing; crate::Bn254);
test_group!(g1_glv; G1Projective; glv);
test_group!(g2_glv; G2Projective; glv);

/// make a simple hash
fn svdw_hash_arbitrary_string_to_curve<SVDWCurve: SVDWConfig>() {
    use sha2::Sha256;
    let test_svdw_to_curve_hasher = MapToCurveBasedHasher::<
        Projective<SVDWCurve>,
        DefaultFieldHasher<Sha256, 128>,
        SVDWMap<SVDWCurve>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_svdw_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

    assert!(
        hash_result.x != SVDWCurve::BaseField::zero()
            && hash_result.y != SVDWCurve::BaseField::zero(),
        "we assume that not both a and b coefficienst are zero for the test curve"
    );

    assert!(
        hash_result.is_on_curve(),
        "hash results into a point off the curve"
    );
}

#[test]
fn svdw_hash_arbitrary_string_to_g1() {
    svdw_hash_arbitrary_string_to_curve::<crate::g1::Config>();
}

#[test]
fn svdw_hash_arbitrary_string_to_g2() {
    svdw_hash_arbitrary_string_to_curve::<crate::g2::Config>();
}

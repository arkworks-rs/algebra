use crate::{Bls12_377, G1Projective, G2Projective};
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bls12_377>; msm);
test_pairing!(pairing; crate::Bls12_377);
test_group!(g1_glv; G1Projective; glv);
test_group!(g2_glv; G2Projective; glv);
test_h2c!(g1_h2c; "./src/curves/tests"; "BLS12377G1"; crate::g1::Config; crate::Fq; crate::Fq; 1);
test_h2c!(g2_hc2; "./src/curves/tests"; "BLS12377G2"; crate::g2::Config; crate::Fq2; crate::Fq; 2);

#[cfg(test)]
mod test {
    use ark_ec::{
        hashing::{
            curve_maps::wb::{WBConfig, WBMap},
            map_to_curve_hasher::MapToCurveBasedHasher,
            HashToCurve,
        },
        short_weierstrass::Projective,
    };
    use ark_ff::field_hashers::DefaultFieldHasher;
    use ark_std::Zero;

    /// make a simple hash
    fn wb_hash_arbitrary_string_to_curve<WBCurve: WBConfig>() {
        use sha2::Sha256;
        let test_wb_to_curve_hasher = MapToCurveBasedHasher::<
            Projective<WBCurve>,
            DefaultFieldHasher<Sha256, 128>,
            WBMap<WBCurve>,
        >::new(&[1])
        .unwrap();

        let hash_result = test_wb_to_curve_hasher.hash(b"if you stick a Babel fish in your ear you can instantly understand anything said to you in any form of language.").expect("fail to hash the string to curve");

        assert!(
            hash_result.x != WBCurve::BaseField::zero()
                && hash_result.y != WBCurve::BaseField::zero(),
            "we assume that not both a and b coefficienst are zero for the test curve"
        );

        assert!(
            hash_result.is_on_curve(),
            "hash results into a point off the curve"
        );
    }

    #[test]
    fn wb_hash_arbitrary_string_to_g1() {
        wb_hash_arbitrary_string_to_curve::<crate::g1::Config>();
    }

    #[test]
    fn wb_hash_arbitrary_string_to_g2() {
        wb_hash_arbitrary_string_to_curve::<crate::g2::Config>();
    }
}

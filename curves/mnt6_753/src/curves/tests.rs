use crate::*;
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; 100; sw);
test_group!(g2; G2Projective; 100; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<MNT6_753>; 100; msm);
test_pairing!(pairing; crate::MNT6_753);

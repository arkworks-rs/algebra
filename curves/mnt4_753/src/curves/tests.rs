use crate::*;
use ark_algebra_test_templates::*;

test_group!(50; g1; G1Projective; sw);
test_group!(50; g2; G2Projective; sw);
test_group!(50; pairing_output; ark_ec::pairing::PairingOutput<MNT4_753>; msm);
test_pairing!(pairing; crate::MNT4_753);
test_g2_prepared!(g2_prepared; crate::MNT4_753; double_coefficients, addition_coefficients);

use crate::*;
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<MNT4_298>; msm);
test_pairing!(pairing; crate::MNT4_298);
test_g2_prepared!(g2_prepared; crate::MNT4_298; double_coefficients, addition_coefficients);

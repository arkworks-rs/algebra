use ark_algebra_test_templates::*;
use ark_ff::Field;

use crate::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<CP6_782>; msm);
test_pairing!(pairing; crate::CP6_782);

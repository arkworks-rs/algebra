use ark_algebra_test_templates::*;
use ark_ff::fields::Field;

use crate::{Bn254, G1Projective, G2Projective};

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Bn254>; msm);
test_pairing!(pairing; crate::Bn254);
test_group!(g1_glv; G1Projective; glv);
test_group!(g2_glv; G2Projective; glv);

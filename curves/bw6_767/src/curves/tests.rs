use crate::*;
use ark_algebra_test_templates::*;
use ark_ff::Field;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<BW6_767>; msm);
test_pairing!(pairing; crate::BW6_767);

#[test]
fn test_final_exponentiation_of_zero() {
    use ark_ec::pairing::{MillerLoopOutput, Pairing};
    use ark_ff::Zero;

    assert!(BW6_767::final_exponentiation(MillerLoopOutput(Fq6::zero())).is_none());
}

use crate::*;
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<MNT4_298>; msm);
test_pairing!(pairing; crate::MNT4_298);

#[test]
fn test_pairing_with_zero() {
    use ark_ec::pairing::Pairing;
    use ark_std::{test_rng, UniformRand, Zero};

    let rng = &mut test_rng();
    let a = <MNT4_298 as Pairing>::G1::rand(rng);
    let b = <MNT4_298 as Pairing>::G2::rand(rng);
    let zero_g1 = <MNT4_298 as Pairing>::G1::zero();
    let zero_g2 = <MNT4_298 as Pairing>::G2::zero();

    assert_eq!(
        <MNT4_298>::pairing(a, zero_g2),
        ark_ec::pairing::PairingOutput::zero()
    );
    assert_eq!(
        <MNT4_298>::pairing(zero_g1, b),
        ark_ec::pairing::PairingOutput::zero()
    );
    assert_eq!(
        <MNT4_298>::pairing(zero_g1, zero_g2),
        ark_ec::pairing::PairingOutput::zero()
    );
}

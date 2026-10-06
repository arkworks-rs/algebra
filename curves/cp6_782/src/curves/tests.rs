use ark_algebra_test_templates::*;
use ark_ff::Field;

use crate::*;

test_group!(50; g1; G1Projective; sw);
test_group!(10; g2; G2Projective; sw);
test_group!(10; pairing_output; ark_ec::pairing::PairingOutput<CP6_782>; msm);
test_pairing!(25; pairing; crate::CP6_782);

#[test]
fn test_pairing_with_identity() {
    use ark_ec::{pairing::Pairing, AffineRepr, PrimeGroup};
    use ark_std::{test_rng, UniformRand, Zero};

    let mut rng = test_rng();
    let p = G1Projective::rand(&mut rng);
    let q = G2Projective::rand(&mut rng);

    assert!(CP6_782::pairing(p, G2Affine::zero()).is_zero());
    assert!(CP6_782::pairing(G1Affine::zero(), q).is_zero());
    assert!(CP6_782::pairing(G1Affine::zero(), G2Affine::zero()).is_zero());

    let g = G1Projective::generator();
    let h = G2Projective::generator();
    assert_eq!(
        CP6_782::multi_pairing([p, G1Projective::zero(), g], [q, h, G2Projective::zero()]),
        CP6_782::pairing(p, q)
    );
}

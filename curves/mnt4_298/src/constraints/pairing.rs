use crate::Config;

/// Specifies the constraints for computing a pairing in the MNT4-298 bilinear
/// group.
pub type PairingVar = ark_r1cs_std::pairing::mnt4::PairingVar<Config>;

#[test]
fn test() {
    use crate::MNT4_298;
    ark_curve_constraint_tests::pairing::bilinearity_test::<MNT4_298, PairingVar>().unwrap();
    ark_curve_constraint_tests::pairing::g2_prepare_consistency_test::<MNT4_298, PairingVar>()
        .unwrap();
}

use ark_r1cs_std::groups::mnt6;

use crate::Config;

/// An element of G1 in the MNT6-753 bilinear group.
pub type G1Var = mnt6::G1Var<Config>;
/// An element of G2 in the MNT6-753 bilinear group.
pub type G2Var = mnt6::G2Var<Config>;

/// Represents the cached precomputation that can be performed on a G1 element
/// which enables speeding up pairing computation.
pub type G1PreparedVar = mnt6::G1PreparedVar<Config>;
/// Represents the cached precomputation that can be performed on a G2 element
/// which enables speeding up pairing computation.
pub type G2PreparedVar = mnt6::G2PreparedVar<Config>;

#[test]
fn test() {
    use ark_ec::models::mnt6::MNT6Config;
    ark_curve_constraint_tests::curves::sw_test::<<Config as MNT6Config>::G1Config, G1Var>()
        .unwrap();
    ark_curve_constraint_tests::curves::sw_test::<<Config as MNT6Config>::G2Config, G2Var>()
        .unwrap();
}

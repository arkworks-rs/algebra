use ark_r1cs_std::groups::mnt4;

use crate::Config;

/// An element of G1 in the MNT4-753 bilinear group.
pub type G1Var = mnt4::G1Var<Config>;
/// An element of G2 in the MNT4-753 bilinear group.
pub type G2Var = mnt4::G2Var<Config>;

/// Represents the cached precomputation that can be performed on a G1 element
/// which enables speeding up pairing computation.
pub type G1PreparedVar = mnt4::G1PreparedVar<Config>;
/// Represents the cached precomputation that can be performed on a G2 element
/// which enables speeding up pairing computation.
pub type G2PreparedVar = mnt4::G2PreparedVar<Config>;

#[test]
fn test() {
    use ark_ec::models::mnt4::MNT4Config;
    ark_curve_constraint_tests::curves::sw_test::<<Config as MNT4Config>::G1Config, G1Var>()
        .unwrap();
    ark_curve_constraint_tests::curves::sw_test::<<Config as MNT4Config>::G2Config, G2Var>()
        .unwrap();
}

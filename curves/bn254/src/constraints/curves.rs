use ark_r1cs_std::groups::curves::short_weierstrass::ProjectiveVar;

use crate::{constraints::FBaseVar, g1::Config};

/// A group element in the Bn254 prime-order group.
pub type GVar = ProjectiveVar<Config, FBaseVar>;

#[test]
fn test() {
    ark_curve_constraint_tests::curves::sw_test::<Config, GVar>().unwrap();
}

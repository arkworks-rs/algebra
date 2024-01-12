use ark_r1cs_std::groups::curves::short_weierstrass::ProjectiveVar;

use crate::{constraints::FBaseVar, *};

/// A group element in the Vesta prime-order group.
pub type GVar = ProjectiveVar<VestaConfig, FBaseVar>;

#[test]
fn test() {
    ark_curve_constraint_tests::curves::sw_test::<VestaConfig, GVar>().unwrap();
}

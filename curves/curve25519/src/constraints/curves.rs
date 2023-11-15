use ark_r1cs_std::groups::curves::twisted_edwards::{AffineVar, MontgomeryAffineVar};

use crate::{constraints::FqVar, *};

/// A variable that is the R1CS equivalent of `crate::EdwardsAffine`.
pub type EdwardsVar = AffineVar<Curve25519Config, FqVar>;

/// A variable that is the R1CS equivalent of `crate::NonZeroMontgomeryAffine`.
pub type NonZeroMontgomeryVar = MontgomeryAffineVar<Curve25519Config, FqVar>;

#[test]
fn test() {
    ark_curve_constraint_tests::curves::te_test::<Curve25519Config, EdwardsVar>().unwrap();
}

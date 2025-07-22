use crate::{constraints::FqVar, *};
use ark_r1cs_std::groups::curves::short_weierstrass::ProjectiveVar;

/// A group element in the Jq255s curve.
pub type GVar = ProjectiveVar<Config, FqVar>;

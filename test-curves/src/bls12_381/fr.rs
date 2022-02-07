use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[generator = "7"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

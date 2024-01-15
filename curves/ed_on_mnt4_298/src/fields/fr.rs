use ark_ff::fields::{Fp320, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631"]
#[generator = "7"]
pub struct FrConfig;
pub type Fr = Fp320<MontBackend<FrConfig, 5>>;

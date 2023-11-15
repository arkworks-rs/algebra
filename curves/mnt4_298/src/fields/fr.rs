use ark_ff::fields::{Fp320, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "475922286169261325753349249653048451545124878552823515553267735739164647307408490559963137"]
#[generator = "10"]
pub struct FrConfig;
pub type Fr = Fp320<MontBackend<FrConfig, 5>>;

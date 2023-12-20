use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "2736030358979909402780800718157159386076813972158567259200215660948447373041"]
#[generator = "31"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "115792089210356248762697446949407573529996955224135760342422259061068512044369"]
#[generator = "11"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

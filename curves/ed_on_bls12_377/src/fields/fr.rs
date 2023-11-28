use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "2111115437357092606062206234695386632838870926408408195193685246394721360383"]
#[generator = "5"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

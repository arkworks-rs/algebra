use ark_ff::fields::{Fp384, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "32333053251621136751331591711861691692049189094364332567435817881934511297123972799646723302813083835942624121493"]
#[generator = "13"]
pub struct FrConfig;
pub type Fr = Fp384<MontBackend<FrConfig, 6>>;

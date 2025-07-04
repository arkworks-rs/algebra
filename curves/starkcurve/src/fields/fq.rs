use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[generator = "3"]
pub struct FqConfig;
pub type Fq = Fp256<MontBackend<FqConfig, 4>>;

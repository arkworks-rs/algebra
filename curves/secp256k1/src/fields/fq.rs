use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "115792089237316195423570985008687907853269984665640564039457584007908834671663"]
#[generator = "3"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "1"]
pub struct FqConfig;
pub type Fq = Fp256<MontBackend<FqConfig, 4>>;

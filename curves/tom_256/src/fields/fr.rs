use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "115792089210356248762697446949407573530594504085698471288169790229257723883799"]
#[generator = "7"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "1"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

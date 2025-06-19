use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "7237005577332262213973186563042994240857116359379907606001950938285454250989"]
#[generator = "2"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "1"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

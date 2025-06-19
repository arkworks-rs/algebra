use ark_ff::fields::{Fp320, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "475922286169261325753349249653048451545124879242694725395555128576210262817955800483758081"]
#[generator = "17"]
#[small_subgroup_base = "7"]
#[small_subgroup_power = "2"]
pub struct FqConfig;
pub type Fq = Fp320<MontBackend<FqConfig, 5>>;

use ark_ff::fields::{Fp384, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "5945877603251831796258517492029536515488649313567122628445038208291596545947608789992834434053176523624102324539393"]
#[generator = "5"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "2"]
pub struct FrConfig;
pub type Fr = Fp384<MontBackend<FrConfig, 6>>;

pub const FR_ONE: Fr = ark_ff::MontFp!(Fr, "1");
pub const FR_ZERO: Fr = ark_ff::MontFp!(Fr, "0");

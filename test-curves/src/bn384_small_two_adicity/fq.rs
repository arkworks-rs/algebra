use ark_ff::fields::{Fp384, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "5945877603251831796258517492029536515488649313567122628447476625319762940580461319088175968449723373773214087057409"]
#[generator = "7"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "2"]
pub struct FqConfig;
pub type Fq = Fp384<MontBackend<FqConfig, 6>>;

pub const FQ_ONE: Fq = ark_ff::MontFp!(Fq, "1");
pub const FQ_ZERO: Fq = ark_ff::MontFp!(Fq, "0");

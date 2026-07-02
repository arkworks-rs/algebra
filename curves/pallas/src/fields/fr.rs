use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "28948022309329048855892746252171976963363056481941647379679742748393362948097"]
#[generator = "5"]
#[sqrt_precomp = "crate::fields::fr_sqrt_table::SQRT_PRECOMP"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

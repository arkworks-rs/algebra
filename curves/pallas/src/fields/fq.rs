use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "28948022309329048855892746252171976963363056481941560715954676764349967630337"]
#[generator = "5"]
#[sqrt_precomp = "crate::fields::fq_sqrt_table::SQRT_PRECOMP"]
pub struct FqConfig;
pub type Fq = Fp256<MontBackend<FqConfig, 4>>;

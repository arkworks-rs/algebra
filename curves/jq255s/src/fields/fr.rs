use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "28948022309329048855892746252171976963374400301680813836675510354995316871879"]
#[generator = "7"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

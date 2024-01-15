use ark_ff::fields::{Fp384, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643"]
#[generator = "2"]
pub struct FrConfig;
pub type Fr = Fp384<MontBackend<FrConfig, 6>>;

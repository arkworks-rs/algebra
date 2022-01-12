use ark_ff::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, MontBackend, MontConfig, MontFp},
    BigInt,
};

pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

impl MontConfig<4> for FrConfig {
    /// MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    const MODULUS: BigInteger =
        BigInt!("52435875175126190479447740508185965837690552500527637822603658699938581184513");

    /// GENERATOR = 7
    const GENERATOR: Fr = MontFp!(Fr, "7");

    const TWO_ADIC_ROOT_OF_UNITY: Fr = MontFp!(
        Fr,
        "10238227357739495823651030575849232062558860180284477541189508159991286009131"
    );
}

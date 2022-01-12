use ark_ff::{
    biginteger::BigInt,
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, MontBackend, MontConfig, MontFp},
};

pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

impl MontConfig<4> for FrConfig {
    /// MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInt::<4>([
        0xffffffff00000001,
        0x53bda402fffe5bfe,
        0x3339d80809a1d805,
        0x73eda753299d7d48,
    ]);

    /// GENERATOR = 7
    /// Encoded in Montgomery form, so the value here is
    /// 7 * R % q = 24006497034320510773280787438025867407531605151569380937148207556313189711857
    #[rustfmt::skip]
    const GENERATOR: Fr = MontFp!(Fr, "7");

    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: Fr = MontFp!(Fr, "10238227357739495823651030575849232062558860180284477541189508159991286009131");
}

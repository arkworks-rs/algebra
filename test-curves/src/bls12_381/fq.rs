use ark_ff::fields::{Fp384, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"]
#[generator = "2"]
pub struct FqConfig;
pub type Fq = Fp384<MontBackend<FqConfig, 6>>;

pub const FQ_ONE: Fq = ark_ff::MontFp!("1");
pub const FQ_ZERO: Fq = ark_ff::MontFp!("0");

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;

    use super::*;
    use ark_ff::{BigInt, FpConfig, One};

    #[test]
    fn test_constants() {
        use ark_ff::{MontConfig, PrimeField};
        assert_eq!(Fq::MODULUS_BIT_SIZE, 381);

        assert_eq!(FqConfig::INV, 0x89f3fffcfffcfffd);

        // R = 3380320199399472671518931668520476396067793891014375699959770179129436917079669831430077592723774664465579537268733
        assert_eq!(
            FqConfig::R,
            BigInt::<6>([
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ])
        );

        assert_eq!(
            FqConfig::R2,
            BigInt::<6>([
                0xf4df1f341c341746,
                0xa76e6a609d104f1,
                0x8de5476c4c95b6d5,
                0x67eb88a9939d83c0,
                0x9a793e85b519952d,
                0x11988fe592cae3aa,
            ])
        );

        assert_eq!(
            Fq::TRACE,
            BigInt::<6>([
                0xdcff7fffffffd555,
                0xf55ffff58a9ffff,
                0xb39869507b587b12,
                0xb23ba5c279c2895f,
                0x258dd3db21a5d66b,
                0xd0088f51cbff34d,
            ])
        );
        assert_eq!(
            Fq::MODULUS_MINUS_ONE_DIV_TWO,
            BigInt::<6>([
                0xdcff7fffffffd555,
                0xf55ffff58a9ffff,
                0xb39869507b587b12,
                0xb23ba5c279c2895f,
                0x258dd3db21a5d66b,
                0xd0088f51cbff34d,
            ])
        );

        assert_eq!(
            Fq::TRACE_MINUS_ONE_DIV_TWO,
            BigInt::<6>([
                0xee7fbfffffffeaaa,
                0x7aaffffac54ffff,
                0xd9cc34a83dac3d89,
                0xd91dd2e13ce144af,
                0x92c6e9ed90d2eb35,
                0x680447a8e5ff9a6,
            ])
        );
        // GENERATOR = 2
        // Encoded in Montgomery form, so the value is
        // 2 * R % q =
        // 2758230843577277949620073511305048635578704962089743514587482222134842183668501798417467556318533664893264801977679
        assert_eq!(
            FqConfig::GENERATOR,
            ark_ff::Fp(
                BigInt::new([
                    0x321300000006554f,
                    0xb93c0018d6c40005,
                    0x57605e0db0ddbb51,
                    0x8b256521ed1f9bcb,
                    0x6cf28d7901622c03,
                    0x11ebab9dbb81e28c,
                ]),
                PhantomData
            )
        );

        assert_eq!(FQ_ONE, Fq::one());
        assert_eq!(FQ_ONE, <MontBackend<FqConfig, 6>>::ONE);
    }
}

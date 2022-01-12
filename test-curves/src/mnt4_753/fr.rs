use ark_ff::{
    biginteger::BigInt,
    biginteger::BigInteger768 as BigInteger,
    fields::{Fp768, MontBackend},
};

pub type Fr = Fp768<MontBackend<FrConfig, 12>>;
pub struct FrConfig;

impl ark_ff::MontConfig<12> for FrConfig {
    /// MODULUS = 41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001
    const MODULUS: BigInteger = BigInt::<12>([
        0xd90776e240000001,
        0x4ea099170fa13a4f,
        0xd6c381bc3f005797,
        0xb9dff97634993aa4,
        0x3eebca9429212636,
        0xb26c5c28c859a99b,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]);

    const GENERATOR: Fr = ark_ff::MontFp!(Fr, "17");

    const TWO_ADIC_ROOT_OF_UNITY: Fr = ark_ff::MontFp!(Fr, "40577822398412982719876671814347622311725878559400100565221223860226396934830112376659822430317692232440883010225033880793828874730711721234325694240460855741763791540474706150170374090550695427806583236301930157866709353840964");

    const SMALL_SUBGROUP_BASE: Option<u32> = Some(5);
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(2);

    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fr> = Some(ark_ff::MontFp!(Fr, "12249458902762217747626832919710926618510011455364963726393752854649914979954138109976331601455448780251166045203053508523342111624583986869301658366625356826888785691823710598470775453742133593634524619429629803955083254436531"));
}

pub const FR_ONE: Fr = ark_ff::MontFp!(Fr, "1");

use ark_ff::{
    biginteger::BigInteger768 as BigInteger,
    fields::{FftParameters, Fp768, Fp768Parameters, FpParameters},
};

pub type FqSmall = Fp768<FqSmallParameters>;

pub struct FqSmallParameters;

impl Fp768Parameters for FqSmallParameters {}
impl FftParameters for FqSmallParameters {
    type BigInt = BigInteger;

    const TWO_ADICITY: u32 = 3;

    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        0x3c674239db68493,
        0xfef6975cbb462226,
        0xb51b3bc1d046cc3b,
        0x64bb3f640d778d9a,
        0xdccd2095fcdd5597,
        0xd4180a2274a800d5,
        0xd2bd63cea1669c48,
        0x56df5a309734fcb3,
        0x3f6bc8daac33fd24,
        0x630bf0d3db7844df,
        0xb195db53f469d63c,
        0xe31067a48c8d,
    ]);

    const SMALL_SUBGROUP_BASE: Option<u32> = Some(5);
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(2);
    /// LARGE_SUBGROUP_ROOT_OF_UNITY =
    /// 361945032479010641438674208552470823039048385584628324787231077322605681290231257959792411841605607901536185800295460409558230827322932929456332968686376141335717483896928057193278646316573411042969448937589880896861365568984
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<BigInteger> = Some(BigInteger([
        0x6695144b9a2785d8,
        0x41b6d64f332d595,
        0x9324d19ee9a2e06,
        0x3f282520ecfc9ea8,
        0xeebc1e12d6591caa,
        0xbb387b86e539d31b,
        0xaf5e30b5bdad73ba,
        0x6231336fb99772f6,
        0xb662890031bcf9a7,
        0x9785837058f42098,
        0xb7bc28a492de75ba,
        0x3e94dbde73a,
    ]));
}
impl FpParameters for FqSmallParameters {
    /// MODULUS = 41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689601
    const MODULUS: BigInteger = BigInteger([
        0x5e9063de245e8001,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]);

    const MODULUS_BITS: u32 = 753;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 15;

    const R: BigInteger = BigInteger([
        0x98a8ecabd9dc6f42,
        0x91cd31c65a034686,
        0x97c3e4a0cd14572e,
        0x79589819c788b601,
        0xed269c942108976f,
        0x1e0f4d8acf031d68,
        0x320c3bb713338559,
        0x598b4302d2f00a62,
        0x4074c9cbfd8ca621,
        0xfa47edb3865e88c,
        0x95455fb31ff9a195,
        0x7b479ec8e242,
    ]);

    const R2: BigInteger = BigInteger([
        0x84717088cfd190c8,
        0xc7d9ff8e7df03c0a,
        0xa24bea56242b3507,
        0xa896a656a0714c7d,
        0x80a46659ff6f3ddf,
        0x2f47839ef88d7ce8,
        0xa8c86d4604a3b597,
        0xe03c79cac4f7ef07,
        0x2505daf1f4a81245,
        0x8e4605754c381723,
        0xb081f15bcbfdacaf,
        0x2a33e89cb485,
    ]);

    const INV: u64 = 0xf2044cfbe45e7fff;

    const GENERATOR: BigInteger = BigInteger([
        0xa8f627f0e629635e,
        0x202afce346c36872,
        0x85e1ece733493254,
        0x6d76e610664ac389,
        0xdf542f3f04441585,
        0x3aa4885bf6d4dd80,
        0xeb8b63c1c0fffc74,
        0xd2488e985f6cfa4e,
        0xcce1c2a623f7a66a,
        0x2a060f4d5085b19a,
        0xa9111a596408842f,
        0x11ca8d50bf627,
    ]);

    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xaf4831ef122f4000,
        0x71ceaa29166e88cf,
        0x31c40838cd6212f8,
        0x342d6674bb392a52,
        0xdc0786d2e5a9bf1c,
        0xd88bf3bb790c02ce,
        0xcce8926cd0ad7bce,
        0x83fedc92f45076c6,
        0xaf5bf47cb64bec39,
        0xdbfccba82dc7d7f6,
        0x88114811777166d6,
        0xe26316c96208,
    ]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T

    /// T = (MODULUS - 1) / 2^S =
    /// 5237311370989869175293026848905079641021338739994243633972937865128169101571388346632361720473792365177258871486031723264294215816198048150198950715251640808616425543493730067875998290967932856715078506461517658162889340211200
    const T: BigInteger = BigInteger([
        0xebd20c7bc48bd000,
        0x1c73aa8a459ba233,
        0x8c71020e335884be,
        0xd0b599d2ece4a94,
        0xb701e1b4b96a6fc7,
        0xb622fceede4300b3,
        0xb33a249b342b5ef3,
        0x60ffb724bd141db1,
        0xabd6fd1f2d92fb0e,
        0xb6ff32ea0b71f5fd,
        0x220452045ddc59b5,
        0x3898c5b25882,
    ]);

    /// (T - 1) / 2 =
    /// 2618655685494934587646513424452539820510669369997121816986468932564084550785694173316180860236896182588629435743015861632147107908099024075099475357625820404308212771746865033937999145483966428357539253230758829081444670105599
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xf5e9063de245e7ff,
        0xe39d54522cdd119,
        0x4638810719ac425f,
        0x8685acce9767254a,
        0xdb80f0da5cb537e3,
        0xdb117e776f218059,
        0xd99d124d9a15af79,
        0x307fdb925e8a0ed8,
        0xd5eb7e8f96c97d87,
        0xdb7f997505b8fafe,
        0x110229022eee2cda,
        0x1c4c62d92c41,
    ]);
}

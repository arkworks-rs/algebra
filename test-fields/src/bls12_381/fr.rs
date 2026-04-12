use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[generator = "7"]
#[small_subgroup_base = "3"]
#[small_subgroup_power = "1"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;

#[test]
fn test_inv() {
    assert_eq!(FrConfig::INV, 0xffff_fffe_ffff_ffff);
}

#[test]
fn test_modulus() {
    assert_eq!(
        FrConfig::MODULUS.0,
        [
            0xffff_ffff_0000_0001,
            0x53bd_a402_fffe_5bfe,
            0x3339_d808_09a1_d805,
            0x73ed_a753_299d_7d48,
        ]
    );
}

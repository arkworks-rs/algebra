use ark_ec::{
    models::{ModelParameters, SWModelParameters},
    short_weierstrass_jacobian::*,
};
use ark_ff::field_new;

use crate::mnt4_753::{Fq, Fr, FR_ONE};

pub type G1Affine = GroupAffine<Parameters>;
pub type G1Projective = GroupProjective<Parameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Parameters;

impl ModelParameters for Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[1];

    /// COFACTOR^(-1) mod r =
    /// 1
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = FR_ONE;
}

impl SWModelParameters for Parameters {
    /// COEFF_A = 2
    #[rustfmt::skip]
    const COEFF_A: Fq = field_new!(Fq, "2");

    /// COEFF_B = 0x01373684A8C9DCAE7A016AC5D7748D3313CD8E39051C596560835DF0C9E50A5B59B882A92C78DC537E51A16703EC9855C77FC3D8BB21C8D68BB8CFB9DB4B8C8FBA773111C36C8B1B4E8F1ECE940EF9EAAD265458E06372009C9A0491678EF4
    ///         = 28798803903456388891410036793299405764940372360099938340752576406393880372126970068421383312482853541572780087363938442377933706865252053507077543420534380486492786626556269083255657125025963825610840222568694137138741554679540
    #[rustfmt::skip]
    const COEFF_B: Fq = field_new!(Fq, "28798803903456388891410036793299405764940372360099938340752576406393880372126970068421383312482853541572780087363938442377933706865252053507077543420534380486492786626556269083255657125025963825610840222568694137138741554679540");

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (G1_GENERATOR_X, G1_GENERATOR_Y);
}

// Generator of G1
// X = 7790163481385331313124631546957228376128961350185262705123068027727518350362064426002432450801002268747950550964579198552865939244360469674540925037890082678099826733417900510086646711680891516503232107232083181010099241949569,
// Y = 6913648190367314284606685101150155872986263667483624713540251048208073654617802840433842931301128643140890502238233930290161632176167186761333725658542781350626799660920481723757654531036893265359076440986158843531053720994648,
/// G1_GENERATOR_X =
#[rustfmt::skip]
pub const G1_GENERATOR_X: Fq = field_new!(Fq, "7790163481385331313124631546957228376128961350185262705123068027727518350362064426002432450801002268747950550964579198552865939244360469674540925037890082678099826733417900510086646711680891516503232107232083181010099241949569");

/// G1_GENERATOR_Y =
#[rustfmt::skip]
pub const G1_GENERATOR_Y: Fq = field_new!(Fq, "6913648190367314284606685101150155872986263667483624713540251048208073654617802840433842931301128643140890502238233930290161632176167186761333725658542781350626799660920481723757654531036893265359076440986158843531053720994648");

use ark_ec::{
    mnt4,
    mnt4::MNT4Config,
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
};
use ark_ff::{AdditiveGroup, MontFp};

use crate::{Fq, Fq2, Fr, G1_COEFF_A_NON_RESIDUE};

pub type G2Affine = mnt4::G2Affine<crate::Config>;
pub type G2Projective = mnt4::G2Projective<crate::Config>;
pub type G2Prepared = mnt4::G2Prepared<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq2;
    type ScalarField = Fr;

    /// COFACTOR =
    /// 41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888049094905534395567574915333486969589229856772141392370549616644545554517640527237829320384324374366385444967219201
    #[rustfmt::skip]
    const COFACTOR: &'static [u64] = &[
        16436257212445032449,
        8690275530472745198,
        17315389657026393162,
        1645397558963170979,
        3544984605440726586,
        12665092767997125024,
        11083680675069097885,
        575819899841080717,
        6825179918269667443,
        13256793349531086829,
        1162650133526138285,
        497830423872529,
    ];

    /// COFACTOR^(-1) mod r =
    /// 102345604409665481004734934052318066391634848395005988700111949231215905051467807945653833683883449458834877235200
    const COFACTOR_INV: Fr = MontFp!("102345604409665481004734934052318066391634848395005988700111949231215905051467807945653833683883449458834877235200");
}

/// MUL_BY_A_C0 = NONRESIDUE * COEFF_A
pub const MUL_BY_A_C0: Fq = G1_COEFF_A_NON_RESIDUE;

/// MUL_BY_A_C1 = NONRESIDUE * COEFF_A
pub const MUL_BY_A_C1: Fq = G1_COEFF_A_NON_RESIDUE;

impl SWCurveConfig for Config {
    const COEFF_A: Fq2 = crate::Config::TWIST_COEFF_A;
    // B coefficient of MNT4-753 G2 =
    // ```
    // mnt4753_twist_coeff_b = mnt4753_Fq2(mnt4753_Fq::zero(),
    //                                  mnt4753_G1::coeff_b * mnt4753_Fq2::non_residue);
    // non_residue = mnt4753_Fq2::non_residue = mnt4753_Fq("13");
    //  = (ZERO, G1_B_COEFF * NON_RESIDUE);
    //  =
    //  (0, 39196523001581428369576759982967177918859161321667605855515469914917622337081756705006832951954384669101573360625169461998308377011601613979275218690841934572954991361632773738259652003389826903175898479855893660378722437317212)
    // ```
    const COEFF_B: Fq2 = Fq2::new(
        Fq::ZERO,
        MontFp!("39196523001581428369576759982967177918859161321667605855515469914917622337081756705006832951954384669101573360625169461998308377011601613979275218690841934572954991361632773738259652003389826903175898479855893660378722437317212")
    );

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(elt: Fq2) -> Fq2 {
        Fq2::new(MUL_BY_A_C0 * &elt.c0, MUL_BY_A_C1 * &elt.c1)
    }
}

const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

// Generator of G2
// These are two Fq elements each because X and Y (and Z) are elements of Fq^2
// X = 29483965110843144675703364744708836524643960105538608078862508397502447349913068434941060515343254862580437318493682762113105361632548148204806052114008731372757389645383891982211245013965175213456066452587869519098351487925167,
// 19706011319630172391076079624799753948158506771222147486237995321925443331396169656568431378974558350664383559981183980668976846806019030432389169137953988990802000581078994008283967768348275973921598166274857631001635633631000,
// Y = 39940152670760519653940320314827327941993141403708338666925204282084477074754642625849927569427860786384998614863651207257467076192649385174108085803168743803491780568503369317093191101779534035377266300185099318717465441820654,
// 17608637424964395737041291373756657139607306440193731804102457011726690702169238966996114255971643893157857311132388792357391583164125870757541009035041469463366528798593952884745987697403056488744603829437448927398468360797245,
pub const G2_GENERATOR_X_C0: Fq = MontFp!("29483965110843144675703364744708836524643960105538608078862508397502447349913068434941060515343254862580437318493682762113105361632548148204806052114008731372757389645383891982211245013965175213456066452587869519098351487925167");

pub const G2_GENERATOR_X_C1: Fq = MontFp!("19706011319630172391076079624799753948158506771222147486237995321925443331396169656568431378974558350664383559981183980668976846806019030432389169137953988990802000581078994008283967768348275973921598166274857631001635633631000");

pub const G2_GENERATOR_Y_C0: Fq = MontFp!("39940152670760519653940320314827327941993141403708338666925204282084477074754642625849927569427860786384998614863651207257467076192649385174108085803168743803491780568503369317093191101779534035377266300185099318717465441820654");

pub const G2_GENERATOR_Y_C1: Fq = MontFp!("17608637424964395737041291373756657139607306440193731804102457011726690702169238966996114255971643893157857311132388792357391583164125870757541009035041469463366528798593952884745987697403056488744603829437448927398468360797245");

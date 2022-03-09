use crate::bls12_381::*;
use ark_ff::{fields::*, MontFp, QuadExt};

pub type Fq6 = Fp6<Fq6Config>;

#[derive(Clone, Copy)]
pub struct Fq6Config;

impl Fp6Config for Fq6Config {
    type Fp2Config = Fq2Config;

    /// NONRESIDUE = (U + 1)
    const NONRESIDUE: Fq2 = QuadExt!(MontFp!(Fq, "1"), MontFp!(Fq, "1"));

    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP6_C1: &'static [Fq2] = &[
        // Fp2::NONRESIDUE^(((q^0) - 1) / 3)
        QuadExt!(MontFp!(Fq, "1"), MontFp!(Fq, "0")),

        // Fp2::NONRESIDUE^(((q^1) - 1) / 3)
        QuadExt!(
            MontFp!(Fq, "0"),
            MontFp!(Fq, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
        ),
        // Fp2::NONRESIDUE^(((q^2) - 1) / 3)
        QuadExt!(
            MontFp!(Fq, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
            MontFp!(Fq, "0"),
        ),
        // Fp2::NONRESIDUE^(((q^3) - 1) / 3)
        QuadExt!(
            MontFp!(Fq, "0"),
            MontFp!(Fq, "1"),
        ),
        // Fp2::NONRESIDUE^(((q^4) - 1) / 3)
        QuadExt!(
            MontFp!(Fq, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
            MontFp!(Fq, "0"),
        ),
        // Fp2::NONRESIDUE^(((q^5) - 1) / 3)
        QuadExt!(
            MontFp!(Fq, "0"),
            MontFp!(Fq, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
        ),
];

    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP6_C2: &'static [Fq2] = &[
        // Fq2(u + 1)**(((2q^0) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "1"),
            MontFp!(Fq, "0"),
        ),
        // Fq2(u + 1)**(((2q^1) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437"),
            MontFp!(Fq, "0"),
        ),
        // Fq2(u + 1)**(((2q^2) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
            MontFp!(Fq, "0"),
        ),
        // Fq2(u + 1)**(((2q^3) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "-1"),
            MontFp!(Fq, "0"),
        ),
        // Fq2(u + 1)**(((2q^4) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
            MontFp!(Fq, "0"),
        ),
        // Fq2(u + 1)**(((2q^5) - 2) / 3)
        QuadExt!(
            MontFp!(Fq, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351"),
            MontFp!(Fq, "0"),
        ),
    ];

    /// Multiply this element by the quadratic nonresidue 1 + u.
    /// Make this generic.
    fn mul_fp2_by_nonresidue(fe: &Fq2) -> Fq2 {
        let mut copy = *fe;
        let t0 = copy.c0;
        copy.c0 -= &fe.c1;
        copy.c1 += &t0;
        copy
    }
}

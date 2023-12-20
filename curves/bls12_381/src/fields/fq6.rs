use ark_ff::{fields::*, MontFp};

use crate::*;

pub type Fq6 = Fp6<Fq6Config>;

#[derive(Clone, Copy)]
pub struct Fq6Config;

impl Fp6Config for Fq6Config {
    type Fp2Config = Fq2Config;

    /// NONRESIDUE = (U + 1)
    const NONRESIDUE: Fq2 = Fq2::new(Fq::ONE, Fq::ONE);

    const FROBENIUS_COEFF_FP6_C1: &'static [Fq2] = &[
        // Fp2::NONRESIDUE^(((q^0) - 1) / 3)
        Fq2::new(
            Fq::ONE,
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^1) - 1) / 3)
        Fq2::new(
            Fq::ZERO,
            MontFp!("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
        ),
        // Fp2::NONRESIDUE^(((q^2) - 1) / 3)
        Fq2::new(
            MontFp!("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^3) - 1) / 3)
        Fq2::new(
            Fq::ZERO,
            Fq::ONE,
        ),
        // Fp2::NONRESIDUE^(((q^4) - 1) / 3)
        Fq2::new(
            MontFp!("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^5) - 1) / 3)
        Fq2::new(
            Fq::ZERO,
            MontFp!("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
        ),
];

    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP6_C2: &'static [Fq2] = &[
        // Fq2(u + 1)**(((2q^0) - 2) / 3)
        Fq2::new(
            Fq::ONE,
            Fq::ZERO,
        ),
        // Fq2(u + 1)**(((2q^1) - 2) / 3)
        Fq2::new(
            MontFp!("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437"),
            Fq::ZERO,
        ),
        // Fq2(u + 1)**(((2q^2) - 2) / 3)
        Fq2::new(
            MontFp!("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436"),
            Fq::ZERO,
        ),
        // Fq2(u + 1)**(((2q^3) - 2) / 3)
        Fq2::new(
            MontFp!("-1"),
            Fq::ZERO,
        ),
        // Fq2(u + 1)**(((2q^4) - 2) / 3)
        Fq2::new(
            MontFp!("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"),
            Fq::ZERO,
        ),
        // Fq2(u + 1)**(((2q^5) - 2) / 3)
        Fq2::new(
            MontFp!("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351"),
            Fq::ZERO,
        ),
    ];

    /// Multiply this element by the quadratic nonresidue 1 + u.
    /// Make this generic.
    fn mul_fp2_by_nonresidue_in_place(fe: &mut Fq2) -> &mut Fq2 {
        let t0 = fe.c0;
        fe.c0 -= &fe.c1;
        fe.c1 += &t0;
        fe
    }
}

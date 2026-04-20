use crate::bls12_381::{Fq, FQ_ONE, FQ_ZERO};
use ark_ff::{
    fields::{AdditiveGroup, Fp2, Fp2Config},
    MontFp,
};

pub type Fq2 = Fp2<Fq2Config>;

pub struct Fq2Config;

impl Fp2Config for Fq2Config {
    type Fp = Fq;

    /// NONRESIDUE = -1
    const NONRESIDUE: Fq = MontFp!("-1");

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &[Fq] = &[
        // Fq(-1)**(((q^0) - 1) / 2)
        MontFp!("1"),
        // Fq(-1)**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];

    #[inline(always)]
    fn mul_fp_by_nonresidue_in_place(fp: &mut Self::Fp) -> &mut Self::Fp {
        fp.neg_in_place()
    }

    #[inline(always)]
    fn mul_fp_by_nonresidue_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        y.neg_in_place();
        *y += x;
    }

    #[inline(always)]
    fn mul_fp_by_nonresidue_plus_one_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        *y = *x;
    }

    #[inline(always)]
    fn sub_and_mul_fp_by_nonresidue(y: &mut Self::Fp, x: &Self::Fp) {
        *y += x;
    }
}

pub const FQ2_ZERO: Fq2 = Fq2::new(FQ_ZERO, FQ_ZERO);
pub const FQ2_ONE: Fq2 = Fq2::new(FQ_ONE, FQ_ZERO);

#[cfg(test)]
mod raw_layout {
    //! `QuadExtField` is `#[repr(C)]` and derives `zerocopy::IntoBytes`, so
    //! `Fp2` over a zerocopy-compatible base field lays out as two adjacent
    //! base-field elements with no padding.
    use super::*;
    use ark_std::vec::Vec;
    use core::mem::{align_of, size_of};
    use zerocopy::IntoBytes;

    #[test]
    fn fq2_is_two_adjacent_fqs() {
        assert_eq!(size_of::<Fq2>(), 2 * size_of::<Fq>());
        assert_eq!(align_of::<Fq2>(), align_of::<Fq>());
    }

    #[test]
    fn fq2_as_bytes_is_c0_then_c1() {
        let elems: Vec<Fq2> = (0..3u64)
            .map(|v| Fq2::new(Fq::from(v), Fq::from(v + 100)))
            .collect();
        let bytes = elems.as_bytes();
        assert_eq!(bytes.len(), elems.len() * 2 * size_of::<Fq>());

        // c0 must appear before c1 for each element.
        for (i, elem) in elems.iter().enumerate() {
            let start = i * 2 * size_of::<Fq>();
            let c0_bytes = &bytes[start..start + size_of::<Fq>()];
            let c1_bytes = &bytes[start + size_of::<Fq>()..start + 2 * size_of::<Fq>()];
            assert_eq!(c0_bytes, elem.c0.as_bytes());
            assert_eq!(c1_bytes, elem.c1.as_bytes());
        }
    }
}

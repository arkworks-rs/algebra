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
    //! `QuadExtField` is `#[repr(C)]`, so an `Fp2` of a `#[repr(transparent)]`
    //! base field lays out as `[BaseField; 2]` with no padding. The downstream
    //! `efficient-sumcheck` relies on this to reinterpret `&[Fp2]` as
    //! `&[u64]` for the Goldilocks SIMD kernels.
    use super::*;
    use ark_ff::RawU64Repr;
    use ark_std::vec::Vec;
    use core::mem::{align_of, size_of};

    #[test]
    fn fq2_is_two_adjacent_fqs() {
        assert_eq!(size_of::<Fq2>(), 2 * size_of::<Fq>());
        assert_eq!(align_of::<Fq2>(), align_of::<Fq>());
    }

    #[test]
    fn raw_u64_repr_n_u64_composes() {
        // Fq is Fp384 over BigInt<6> → 6 u64 limbs per element.
        assert_eq!(<Fq as RawU64Repr>::N_U64, 6);
        // Fq2 is a QuadExt over Fq → 2 * 6 = 12 limbs per element.
        assert_eq!(<Fq2 as RawU64Repr>::N_U64, 12);
    }

    #[test]
    fn raw_u64_repr_slice_round_trip() {
        let elems: Vec<Fq2> = (0..3u64)
            .map(|v| Fq2::new(Fq::from(v), Fq::from(v + 100)))
            .collect();
        let limbs = Fq2::as_u64_slice(&elems);
        assert_eq!(limbs.len(), elems.len() * 12);
    }
}

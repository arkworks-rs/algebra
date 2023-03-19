use core::ops::Neg;

use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::{
    fields::{
        fp3::Fp3Config,
        fp6_2over3::{Fp6, Fp6Config},
        Field, PrimeField,
    },
    BigInteger, BitIteratorBE, CyclotomicMultSubgroup,
};
use itertools::Itertools;
use num_traits::One;

use ark_std::{marker::PhantomData, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub enum TwistType {
    M,
    D,
}

pub trait BW6Config: 'static + Eq + Sized {
    const X: <Self::Fp as PrimeField>::BigInt;
    const X_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_1: &'static [u64];
    const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool;
    const ATE_LOOP_COUNT_2: &'static [i8];
    const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool;
    const H_T: i64;
    const H_Y: i64;
    const TWIST_TYPE: TwistType;
    type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp3Config: Fp3Config<Fp = Self::Fp>;
    type Fp6Config: Fp6Config<Fp3Config = Self::Fp3Config>;
    type G1Config: SWCurveConfig<BaseField = Self::Fp>;
    type G2Config: SWCurveConfig<
        BaseField = Self::Fp,
        ScalarField = <Self::G1Config as CurveConfig>::ScalarField,
    >;

    fn final_exponentiation(f: MillerLoopOutput<BW6<Self>>) -> Option<PairingOutput<BW6<Self>>> {
        let value = f.0;
        let value_inv = value.inverse().unwrap();
        let value_to_first_chunk =
            BW6::<Self>::final_exponentiation_first_chunk(&value, &value_inv);
        Some(BW6::<Self>::final_exponentiation_last_chunk(
            &value_to_first_chunk,
        ))
        .map(PairingOutput)
    }

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
        b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
    ) -> MillerLoopOutput<BW6<Self>> {
        // Alg.5 in https://eprint.iacr.org/2020/351.pdf

        let (mut pairs_1, mut pairs_2) = a
            .into_iter()
            .zip_eq(b)
            .filter_map(|(p, q)| {
                let (p, q): (G1Prepared<Self>, G2Prepared<Self>) = (p.into(), q.into());
                match !p.is_zero() && !q.is_zero() {
                    true => Some((
                        (p, q.ell_coeffs_1.into_iter()),
                        (p, q.ell_coeffs_2.into_iter()),
                    )),
                    false => None,
                }
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();

        let mut f_1 = cfg_chunks_mut!(pairs_1, 4)
            .map(|pairs| {
                let mut f = <BW6<Self> as Pairing>::TargetField::one();
                for i in BitIteratorBE::without_leading_zeros(Self::ATE_LOOP_COUNT_1).skip(1) {
                    f.square_in_place();
                    for (p, coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }
                    if i {
                        for (p, coeffs) in pairs.iter_mut() {
                            BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<BW6<Self> as Pairing>::TargetField>();

        if Self::ATE_LOOP_COUNT_1_IS_NEGATIVE {
            f_1.cyclotomic_inverse_in_place();
        }
        let mut f_2 = cfg_chunks_mut!(pairs_2, 4)
            .map(|pairs| {
                let mut f = <<BW6<Self> as Pairing>::TargetField>::one();
                for i in (1..Self::ATE_LOOP_COUNT_2.len()).rev() {
                    if i != Self::ATE_LOOP_COUNT_2.len() - 1 {
                        f.square_in_place();
                    }

                    for (p, ref mut coeffs) in pairs.iter_mut() {
                        BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                    }

                    let bit = Self::ATE_LOOP_COUNT_2[i - 1];
                    if bit == 1 || bit == -1 {
                        for &mut (p, ref mut coeffs) in pairs.iter_mut() {
                            BW6::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
                        }
                    }
                }
                f
            })
            .product::<<BW6<Self> as Pairing>::TargetField>();

        if Self::ATE_LOOP_COUNT_2_IS_NEGATIVE {
            f_2.cyclotomic_inverse_in_place();
        }

        f_2.frobenius_map_in_place(1);

        MillerLoopOutput(f_1 * &f_2)
    }
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct BW6<P: BW6Config>(PhantomData<fn() -> P>);

impl<P: BW6Config> BW6<P> {
    // Evaluate the line function at point p.
    fn ell(f: &mut Fp6<P::Fp6Config>, coeffs: &(P::Fp, P::Fp, P::Fp), p: &G1Affine<P>) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;
        let mut c2 = coeffs.2;

        match P::TWIST_TYPE {
            TwistType::M => {
                c2 *= &p.y;
                c1 *= &p.x;
                f.mul_by_014(&c0, &c1, &c2);
            },
            TwistType::D => {
                c0 *= &p.y;
                c1 *= &p.x;
                f.mul_by_034(&c0, &c1, &c2);
            },
        }
    }

    fn exp_by_x(f0: Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        let mut f = f0.cyclotomic_exp(P::X);
        if P::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        f
    }

    fn exp_by_x_minus_1(f0: Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        let mut f = f0.cyclotomic_exp(P::X);
        if P::X_IS_NEGATIVE {
            f.cyclotomic_inverse_in_place();
        }
        f * &f0.cyclotomic_inverse().unwrap()
    }

    fn final_exponentiation_first_chunk(
        elt: &Fp6<P::Fp6Config>,
        elt_inv: &Fp6<P::Fp6Config>,
    ) -> Fp6<P::Fp6Config> {
        // (q^3-1)*(q+1)

        // elt_q3 = elt^(q^3)
        let mut elt_q3 = *elt;
        elt_q3.cyclotomic_inverse_in_place();
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let mut alpha = elt_q3_over_elt;
        alpha.frobenius_map_in_place(1);
        // beta = elt^((q^3-1)*(q+1)
        alpha * &elt_q3_over_elt
    }

    #[allow(clippy::let_and_return)]
    fn final_exponentiation_last_chunk(m: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
        // generic method for the BW6 family, parametrized by `h_t` and `h_y`
        // hard_part
        // From [HG21](https://eprint.iacr.org/2021/1359.pdf), Eq. 22
        // Currently only implemented for trace = 0 mod 6
        // TODO: Implement for trace = 3 mod 6

        #[rustfmt::skip]
        // The task is to exponentiate `f` (output of the easy part) by `(u+1)*Phi_k(p(u))/r(u)`
        // To make an explicit link with [HHT](https://eprint.iacr.org/2020/875), Theorem 4, we have:
        // Phi_k(p)/r = h_1 * (T + p - 1) + h_2
        // where T = t - 1 = t_bw + h_t * r - 1
        // h_1 = c (cofactor) = (h_t^2 + 3*h_y^2) / 4r + (h_t - h_y)/2t_bw + ((t_bw^2)/3 - t_bw + 1)/r - h_t

        let x = <P::Fp as PrimeField>::from_bigint(P::X).unwrap();
        let x_minus_1 = x - <P::Fp>::one();
        // compute a = f^(q - 1 - (X-1)^2)
        let mut a = m.cyclotomic_exp(P::X) * m.cyclotomic_inverse().unwrap();
        // let mut a = Self::exp_by_x_minus_1(*m);
        {
            let tv = m.cyclotomic_exp(x_minus_1.into_bigint());
            assert_eq!(a, tv, "failed at a")
        }
        a = Self::exp_by_x_minus_1(a);
        a = m * a;
        a.conjugate_in_place();
        let f_frob = m.frobenius_map(1);
        a *= f_frob;

        // compute b = f^(-(X^3-X^2+1) + (X+1)*q)
        let b = Self::exp_by_x(a) * a * m;
        {
            let left = x*x*x - x*x + <P::Fp>::one();
            let right = x + <P::Fp>::one();
            let tv = m.cyclotomic_exp(left.into_bigint()).cyclotomic_inverse().unwrap();
            let mut tv2 = m.cyclotomic_exp(right.into_bigint());
            tv2.frobenius_map_in_place(1);
            assert_eq!(b, tv * tv2, "failed at b")
        }

        // now h = b^(c + h_t)

        // checking composition of `c`, we need to get the exponent t_bw/3
        // t_bw/3 = (-X^5 + 3X^4 - 3X^3 + X)/3 (per Table 3 in [HG21])
        // c = b^((X-1)/3)
        let c = if P::X_IS_NEGATIVE {
            let x = <P::Fp as PrimeField>::from_bigint(P::X).unwrap();
            let tv2 = (x + <P::Fp>::one()) / <P::Fp>::from(3u64);
            let mut tv = b.cyclotomic_exp(tv2.into_bigint());
            tv.cyclotomic_inverse_in_place();
            tv
        } else {
            let x = <P::Fp as PrimeField>::from_bigint(P::X).unwrap();
            let tv2 = (x - <P::Fp>::one()) / <P::Fp>::from(3u64);
            b.cyclotomic_exp(tv2.into_bigint())
        };

        {
            let tv2 = x_minus_1 / <P::Fp>::from(3u64);
            let tv = b.cyclotomic_exp(tv2.into_bigint());
            assert_eq!(c, tv, "failed at c")
        }

        let d = Self::exp_by_x_minus_1(c);
        {
            let tv2 = (x_minus_1 * x_minus_1) / <P::Fp>::from(3u64);
            let tv = b.cyclotomic_exp(tv2.into_bigint());
            assert_eq!(d, tv, "failed at d")
        }

        let mut e = Self::exp_by_x_minus_1(d);
        e = Self::exp_by_x_minus_1(e);
        e *= &d;

        let cc_0_min_1 =
            ((x_minus_1 * x_minus_1 * x_minus_1 * x_minus_1) + (x_minus_1 * x_minus_1));
        {
            let pow = cc_0_min_1 / <P::Fp>::from(3u64);
            let tv = b.cyclotomic_exp(pow.into_bigint());
            assert_eq!(e, tv, "failed at e")
        }

        let mut f = Self::exp_by_x(e) * &e * &c;

        f.cyclotomic_inverse_in_place();
        f *= &d;

        // tr0 = -u^5 + 3*u^4 - 3*u^3 + u
        let neg_tr_0 = (x * x * x * x * x) - (x * x * x * x * <P::Fp>::from(3u64))
            + (x * x * x * <P::Fp>::from(3u64))
            - x;

        {
            // let x_plus_1 = x + <P::Fp>::one();
            let tv2 = neg_tr_0 / <P::Fp>::from(3u64);

            let mut tv = b.cyclotomic_exp(tv2.into_bigint());
            tv.cyclotomic_inverse_in_place();
            // tv *= &d;
            assert_eq!(f, tv, "failed at f")
        }

        let d1 = (P::H_T - P::H_Y) / 2;
        let d2 = ((P::H_T ^ 2 + 3 * (P::H_Y ^ 2)) / 4) as u64;

        let mut g = f * &d;
        g = Self::exp_by_x(g) * g;
        g.cyclotomic_inverse_in_place();
        g *= &c * &b;
        g.cyclotomic_exp_in_place(&[d2]);
        let r = <Self as Pairing>::ScalarField::MODULUS;
        let pow = <P::Fp as PrimeField>::from_be_bytes_mod_order(&r.to_bytes_be());

        let d2_bigint = <P::Fp as PrimeField>::BigInt::from(d2 as u64);
        let d_2 = <P::Fp as PrimeField>::from_bigint(d2_bigint).unwrap();
        let r_d2 = d_2 * pow;
        {
            let tv = b.cyclotomic_exp(r_d2.into_bigint());
            assert_eq!(g, tv, "failed at g")
        }

        let mut h = f.cyclotomic_exp(&[d1 as u64]);

        if d1 < 0 {
            h.cyclotomic_inverse_in_place();
        }
        h *= &e;
        h = &h.square() * &h * &b * &g;

        {
            let pow = r_d2 - P::Fp::from(d1 as u64) * neg_tr_0 + cc_0_min_1 + <P::Fp>::one();
            let mut tv2 = b.cyclotomic_exp(&pow.into_bigint());
            assert_eq!(h, tv2, "failed at h");
        }

        // compute a = f^3(q - 1 - (u-1)^2)
        a = a.square() * &a;
        a.cyclotomic_inverse_in_place();
        {
            let tv2 = (P::Fp::from(3u64) * (x_minus_1 * x_minus_1) + P::Fp::from(3u64));
            let mut tv = f_frob * f_frob * f_frob;
            tv.cyclotomic_inverse_in_place();
            let tv3 = m.cyclotomic_exp(tv2.into_bigint());
            let tv4 = tv * &tv3;
            assert_eq!(a, tv4, "failed at a^3")
        }

        // now the rest
        let out = h * &a;
        // {
        //     let x = <P::Fp as PrimeField>::from_bigint(P::X).unwrap();
        //     let x_minus_1 = x - <P::Fp>::one();
        //     let tv2 = (P::Fp::from(3u64) * (x_minus_1 * x_minus_1) + P::Fp::from(3u64));
        //     // + P::Fp::from_bigint(P::Fp::MODULUS).unwrap())
        //     // * <P::Fp>::from(3u64);
        //     let mut tv = f_frob * f_frob * f_frob;
        //     tv.cyclotomic_inverse_in_place();
        //     let tv3 = m.cyclotomic_exp(tv2.into_bigint());
        //     assert_eq!(out, tv4, "failed at a^3")
        // }
        out
    }
}

impl<P: BW6Config> Pairing for BW6<P> {
    type BaseField = <P::G1Config as CurveConfig>::BaseField;
    type ScalarField = <P::G1Config as CurveConfig>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp6<P::Fp6Config>;

    fn final_exponentiation(f: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        P::final_exponentiation(f)
    }

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        P::multi_miller_loop(a, b)
    }
}

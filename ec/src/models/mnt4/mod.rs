use crate::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    pairing::Pairing,
    pairing::{MillerLoopOutput, PairingOutput},
};
use ark_ff::{
    fp2::{Fp2, Fp2Config},
    fp4::{Fp4, Fp4Config},
    BitIteratorBE, CyclotomicMultSubgroup, Field, PrimeField,
};
use itertools::Itertools;
use num_traits::{One, Zero};

use ark_std::{marker::PhantomData, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub mod g1;
pub mod g2;

use self::g2::{AteAdditionCoefficients, AteDoubleCoefficients, G2ProjectiveExtended};
pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};

pub type GT<P> = Fp4<P>;

pub trait MNT4Parameters: 'static {
    const TWIST: Fp2<Self::Fp2Config>;
    const TWIST_COEFF_A: Fp2<Self::Fp2Config>;
    const ATE_LOOP_COUNT: &'static [u64];
    const ATE_IS_LOOP_COUNT_NEG: bool;
    const FINAL_EXPONENT_LAST_CHUNK_1: <Self::Fp as PrimeField>::BigInt;
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool;
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: <Self::Fp as PrimeField>::BigInt;
    type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fr: PrimeField + Into<<Self::Fr as PrimeField>::BigInt>;
    type Fp2Config: Fp2Config<Fp = Self::Fp>;
    type Fp4Config: Fp4Config<Fp2Config = Self::Fp2Config>;
    type G1Parameters: SWCurveConfig<BaseField = Self::Fp, ScalarField = Self::Fr>;
    type G2Parameters: SWCurveConfig<
        BaseField = Fp2<Self::Fp2Config>,
        ScalarField = <Self::G1Parameters as CurveConfig>::ScalarField,
    >;
}

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct MNT4<P: MNT4Parameters>(PhantomData<fn() -> P>);

impl<P: MNT4Parameters> MNT4<P> {
    fn doubling_step_for_flipped_miller_loop(
        r: &G2ProjectiveExtended<P>,
    ) -> (G2ProjectiveExtended<P>, AteDoubleCoefficients<P>) {
        let a = r.t.square();
        let b = r.x.square();
        let c = r.y.square();
        let d = c.square();
        let e = (r.x + &c).square() - &b - &d;
        let f = (b + &b + &b) + &(P::TWIST_COEFF_A * &a);
        let g = f.square();

        let d_eight = d.double().double().double();

        let x = -(e + &e + &e + &e) + &g;
        let y = -d_eight + &(f * &(e + &e - &x));
        let z = (r.y + &r.z).square() - &c - &r.z.square();
        let t = z.square();

        let r2 = G2ProjectiveExtended { x, y, z, t };
        let coeff = AteDoubleCoefficients {
            c_h: (r2.z + &r.t).square() - &r2.t - &a,
            c_4c: c + &c + &c + &c,
            c_j: (f + &r.t).square() - &g - &a,
            c_l: (f + &r.x).square() - &g - &b,
        };

        (r2, coeff)
    }

    fn mixed_addition_step_for_flipped_miller_loop(
        x: &Fp2<P::Fp2Config>,
        y: &Fp2<P::Fp2Config>,
        r: &G2ProjectiveExtended<P>,
    ) -> (G2ProjectiveExtended<P>, AteAdditionCoefficients<P>) {
        let a = y.square();
        let b = r.t * x;
        let d = ((r.z + y).square() - &a - &r.t) * &r.t;
        let h = b - &r.x;
        let i = h.square();
        let e = i + &i + &i + &i;
        let j = h * &e;
        let v = r.x * &e;
        let l1 = d - &(r.y + &r.y);

        let x = l1.square() - &j - &(v + &v);
        let y = l1 * &(v - &x) - &(j * &(r.y + &r.y));
        let z = (r.z + &h).square() - &r.t - &i;
        let t = z.square();

        let r2 = G2ProjectiveExtended { x, y, z, t };
        let coeff = AteAdditionCoefficients { c_l1: l1, c_rz: z };

        (r2, coeff)
    }

    pub fn ate_miller_loop(p: &G1Prepared<P>, q: &G2Prepared<P>) -> Fp4<P::Fp4Config> {
        let l1_coeff = Fp2::new(p.x, P::Fp::zero()) - &q.x_over_twist;

        let mut f = <Fp4<P::Fp4Config>>::one();

        let mut add_idx: usize = 0;

        // code below gets executed for all bits (EXCEPT the MSB itself) of
        // mnt6_param_p (skipping leading zeros) in MSB to LSB order

        for (bit, dc) in BitIteratorBE::without_leading_zeros(P::ATE_LOOP_COUNT)
            .skip(1)
            .zip(&q.double_coefficients)
        {
            let g_rr_at_p = Fp4::new(
                -dc.c_4c - &(dc.c_j * &p.x_twist) + &dc.c_l,
                dc.c_h * &p.y_twist,
            );

            f = f.square() * &g_rr_at_p;

            if bit {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;

                let g_rq_at_p = Fp4::new(
                    ac.c_rz * &p.y_twist,
                    -(q.y_over_twist * &ac.c_rz + &(l1_coeff * &ac.c_l1)),
                );
                f *= &g_rq_at_p;
            }
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            let ac = &q.addition_coefficients[add_idx];

            let g_rnegr_at_p = Fp4::new(
                ac.c_rz * &p.y_twist,
                -(q.y_over_twist * &ac.c_rz + &(l1_coeff * &ac.c_l1)),
            );
            f = (f * &g_rnegr_at_p).inverse().unwrap();
        }

        f
    }

    fn final_exponentiation_first_chunk(
        elt: &Fp4<P::Fp4Config>,
        elt_inv: &Fp4<P::Fp4Config>,
    ) -> Fp4<P::Fp4Config> {
        // (q^2-1)

        // elt_q2 = elt^(q^2)
        let mut elt_q2 = *elt;
        elt_q2.cyclotomic_inverse_in_place();
        // elt_q2_over_elt = elt^(q^2-1)
        elt_q2 * elt_inv
    }

    fn final_exponentiation_last_chunk(
        elt: &Fp4<P::Fp4Config>,
        elt_inv: &Fp4<P::Fp4Config>,
    ) -> Fp4<P::Fp4Config> {
        let elt_clone = *elt;
        let elt_inv_clone = *elt_inv;

        let mut elt_q = *elt;
        elt_q.frobenius_map(1);

        let w1_part = elt_q.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_1);
        let w0_part = if P::FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG {
            elt_inv_clone.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        } else {
            elt_clone.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        };

        w1_part * &w0_part
    }
}

impl<P: MNT4Parameters> Pairing for MNT4<P> {
    type ScalarField = <P::G1Parameters as CurveConfig>::ScalarField;
    type G1 = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G1Prepared = G1Prepared<P>;
    type G2 = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type G2Prepared = G2Prepared<P>;
    type TargetField = Fp4<P::Fp4Config>;

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        let pairs = a
            .into_iter()
            .zip_eq(b)
            .map(|(a, b)| (a.into(), b.into()))
            .collect::<Vec<_>>();
        let result = cfg_into_iter!(pairs)
            .map(|(a, b)| Self::ate_miller_loop(&a, &b))
            .product();
        MillerLoopOutput(result)
    }

    fn final_exponentiation(f: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        let value = f.0;
        let value_inv = value.inverse().unwrap();
        let value_to_first_chunk = Self::final_exponentiation_first_chunk(&value, &value_inv);
        let value_inv_to_first_chunk = Self::final_exponentiation_first_chunk(&value_inv, &value);
        let result =
            Self::final_exponentiation_last_chunk(&value_to_first_chunk, &value_inv_to_first_chunk);
        Some(PairingOutput(result))
    }
}

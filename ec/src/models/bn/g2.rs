use ark_ff::{
    fields::{Field, Fp2},
    AdditiveGroup,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::*;
use educe::Educe;
use num_traits::One;

use crate::{
    bn::{BnConfig, TwistType},
    models::short_weierstrass::SWCurveConfig,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};

pub type G2Affine<P> = Affine<<P as BnConfig>::G2Config>;
pub type G2Projective<P> = Projective<<P as BnConfig>::G2Config>;

#[derive(Educe, CanonicalSerialize, CanonicalDeserialize)]
#[educe(Clone, Debug, PartialEq, Eq)]
pub struct G2Prepared<P: BnConfig> {
    /// Stores the coefficients of the line evaluations as calculated in
    /// <https://eprint.iacr.org/2013/722.pdf>
    pub ell_coeffs: Vec<EllCoeff<P>>,
    pub infinity: bool,
}

pub type EllCoeff<P> = (
    Fp2<<P as BnConfig>::Fp2Config>,
    Fp2<<P as BnConfig>::Fp2Config>,
    Fp2<<P as BnConfig>::Fp2Config>,
);

#[derive(Educe)]
#[educe(Clone, Copy, Debug)]
pub struct G2HomProjective<P: BnConfig> {
    x: Fp2<P::Fp2Config>,
    y: Fp2<P::Fp2Config>,
    z: Fp2<P::Fp2Config>,
}

impl<P: BnConfig> G2HomProjective<P> {
    pub fn double_in_place(&mut self, two_inv: &P::Fp) -> EllCoeff<P> {
        // Formula for line function when working with
        // homogeneous projective coordinates.

        let mut a = self.x * &self.y;
        a.mul_assign_by_fp(two_inv);
        let b = self.y.square();
        let c = self.z.square();
        let e = P::G2Config::COEFF_B * &(c.double() + &c);
        let f = e.double() + &e;
        let mut g = b + &f;
        g.mul_assign_by_fp(two_inv);
        let h = (self.y + &self.z).square() - &(b + &c);
        let i = e - &b;
        let j = self.x.square();
        let e_square = e.square();

        self.x = a * &(b - &f);
        self.y = g.square() - &(e_square.double() + &e_square);
        self.z = b * &h;
        match P::TWIST_TYPE {
            TwistType::M => (i, j.double() + &j, -h),
            TwistType::D => (-h, j.double() + &j, i),
        }
    }

    pub fn add_in_place(&mut self, q: &G2Affine<P>) -> EllCoeff<P> {
        // Formula for line function when working with
        // homogeneous projective coordinates.
        let theta = self.y - &(q.y * &self.z);
        let lambda = self.x - &(q.x * &self.z);
        let c = theta.square();
        let d = lambda.square();
        let e = lambda * &d;
        let f = self.z * &c;
        let g = self.x * &d;
        let h = e + &f - &g.double();
        self.x = lambda * &h;
        self.y = theta * &(g - &h) - &(e * &self.y);
        self.z *= &e;
        let j = theta * &q.x - &(lambda * &q.y);

        match P::TWIST_TYPE {
            TwistType::M => (j, -theta, lambda),
            TwistType::D => (lambda, -theta, j),
        }
    }
}

impl<P: BnConfig> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::generator())
    }
}

impl<P: BnConfig> From<G2Affine<P>> for G2Prepared<P> {
    fn from(q: G2Affine<P>) -> Self {
        if q.infinity {
            G2Prepared {
                ell_coeffs: vec![],
                infinity: true,
            }
        } else {
            let two_inv = P::Fp::one().double().inverse().unwrap();
            let mut ell_coeffs = vec![];
            let mut r = G2HomProjective::<P> {
                x: q.x,
                y: q.y,
                z: Fp2::one(),
            };

            let neg_q = -q;

            for bit in P::ATE_LOOP_COUNT.iter().rev().skip(1) {
                ell_coeffs.push(r.double_in_place(&two_inv));

                match bit {
                    1 => ell_coeffs.push(r.add_in_place(&q)),
                    -1 => ell_coeffs.push(r.add_in_place(&neg_q)),
                    _ => continue,
                }
            }

            let q1 = mul_by_char::<P>(q);
            let mut q2 = mul_by_char::<P>(q1);

            if P::X_IS_NEGATIVE {
                r.y = -r.y;
            }

            q2.y = -q2.y;

            ell_coeffs.push(r.add_in_place(&q1));
            ell_coeffs.push(r.add_in_place(&q2));

            Self {
                ell_coeffs,
                infinity: false,
            }
        }
    }
}

impl<P: BnConfig> From<G2Projective<P>> for G2Prepared<P> {
    fn from(q: G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: BnConfig> From<&'a G2Affine<P>> for G2Prepared<P> {
    fn from(other: &'a G2Affine<P>) -> Self {
        (*other).into()
    }
}

impl<'a, P: BnConfig> From<&'a G2Projective<P>> for G2Prepared<P> {
    fn from(q: &'a G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BnConfig> G2Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

fn mul_by_char<P: BnConfig>(r: G2Affine<P>) -> G2Affine<P> {
    // multiply by field characteristic

    let mut s = r;
    s.x.frobenius_map_in_place(1);
    s.x *= &P::TWIST_MUL_BY_Q_X;
    s.y.frobenius_map_in_place(1);
    s.y *= &P::TWIST_MUL_BY_Q_Y;

    s
}

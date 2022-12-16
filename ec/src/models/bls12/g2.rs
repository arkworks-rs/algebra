use ark_ff::{BitIteratorBE, Field, Fp2};
use ark_serialize::*;
use ark_std::{vec::Vec, One};

use crate::{
    bls12::{Bls12Config, TwistType},
    models::short_weierstrass::SWCurveConfig,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};

pub type G2Affine<P> = Affine<<P as Bls12Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as Bls12Config>::G2Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: Bls12Config"),
    Debug(bound = "P: Bls12Config"),
    PartialEq(bound = "P: Bls12Config"),
    Eq(bound = "P: Bls12Config")
)]
pub struct G2Prepared<P: Bls12Config> {
    // Stores the coefficients of the line evaluations as calculated in
    // https://eprint.iacr.org/2013/722.pdf
    pub ell_coeffs: Vec<EllCoeff<P>>,
    pub infinity: bool,
}

pub(crate) type EllCoeff<P> = (
    Fp2<<P as Bls12Config>::Fp2Config>,
    Fp2<<P as Bls12Config>::Fp2Config>,
    Fp2<<P as Bls12Config>::Fp2Config>,
);

#[derive(Derivative)]
#[derivative(
    Clone(bound = "P: Bls12Config"),
    Copy(bound = "P: Bls12Config"),
    Debug(bound = "P: Bls12Config")
)]
struct G2HomProjective<P: Bls12Config> {
    x: Fp2<P::Fp2Config>,
    y: Fp2<P::Fp2Config>,
    z: Fp2<P::Fp2Config>,
}

impl<P: Bls12Config> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::generator())
    }
}

impl<P: Bls12Config> From<G2Affine<P>> for G2Prepared<P> {
    fn from(q: G2Affine<P>) -> Self {
        let two_inv = P::Fp::one().double().inverse().unwrap();
        let zero = G2Prepared {
            ell_coeffs: vec![],
            infinity: true,
        };
        q.xy().map_or(zero, |(&q_x, &q_y)| {
            let mut ell_coeffs = vec![];
            let mut r = G2HomProjective::<P> {
                x: q_x,
                y: q_y,
                z: Fp2::one(),
            };

            for i in BitIteratorBE::new(P::X).skip(1) {
                ell_coeffs.push(r.double_in_place(&two_inv));

                if i {
                    ell_coeffs.push(r.add_in_place(&q));
                }
            }

            Self {
                ell_coeffs,
                infinity: false,
            }
        })
    }
}

impl<P: Bls12Config> From<G2Projective<P>> for G2Prepared<P> {
    fn from(q: G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: Bls12Config> From<&'a G2Affine<P>> for G2Prepared<P> {
    fn from(other: &'a G2Affine<P>) -> Self {
        (*other).into()
    }
}

impl<'a, P: Bls12Config> From<&'a G2Projective<P>> for G2Prepared<P> {
    fn from(q: &'a G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: Bls12Config> G2Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl<P: Bls12Config> G2HomProjective<P> {
    fn double_in_place(&mut self, two_inv: &P::Fp) -> EllCoeff<P> {
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

    fn add_in_place(&mut self, q: &G2Affine<P>) -> EllCoeff<P> {
        let (&qx, &qy) = q.xy().unwrap();
        // Formula for line function when working with
        // homogeneous projective coordinates.
        let theta = self.y - &(qy * &self.z);
        let lambda = self.x - &(qx * &self.z);
        let c = theta.square();
        let d = lambda.square();
        let e = lambda * &d;
        let f = self.z * &c;
        let g = self.x * &d;
        let h = e + &f - &g.double();
        self.x = lambda * &h;
        self.y = theta * &(g - &h) - &(e * &self.y);
        self.z *= &e;
        let j = theta * &qx - &(lambda * &qy);

        match P::TWIST_TYPE {
            TwistType::M => (j, -theta, lambda),
            TwistType::D => (lambda, -theta, j),
        }
    }
}

//! Work with sparse and dense polynomials.

use core::cmp::min;

use crate::{DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial};
use ark_ff::{FftField, Field, Zero};
use ark_std::{borrow::Cow, cfg_iter_mut, vec, vec::*};
use DenseOrSparsePolynomial::{DPolynomial, SPolynomial};

mod dense;
mod sparse;

pub use dense::DensePolynomial;
pub use sparse::SparsePolynomial;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Represents either a sparse polynomial or a dense one.
#[derive(Clone)]
pub enum DenseOrSparsePolynomial<'a, F: Field> {
    /// Represents the case where `self` is a sparse polynomial
    SPolynomial(Cow<'a, SparsePolynomial<F>>),
    /// Represents the case where `self` is a dense polynomial
    DPolynomial(Cow<'a, DensePolynomial<F>>),
}

impl<'a, F: 'a + Field> From<DensePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: DensePolynomial<F>) -> Self {
        DPolynomial(Cow::Owned(other))
    }
}

impl<'a, F: 'a + Field> From<&'a DensePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: &'a DensePolynomial<F>) -> Self {
        DPolynomial(Cow::Borrowed(other))
    }
}

impl<'a, F: 'a + Field> From<SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: SparsePolynomial<F>) -> Self {
        SPolynomial(Cow::Owned(other))
    }
}

impl<'a, F: Field> From<&'a SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    fn from(other: &'a SparsePolynomial<F>) -> Self {
        SPolynomial(Cow::Borrowed(other))
    }
}

impl<'a, F: Field> From<DenseOrSparsePolynomial<'a, F>> for DensePolynomial<F> {
    fn from(other: DenseOrSparsePolynomial<'a, F>) -> Self {
        match other {
            DPolynomial(p) => p.into_owned(),
            SPolynomial(p) => p.into_owned().into(),
        }
    }
}

impl<'a, F: 'a + Field> TryInto<SparsePolynomial<F>> for DenseOrSparsePolynomial<'a, F> {
    type Error = ();

    fn try_into(self) -> Result<SparsePolynomial<F>, ()> {
        match self {
            SPolynomial(p) => Ok(p.into_owned()),
            _ => Err(()),
        }
    }
}

impl<F: Field> DenseOrSparsePolynomial<'_, F> {
    /// Checks if the given polynomial is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            SPolynomial(s) => s.is_zero(),
            DPolynomial(d) => d.is_zero(),
        }
    }

    /// Return the degree of `self`.
    pub fn degree(&self) -> usize {
        match self {
            SPolynomial(s) => s.degree(),
            DPolynomial(d) => d.degree(),
        }
    }

    #[inline]
    fn leading_coefficient(&self) -> Option<&F> {
        match self {
            SPolynomial(p) => p.last().map(|(_, c)| c),
            DPolynomial(p) => p.last(),
        }
    }

    #[inline]
    fn iter_with_index(&self) -> Vec<(usize, F)> {
        match self {
            SPolynomial(p) => p.to_vec(),
            DPolynomial(p) => p.iter().copied().enumerate().collect(),
        }
    }

    /// Naive division. Division by a SparsePoly (of k elements) takes O(kn) in
    /// the worst case, division by a DensePoly takes O(n^2) in the worst case.
    fn naive_div(&self, divisor: &Self) -> Option<(DensePolynomial<F>, DensePolynomial<F>)> {
        if self.is_zero() {
            Some((DensePolynomial::zero(), DensePolynomial::zero()))
        } else if divisor.is_zero() {
            panic!("Dividing by zero polynomial")
        } else if self.degree() < divisor.degree() {
            Some((DensePolynomial::zero(), self.clone().into()))
        } else {
            // Now we know that self.degree() >= divisor.degree();
            let mut quotient = vec![F::zero(); self.degree() - divisor.degree() + 1];
            let mut remainder: DensePolynomial<F> = self.clone().into();
            // Can unwrap here because we know self is not zero.
            let divisor_leading_inv = divisor.leading_coefficient().unwrap().inverse().unwrap();
            while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
                let cur_q_coeff = *remainder.coeffs.last().unwrap() * divisor_leading_inv;
                let cur_q_degree = remainder.degree() - divisor.degree();
                quotient[cur_q_degree] = cur_q_coeff;

                for (i, div_coeff) in divisor.iter_with_index() {
                    remainder[cur_q_degree + i] -= &(cur_q_coeff * div_coeff);
                }
                while remainder.coeffs.last().map(|c| c.is_zero()) == Some(true) {
                    remainder.coeffs.pop();
                }
            }
            Some((DensePolynomial::from_coefficients_vec(quotient), remainder))
        }
    }
}

impl<'a, F: FftField> DenseOrSparsePolynomial<'a, F> {
    const SWITCH_TO_HENSEL_DIV: usize = 1 << 8;
    /// Divide self by another (sparse or dense) polynomial, and returns the
    /// quotient and remainder.
    /// If the divisor is a SparsePolynomial, a naive division algorithm is used.
    /// If the divisor is a DensePolynomial of degree >= 2^8, a O(M(n)) algorithm
    /// is used, with M(n) the multiplication complexity.
    /// Since the field is FFT friendly, then M(n) = O(n log n).
    pub fn divide_with_q_and_r(
        &self,
        divisor: &Self,
    ) -> Option<(DensePolynomial<F>, DensePolynomial<F>)> {
        match divisor {
            // Hensel div is faster than naive for big divisors (degree of around 200)
            DPolynomial(p) if p.degree() >= Self::SWITCH_TO_HENSEL_DIV => {
                let q = self.hensel_div(divisor)?;
                let r = &self.clone().into() - &(&q * &divisor.clone().into());

                Some((q, r))
            },
            _ => self.naive_div(divisor),
        }
    }

    pub fn divide(&self, divisor: &Self) -> Option<DensePolynomial<F>> {
        match divisor {
            // Hensel div is faster than naive for big divisors (degree of around 200)
            DPolynomial(p) if p.degree() >= Self::SWITCH_TO_HENSEL_DIV => self.hensel_div(divisor),
            _ => self.naive_div(divisor).map(|(q, _)| q),
        }
    }

    // Fast poly division, following "Modern Computer Algebra", 3rd edition, section 9.1, algorithm 9.5
    fn hensel_div(&self, divisor: &Self) -> Option<DensePolynomial<F>> {
        if self.is_zero() {
            Some(DensePolynomial::zero())
        } else if divisor.is_zero() {
            panic!("Dividing by zero polynomial")
        } else if self.degree() < divisor.degree() {
            Some(DensePolynomial::zero())
        } else {
            // Convert to DensePoly to get FFT multiplication
            let dividend_poly: DensePolynomial<F> = self.clone().into();
            let divisor_poly: DensePolynomial<F> = divisor.clone().into();

            let reverted_dividend = Self::reverse_coeffs(&dividend_poly, self.degree() + 1);
            let reverted_divisor = Self::reverse_coeffs(&divisor_poly, divisor.degree() + 1);

            // compute rev(divisor)^-1 mod X^(deg q + 1), with deg q = deg dividend - deg divisor
            let inversion_degree = self.degree() - divisor.degree() + 1;
            let reverted_divisor_inverse = Self::inverse_mod(&reverted_divisor, inversion_degree);

            // rev(q) = rev(divisor)^-1 * rev(dividend) mod X^(deg q + 1)
            let reverted_q = DensePolynomial::from_coefficients_slice(
                &(&reverted_divisor_inverse * &reverted_dividend).coeffs[..inversion_degree],
            );
            let q = DensePolynomial::from_coefficients_slice(
                &Self::reverse_coeffs(&reverted_q, inversion_degree)
                    .coeffs
                    .as_slice(),
            );

            Some(q)
        }
    }

    fn inverse_mod(poly: &DensePolynomial<F>, degree: usize) -> DensePolynomial<F> {
        if poly.coeffs[0].is_zero() {
            panic!("Cannot compute inverse of 0");
        }

        // Inverse mod X
        let mut l = 1;
        let mut current_inverse =
            DensePolynomial::from_coefficients_slice(&[F::one() / poly.coeffs[0]]);

        while l < degree {
            // Lift inverse of poly mod X^l to inverse of poly mod X^2l
            // (Also called Newton iteration in the reference book)
            current_inverse = Self::hensel_lift(poly, &current_inverse, l);
            l *= 2;
        }
        let max_coeff = min(current_inverse.coeffs.len(), degree + 1);

        DensePolynomial::from_coefficients_slice(&current_inverse.coeffs[..max_coeff])
    }

    // Given inverse such that inverse * poly = 1 mod X^base_degree, return
    // new_inverse such that new_inverse * poly = 1 mod X^(2*base_degree)
    // More precisely, decomposing inverse * poly as 1 + c * X^base_degree (c is
    // easily extracted from the coefficient list), then
    // new_inverse = inverse - X^base_degree (c * inverse mod X^base_degree)
    // For performance, poly is reduced mod X^2base_degree, and c mod X^base_degree
    #[inline]
    fn hensel_lift(
        poly: &DensePolynomial<F>,
        inverse: &DensePolynomial<F>,
        base_degree: usize,
    ) -> DensePolynomial<F> {
        let poly_mod_x2deg = DensePolynomial::from_coefficients_slice(
            &poly.coeffs[..min(2 * base_degree, poly.coeffs.len())],
        ); // lowest degree guaranteeing >= base_degree coefficients of c
        let one_plus_cxdeg = &poly_mod_x2deg * inverse;

        if one_plus_cxdeg.degree() < base_degree {
            // c = 0 thus we can simply return the inverse immediately
            return inverse.clone();
        }
        let c = DensePolynomial::from_coefficients_slice(
            &one_plus_cxdeg.coeffs[base_degree..min(2 * base_degree, one_plus_cxdeg.coeffs.len())],
        ); // we keep c of degree <= deg

        let mut new_inverse_coeffs = vec![F::zero(); 2 * base_degree];

        // First fill the lower half
        new_inverse_coeffs[..min(base_degree, inverse.coeffs.len())]
            .clone_from_slice(&inverse.coeffs);

        // Compute -inverse * c mod X^base_degree
        let above_deg_coeffs: Vec<F> = (inverse * &c)
            .coeffs
            .iter()
            .take(min(base_degree, inverse.degree() + &c.degree() + 1))
            .map(|&x| -x)
            .collect();

        // Then fill the upper half
        new_inverse_coeffs[base_degree..min(2 * base_degree, base_degree + above_deg_coeffs.len())]
            .clone_from_slice(above_deg_coeffs.as_slice());

        DensePolynomial::from_coefficients_vec(new_inverse_coeffs)
    }

    fn reverse_coeffs(poly: &DensePolynomial<F>, max_degree: usize) -> DensePolynomial<F> {
        if poly.coeffs.len() > max_degree {
            panic!(
                "Polynomial too big (size {}) to be reverted in size {}",
                poly.coeffs.len(),
                max_degree
            );
        }

        let mut rev_coeffs = vec![F::zero(); max_degree];
        rev_coeffs[..poly.coeffs.len()].clone_from_slice(
            &poly
                .coeffs
                .clone()
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .as_slice(),
        );

        DensePolynomial::from_coefficients_vec(rev_coeffs)
    }
}

impl<'a, F: 'a + FftField> DenseOrSparsePolynomial<'a, F> {
    /// Construct `Evaluations` by evaluating a polynomial over the domain
    /// `domain`.
    pub fn evaluate_over_domain<D: EvaluationDomain<F>>(
        poly: impl Into<Self>,
        domain: D,
    ) -> Evaluations<F, D> {
        let poly = poly.into();
        poly.eval_over_domain_helper(domain)
    }

    fn eval_over_domain_helper<D: EvaluationDomain<F>>(self, domain: D) -> Evaluations<F, D> {
        let eval_sparse_poly = |s: &SparsePolynomial<F>| {
            let evals = domain.elements().map(|elem| s.evaluate(&elem)).collect();
            Evaluations::from_vec_and_domain(evals, domain)
        };

        match self {
            SPolynomial(Cow::Borrowed(s)) => eval_sparse_poly(s),
            SPolynomial(Cow::Owned(s)) => eval_sparse_poly(&s),
            DPolynomial(Cow::Borrowed(d)) => {
                if d.is_zero() {
                    Evaluations::zero(domain)
                } else {
                    let mut chunks = d.coeffs.chunks(domain.size());
                    let mut first = chunks.next().unwrap().to_vec();
                    let offset = domain.coset_offset();
                    // Reduce the coefficients of the polynomial mod X^domain.size()
                    for (i, chunk) in chunks.enumerate() {
                        if offset.is_one() {
                            cfg_iter_mut!(first).zip(chunk).for_each(|(x, y)| *x += y);
                        } else {
                            let offset_power = offset.pow([((i + 1) * domain.size()) as u64]);
                            cfg_iter_mut!(first)
                                .zip(chunk)
                                .for_each(|(x, y)| *x += offset_power * y);
                        }
                    }
                    domain.fft_in_place(&mut first);
                    Evaluations::from_vec_and_domain(first, domain)
                }
            },
            DPolynomial(Cow::Owned(mut d)) => {
                if d.is_zero() {
                    Evaluations::zero(domain)
                } else {
                    let mut chunks = d.coeffs.chunks_mut(domain.size());
                    let first = chunks.next().unwrap();
                    let offset = domain.coset_offset();
                    // Reduce the coefficients of the polynomial mod X^domain.size()
                    for (i, chunk) in chunks.enumerate() {
                        if offset.is_one() {
                            cfg_iter_mut!(first).zip(chunk).for_each(|(x, y)| *x += y);
                        } else {
                            let offset_power = offset.pow([((i + 1) * domain.size()) as u64]);
                            cfg_iter_mut!(first)
                                .zip(chunk)
                                .for_each(|(x, y)| *x += offset_power * y);
                        }
                    }
                    domain.fft_in_place(&mut d.coeffs);
                    Evaluations::from_vec_and_domain(d.coeffs, domain)
                }
            },
        }
    }
}

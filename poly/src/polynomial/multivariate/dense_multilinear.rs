//! multilinear polynomial represented in evaluation form

use crate::polynomial::MultilinearPolynomialEvaluationForm;
use crate::{MVPolynomial, Polynomial};
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::fmt;
use ark_std::fmt::Formatter;
use ark_std::ops::{Add, AddAssign, Neg, Sub, SubAssign};
use ark_std::vec::Vec;
use rand::Rng;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
/// Stores a multilinear polynomial in dense evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DenseMultilinearPolynomial<F: Field> {
    /// The evaluation over {0,1}^n
    pub evaluations: Vec<F>,
    /// Number of variables
    pub num_vars: usize,
}

impl<F: Field> DenseMultilinearPolynomial<F> {
    /// Construct a new polynomial from a list of evaluations where the index represent a point.
    ///
    /// Index represents a point in {0,1}^`num_vars` in little endian form. For example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[F]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    /// Construct a new polynomial from a list of evaluations where the index represent a point.
    ///
    /// Index represents a point in {0,1}^`num_vars` in little endian form. For example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_vec(num_vars: usize, evaluations: Vec<F>) -> Self {
        // assert the number of variables match size of evaluations
        assert_eq!(
            evaluations.len(),
            1 << num_vars,
            "The size of evaluations should be 2 ^ num_vars."
        );

        Self {
            num_vars,
            evaluations,
        }
    }
    /// Relabel the point inplace by switching `k` scalars from position `a` to position `b`, and from position `b` to position `a` in vector.
    ///
    /// This function turns `P(x_1,...,x_a,...,x_{a+k - 1},...,x_b,...,x_{b+k - 1},...,x_n)`
    /// to `P(x_1,...,x_b,...,x_{b+k - 1},...,x_a,...,x_{a+k - 1},...,x_n)`
    pub fn relabel_inplace(&mut self, mut a: usize, mut b: usize, k: usize) {
        // enforce order of a and b
        if a > b {
            ark_std::mem::swap(&mut a, &mut b);
        }
        assert!(
            a + k < self.num_vars && b + k < self.num_vars,
            "invalid relabel argument"
        );
        if a == b || k == 0 {
            return;
        }
        assert!(a + k <= b, "overlapped swap window is not allowed");
        for i in 0..self.evaluations.len() {
            let j = swap_bits(i, a, b, k);
            if i < j {
                self.evaluations.swap(i, j);
            }
        }
    }
}

impl<F: Field> Polynomial<F> for DenseMultilinearPolynomial<F> {
    type Point = Vec<F>;

    /// return the total degree of the polynomial, which is number of variables according to
    /// multilinear extension formula
    fn degree(&self) -> usize {
        self.num_vars
    }

    fn evaluate(&self, point: &Self::Point) -> F {
        assert_eq!(point.len(), self.num_vars, "Invalid point size");

        self.partial_evaluate(point).evaluations[0]
    }
}

impl<F: Field> MVPolynomial<F> for DenseMultilinearPolynomial<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn rand<R: Rng>(d: usize, num_vars: usize, rng: &mut R) -> Self {
        assert_eq!(
            d, num_vars,
            "for multilinear polynomial, total degree should be equal to number of variables"
        );
        Self::from_evaluations_vec(
            num_vars,
            (0..(1 << num_vars)).map(|_| F::rand(rng)).collect(),
        )
    }
}

impl<F: Field> MultilinearPolynomialEvaluationForm<F> for DenseMultilinearPolynomial<F> {
    type PartialPoint = Vec<F>;

    #[inline]
    fn lookup_evaluation(&self, index: usize) -> F {
        assert!(index < (1 << self.num_vars), "index out of range");
        self.evaluations[index]
    }

    fn relabel(&self, a: usize, b: usize, k: usize) -> Self {
        let mut copied = self.clone();
        copied.relabel_inplace(a, b, k);
        copied
    }

    fn partial_evaluate(&self, partial_point: &Self::PartialPoint) -> Self {
        assert!(
            partial_point.len() <= self.num_vars,
            "invalid size of partial point"
        );
        let mut poly = self.evaluations.to_vec();
        let nv = self.num_vars;
        let dim = partial_point.len();
        // evaluate single variable of partial point from left to right
        for i in 1..dim + 1 {
            let r = partial_point[i - 1];
            for b in 0..(1 << (nv - i)) {
                poly[b] = poly[b << 1] * (F::one() - r) + poly[(b << 1) + 1] * r;
            }
        }
        Self::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
    }
}

impl<F: Field> Add for DenseMultilinearPolynomial<F> {
    type Output = DenseMultilinearPolynomial<F>;

    fn add(self, other: DenseMultilinearPolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a DenseMultilinearPolynomial<F>>
    for &'b DenseMultilinearPolynomial<F>
{
    type Output = DenseMultilinearPolynomial<F>;

    fn add(self, rhs: &'a DenseMultilinearPolynomial<F>) -> Self::Output {
        // handle constant zero case
        if rhs.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return rhs.clone();
        }
        assert_eq!(self.num_vars, rhs.num_vars);
        let result: Vec<F> = cfg_iter!(self.evaluations)
            .zip(cfg_iter!(rhs.evaluations))
            .map(|(a, b)| *a + *b)
            .collect();

        Self::Output::from_evaluations_vec(self.num_vars, result)
    }
}

impl<F: Field> AddAssign for DenseMultilinearPolynomial<F> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a DenseMultilinearPolynomial<F>>
    for DenseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, other: &'a DenseMultilinearPolynomial<F>) {
        *self = &*self + other;
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a DenseMultilinearPolynomial<F>)>
    for DenseMultilinearPolynomial<F>
{
    fn add_assign(&mut self, (f, other): (F, &'a DenseMultilinearPolynomial<F>)) {
        let other = Self {
            num_vars: other.num_vars,
            evaluations: cfg_iter!(other.evaluations).map(|x| f * x).collect(),
        };
        *self = &*self + &other;
    }
}

impl<F: Field> Neg for DenseMultilinearPolynomial<F> {
    type Output = DenseMultilinearPolynomial<F>;

    fn neg(self) -> Self::Output {
        Self::Output {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations).map(|x| -*x).collect(),
        }
    }
}

impl<F: Field> Sub for DenseMultilinearPolynomial<F> {
    type Output = DenseMultilinearPolynomial<F>;

    fn sub(self, other: DenseMultilinearPolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Sub<&'a DenseMultilinearPolynomial<F>>
    for &'b DenseMultilinearPolynomial<F>
{
    type Output = DenseMultilinearPolynomial<F>;

    fn sub(self, rhs: &'a DenseMultilinearPolynomial<F>) -> Self::Output {
        self + &rhs.clone().neg()
    }
}

impl<F: Field> SubAssign for DenseMultilinearPolynomial<F> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a DenseMultilinearPolynomial<F>>
    for DenseMultilinearPolynomial<F>
{
    fn sub_assign(&mut self, other: &'a DenseMultilinearPolynomial<F>) {
        *self = &*self - other;
    }
}

impl<F: Field> fmt::Debug for DenseMultilinearPolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "DenseML(nv = {}, evaluations = [", self.num_vars)?;
        for i in 0..ark_std::cmp::min(8, self.evaluations.len()) {
            write!(f, "{:?} ", self.evaluations[i])?;
        }
        write!(f, "])")?;
        Ok(())
    }
}

impl<F: Field> Zero for DenseMultilinearPolynomial<F> {
    fn zero() -> Self {
        Self {
            num_vars: 0,
            evaluations: vec![F::zero()],
        }
    }

    fn is_zero(&self) -> bool {
        self.num_vars == 0 && self.evaluations[0].is_zero()
    }
}

// swap n bits of x at position a and b
fn swap_bits(x: usize, a: usize, b: usize, n: usize) -> usize {
    let a_bits = (x >> a) & ((1usize << n) - 1);
    let b_bits = (x >> b) & ((1usize << n) - 1);
    let local_xor_mask = a_bits ^ b_bits;
    let global_xor_mask = (local_xor_mask << a) | (local_xor_mask << b);
    x ^ global_xor_mask
}

#[cfg(test)]
mod tests {
    use crate::polynomial::multivariate::dense_multilinear::DenseMultilinearPolynomial;
    use crate::{MVPolynomial, Polynomial};
    use ark_ff::{Field, Zero};
    use ark_std::ops::Neg;
    use ark_std::vec::Vec;
    use ark_std::{test_rng, UniformRand};
    use ark_test_curves::bls12_381::Fr;

    /// utility: evaluate multilinear extension (in form of data array) at a random point
    fn evaluate_data_array<F: Field>(data: &[F], point: &[F]) -> F {
        if data.len() != (1 << point.len()) {
            panic!("Data size mismatch with number of variables. ")
        }

        let nv = point.len();
        let mut a = data.to_vec();

        for i in 1..nv + 1 {
            let r = point[i - 1];
            for b in 0..(1 << (nv - i)) {
                a[b] = a[b << 1] * (F::one() - r) + a[(b << 1) + 1] * r;
            }
        }
        a[0]
    }

    #[test]
    fn evaluate_at_a_point() {
        let mut rng = test_rng();
        let poly = DenseMultilinearPolynomial::rand(10, 10, &mut rng);
        for _ in 0..10 {
            let point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();
            assert_eq!(
                evaluate_data_array(&poly.evaluations, &point),
                poly.evaluate(&point)
            )
        }
    }

    #[test]
    fn relabel_polynomial() {
        let mut rng = test_rng();
        for _ in 0..20 {
            let mut poly = DenseMultilinearPolynomial::rand(10, 10, &mut rng);
            let mut point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();

            let expected = poly.evaluate(&point);

            poly.relabel_inplace(2, 2, 1); // should have no effect
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_inplace(3, 4, 1); // should switch 3 and 4
            point.swap(3, 4);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_inplace(7, 5, 1);
            point.swap(7, 5);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_inplace(2, 5, 3);
            point.swap(2, 5);
            point.swap(3, 6);
            point.swap(4, 7);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_inplace(7, 0, 2);
            point.swap(0, 7);
            point.swap(1, 8);
            assert_eq!(expected, poly.evaluate(&point));
        }
    }

    #[test]
    fn arithmetic() {
        const NV: usize = 10;
        let mut rng = test_rng();
        for _ in 0..20 {
            let point = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
            let poly1 = DenseMultilinearPolynomial::rand(NV, NV, &mut rng);
            let poly2 = DenseMultilinearPolynomial::rand(NV, NV, &mut rng);
            let v1 = poly1.evaluate(&point);
            let v2 = poly2.evaluate(&point);
            // test add
            assert_eq!((&poly1 + &poly2).evaluate(&point), v1 + v2);
            // test sub
            assert_eq!((&poly1 - &poly2).evaluate(&point), v1 - v2);
            // test negate
            assert_eq!(poly1.clone().neg().evaluate(&point), -v1);
            // test add assign
            {
                let mut poly1 = poly1.clone();
                poly1 += &poly2;
                assert_eq!(poly1.evaluate(&point), v1 + v2)
            }
            // test sub assign
            {
                let mut poly1 = poly1.clone();
                poly1 -= &poly2;
                assert_eq!(poly1.evaluate(&point), v1 - v2)
            }
            // test add assign with scalar
            {
                let mut poly1 = poly1.clone();
                let scalar = Fr::rand(&mut rng);
                poly1 += (scalar, &poly2);
                assert_eq!(poly1.evaluate(&point), v1 + scalar * v2)
            }
            // test additive identity
            {
                assert_eq!(&poly1 + &DenseMultilinearPolynomial::zero(), poly1);
                assert_eq!(&DenseMultilinearPolynomial::zero() + &poly1, poly1);
                {
                    let mut poly1_cloned = poly1.clone();
                    poly1_cloned += &DenseMultilinearPolynomial::zero();
                    assert_eq!(&poly1_cloned, &poly1);
                    let mut zero = DenseMultilinearPolynomial::zero();
                    let scalar = Fr::rand(&mut rng);
                    zero += (scalar, &poly1);
                    assert_eq!(zero.evaluate(&point), scalar * v1);
                }
            }
        }
    }
}

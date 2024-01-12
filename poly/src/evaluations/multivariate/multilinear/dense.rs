//! Multilinear polynomial represented in dense evaluation form.

use crate::{
    evaluations::multivariate::multilinear::{swap_bits, MultilinearExtension},
    Polynomial,
};
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    fmt,
    fmt::Formatter,
    ops::{Add, AddAssign, Index, Neg, Sub, SubAssign},
    rand::Rng,
    slice::{Iter, IterMut},
    vec::Vec,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Stores a multilinear polynomial in dense evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DenseMultilinearExtension<F: Field> {
    /// The evaluation over {0,1}^`num_vars`
    pub evaluations: Vec<F>,
    /// Number of variables
    pub num_vars: usize,
}

impl<F: Field> DenseMultilinearExtension<F> {
    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[F]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_vec(num_vars: usize, evaluations: Vec<F>) -> Self {
        // assert that the number of variables matches the size of evaluations
        assert_eq!(
            evaluations.len(),
            1 << num_vars,
            "The size of evaluations should be 2^num_vars."
        );

        Self {
            num_vars,
            evaluations,
        }
    }
    /// Relabel the point in place by switching `k` scalars from position `a` to
    /// position `b`, and from position `b` to position `a` in vector.
    ///
    /// This function turns `P(x_1,...,x_a,...,x_{a+k - 1},...,x_b,...,x_{b+k - 1},...,x_n)`
    /// to `P(x_1,...,x_b,...,x_{b+k - 1},...,x_a,...,x_{a+k - 1},...,x_n)`
    pub fn relabel_in_place(&mut self, mut a: usize, mut b: usize, k: usize) {
        // enforce order of a and b
        if a > b {
            ark_std::mem::swap(&mut a, &mut b);
        }
        if a == b || k == 0 {
            return;
        }
        assert!(b + k <= self.num_vars, "invalid relabel argument");
        assert!(a + k <= b, "overlapped swap window is not allowed");
        for i in 0..self.evaluations.len() {
            let j = swap_bits(i, a, b, k);
            if i < j {
                self.evaluations.swap(i, j);
            }
        }
    }

    /// Returns an iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter(&self) -> Iter<'_, F> {
        self.evaluations.iter()
    }

    /// Returns a mutable iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter_mut(&mut self) -> IterMut<'_, F> {
        self.evaluations.iter_mut()
    }
}

impl<F: Field> MultilinearExtension<F> for DenseMultilinearExtension<F> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn rand<R: Rng>(num_vars: usize, rng: &mut R) -> Self {
        Self::from_evaluations_vec(
            num_vars,
            (0..(1 << num_vars)).map(|_| F::rand(rng)).collect(),
        )
    }

    fn relabel(&self, a: usize, b: usize, k: usize) -> Self {
        let mut copied = self.clone();
        copied.relabel_in_place(a, b, k);
        copied
    }

    /// Return the MLE resulting from binding the first variables of self
    /// to the values in `partial_point` (from left to right).
    ///
    /// Note: this method can be used in combination with `relabel` or
    /// `relabel_in_place` to bind variables at arbitrary positions.
    ///
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// # use ark_poly::{MultilinearExtension, DenseMultilinearExtension};
    ///
    /// // Constructing the two-variate multilinear polynomial x_0 + 2 * x_1 + 3 * x_0 * x_1
    /// // by specifying its evaluations at [00, 10, 01, 11]
    /// let mle = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![0, 1, 2, 6].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    ///
    /// // Bind the first variable of the MLE to the value 5, resulting in
    /// // the new polynomial 5 + 17 * x_1
    /// let bound = mle.fix_variables(&[Fr::from(5)]);
    ///
    /// assert_eq!(bound.to_evaluations(), vec![Fr::from(5), Fr::from(22)]);
    /// ```
    /// }
    fn fix_variables(&self, partial_point: &[F]) -> Self {
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
                let left = poly[b << 1];
                let right = poly[(b << 1) + 1];
                poly[b] = left + r * (right - left);
            }
        }
        Self::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
    }

    fn to_evaluations(&self) -> Vec<F> {
        self.evaluations.to_vec()
    }
}

impl<F: Field> Index<usize> for DenseMultilinearExtension<F> {
    type Output = F;

    /// Returns the evaluation of the polynomial at a point represented by index.
    ///
    /// Index represents a vector in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    ///
    /// For dense multilinear polynomial, `index` takes constant time.
    fn index(&self, index: usize) -> &Self::Output {
        &self.evaluations[index]
    }
}

impl<F: Field> Add for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn add(self, other: DenseMultilinearExtension<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a DenseMultilinearExtension<F>> for &'b DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn add(self, rhs: &'a DenseMultilinearExtension<F>) -> Self::Output {
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

impl<F: Field> AddAssign for DenseMultilinearExtension<F> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, F: Field> AddAssign<&'a DenseMultilinearExtension<F>> for DenseMultilinearExtension<F> {
    fn add_assign(&mut self, other: &'a DenseMultilinearExtension<F>) {
        *self = &*self + other;
    }
}

impl<'a, F: Field> AddAssign<(F, &'a DenseMultilinearExtension<F>)>
    for DenseMultilinearExtension<F>
{
    fn add_assign(&mut self, (f, other): (F, &'a DenseMultilinearExtension<F>)) {
        let other = Self {
            num_vars: other.num_vars,
            evaluations: cfg_iter!(other.evaluations).map(|x| f * x).collect(),
        };
        *self = &*self + &other;
    }
}

impl<F: Field> Neg for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn neg(self) -> Self::Output {
        Self::Output {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations).map(|x| -*x).collect(),
        }
    }
}

impl<F: Field> Sub for DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn sub(self, other: DenseMultilinearExtension<F>) -> Self {
        &self - &other
    }
}

impl<'a, 'b, F: Field> Sub<&'a DenseMultilinearExtension<F>> for &'b DenseMultilinearExtension<F> {
    type Output = DenseMultilinearExtension<F>;

    fn sub(self, rhs: &'a DenseMultilinearExtension<F>) -> Self::Output {
        self + &rhs.clone().neg()
    }
}

impl<F: Field> SubAssign for DenseMultilinearExtension<F> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, F: Field> SubAssign<&'a DenseMultilinearExtension<F>> for DenseMultilinearExtension<F> {
    fn sub_assign(&mut self, other: &'a DenseMultilinearExtension<F>) {
        *self = &*self - other;
    }
}

impl<F: Field> fmt::Debug for DenseMultilinearExtension<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "DenseML(nv = {}, evaluations = [", self.num_vars)?;
        for i in 0..ark_std::cmp::min(4, self.evaluations.len()) {
            write!(f, "{:?} ", self.evaluations[i])?;
        }
        if self.evaluations.len() < 4 {
            write!(f, "])")?;
        } else {
            write!(f, "...])")?;
        }
        Ok(())
    }
}

impl<F: Field> Zero for DenseMultilinearExtension<F> {
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

impl<F: Field> Polynomial<F> for DenseMultilinearExtension<F> {
    type Point = Vec<F>;

    fn degree(&self) -> usize {
        self.num_vars
    }

    /// Evaluate the dense MLE at the given point
    /// # Example
    /// ```
    /// use ark_test_curves::bls12_381::Fr;
    /// # use ark_poly::{MultilinearExtension, DenseMultilinearExtension, Polynomial};
    /// # use ark_ff::One;
    ///
    /// // The two-variate polynomial x_0 + 3 * x_0 * x_1 + 2 evaluates to [2, 3, 2, 6]
    /// // in the two-dimensional hypercube with points [00, 10, 01, 11]
    /// let mle = DenseMultilinearExtension::from_evaluations_vec(
    ///     2, vec![2, 3, 2, 6].iter().map(|x| Fr::from(*x as u64)).collect()
    /// );
    ///
    /// // By the uniqueness of MLEs, `mle` is precisely the above polynomial, which
    /// // takes the value 54 at the point (1, 17)
    /// let eval = mle.evaluate(&[Fr::one(), Fr::from(17)].into());
    /// assert_eq!(eval, Fr::from(54));
    /// ```
    fn evaluate(&self, point: &Self::Point) -> F {
        assert!(point.len() == self.num_vars);
        self.fix_variables(&point)[0]
    }
}

#[cfg(test)]
mod tests {
    use crate::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use ark_ff::{Field, Zero};
    use ark_std::{ops::Neg, test_rng, vec::Vec, UniformRand};
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
        let poly = DenseMultilinearExtension::rand(10, &mut rng);
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
            let mut poly = DenseMultilinearExtension::rand(10, &mut rng);
            let mut point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();

            let expected = poly.evaluate(&point);

            poly.relabel_in_place(2, 2, 1); // should have no effect
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(3, 4, 1); // should switch 3 and 4
            point.swap(3, 4);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(7, 5, 1);
            point.swap(7, 5);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(2, 5, 3);
            point.swap(2, 5);
            point.swap(3, 6);
            point.swap(4, 7);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(7, 0, 2);
            point.swap(0, 7);
            point.swap(1, 8);
            assert_eq!(expected, poly.evaluate(&point));

            poly.relabel_in_place(0, 9, 1);
            point.swap(0, 9);
            assert_eq!(expected, poly.evaluate(&point));
        }
    }

    #[test]
    fn arithmetic() {
        const NV: usize = 10;
        let mut rng = test_rng();
        for _ in 0..20 {
            let point: Vec<_> = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
            let poly1 = DenseMultilinearExtension::rand(NV, &mut rng);
            let poly2 = DenseMultilinearExtension::rand(NV, &mut rng);
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
                assert_eq!(&poly1 + &DenseMultilinearExtension::zero(), poly1);
                assert_eq!(&DenseMultilinearExtension::zero() + &poly1, poly1);
                {
                    let mut poly1_cloned = poly1.clone();
                    poly1_cloned += &DenseMultilinearExtension::zero();
                    assert_eq!(&poly1_cloned, &poly1);
                    let mut zero = DenseMultilinearExtension::zero();
                    let scalar = Fr::rand(&mut rng);
                    zero += (scalar, &poly1);
                    assert_eq!(zero.evaluate(&point), scalar * v1);
                }
            }
        }
    }
}

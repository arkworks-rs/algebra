//! Work with sparse multivariate polynomials.
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    cmp::Ordering,
    fmt::{Debug, Error, Formatter},
    hash::Hash,
    ops::Deref,
    vec::*,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod sparse;
pub use sparse::SparsePolynomial;

/// Describes the interface for a term (monomial) of a multivariate polynomial.
pub trait Term:
    Clone
    + PartialOrd
    + Ord
    + PartialEq
    + Eq
    + Hash
    + Default
    + Debug
    + Deref<Target = [(usize, usize)]>
    + Send
    + Sync
    + CanonicalSerialize
    + CanonicalDeserialize
{
    /// Create a new `Term` from a list of tuples of the form `(variable, power)`
    fn new(term: Vec<(usize, usize)>) -> Self;

    /// Returns the total degree of `self`. This is the sum of all variable
    /// powers in `self`
    fn degree(&self) -> usize;

    /// Returns a list of variables in `self`
    fn vars(&self) -> Vec<usize>;

    /// Returns a list of the powers of each variable in `self`
    fn powers(&self) -> Vec<usize>;

    /// Returns whether `self` is a constant
    fn is_constant(&self) -> bool;

    /// Evaluates `self` at the point `p`.
    fn evaluate<F: Field>(&self, p: &[F]) -> F;
}

/// Stores a term (monomial) in a multivariate polynomial.
/// Each element is of the form `(variable, power)`.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct SparseTerm(Vec<(usize, usize)>);

impl SparseTerm {
    /// Sums the powers of any duplicated variables. Assumes `term` is sorted.
    fn combine(term: &[(usize, usize)]) -> Vec<(usize, usize)> {
        let mut term_dedup: Vec<(usize, usize)> = Vec::new();
        for (var, pow) in term {
            if let Some(prev) = term_dedup.last_mut() {
                if prev.0 == *var {
                    prev.1 += pow;
                    continue;
                }
            }
            term_dedup.push((*var, *pow));
        }
        term_dedup
    }
}

impl Term for SparseTerm {
    /// Create a new `Term` from a list of tuples of the form `(variable, power)`
    fn new(mut term: Vec<(usize, usize)>) -> Self {
        // Remove any terms with power 0
        term.retain(|(_, pow)| *pow != 0);
        // If there are more than one variables, make sure they are
        // in order and combine any duplicates
        if term.len() > 1 {
            term.sort_by(|(v1, _), (v2, _)| v1.cmp(v2));
            term = Self::combine(&term);
        }
        Self(term)
    }

    /// Returns the sum of all variable powers in `self`
    fn degree(&self) -> usize {
        self.iter().fold(0, |sum, acc| sum + acc.1)
    }

    /// Returns a list of variables in `self`
    fn vars(&self) -> Vec<usize> {
        self.iter().map(|(v, _)| *v).collect()
    }

    /// Returns a list of variable powers in `self`
    fn powers(&self) -> Vec<usize> {
        self.iter().map(|(_, p)| *p).collect()
    }

    /// Returns whether `self` is a constant
    fn is_constant(&self) -> bool {
        self.len() == 0 || self.degree() == 0
    }

    /// Evaluates `self` at the given `point` in the field.
    fn evaluate<F: Field>(&self, point: &[F]) -> F {
        cfg_into_iter!(self)
            .map(|(var, power)| point[*var].pow([*power as u64]))
            .product()
    }
}

impl Debug for SparseTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        for variable in self.iter() {
            if variable.1 == 1 {
                write!(f, " * x_{}", variable.0)?;
            } else {
                write!(f, " * x_{}^{}", variable.0, variable.1)?;
            }
        }
        Ok(())
    }
}

impl Deref for SparseTerm {
    type Target = [(usize, usize)];

    fn deref(&self) -> &[(usize, usize)] {
        &self.0
    }
}

impl PartialOrd for SparseTerm {
    /// Sort by total degree. If total degree is equal then ordering
    /// is given by exponent weight in lower-numbered variables
    /// ie. `x_1 > x_2`, `x_1^2 > x_1 * x_2`, etc.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.degree() != other.degree() {
            Some(self.degree().cmp(&other.degree()))
        } else {
            // Iterate through all variables and return the corresponding ordering
            // if they differ in variable numbering or power
            for ((cur_variable, cur_power), (other_variable, other_power)) in
                self.iter().zip(other.iter())
            {
                if other_variable == cur_variable {
                    if cur_power != other_power {
                        return Some(cur_power.cmp(other_power));
                    }
                } else {
                    return Some(other_variable.cmp(cur_variable));
                }
            }
            Some(Ordering::Equal)
        }
    }
}

impl Ord for SparseTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{Fp64, MontBackend, MontConfig};

    #[derive(MontConfig)]
    #[modulus = "5"]
    #[generator = "2"]
    pub struct F5Config;

    pub type F5 = Fp64<MontBackend<F5Config, 1>>;

    #[test]
    fn test_sparse_term_combine() {
        let term = vec![(1, 2), (1, 3), (2, 1)];
        let combined = SparseTerm::combine(&term);
        assert_eq!(combined, vec![(1, 5), (2, 1)]);
    }

    #[test]
    fn test_sparse_term_new() {
        let term = vec![(2, 1), (1, 2), (1, 3), (3, 0)];
        let sparse_term = SparseTerm::new(term);
        // We expect the terms:
        // - To be sorted by variable
        // - To have combined the powers of the same variable
        // - To have removed any terms with power 0
        assert_eq!(sparse_term, SparseTerm(vec![(1, 5), (2, 1)]));
    }

    #[test]
    fn test_sparse_term_degree() {
        let term = SparseTerm::new(vec![(1, 2), (2, 3)]);
        assert_eq!(term.degree(), 5); // 2 + 3 = 5
    }

    #[test]
    fn test_sparse_term_vars() {
        let term = SparseTerm::new(vec![(1, 1), (1, 2), (2, 3)]);
        assert_eq!(term.vars(), vec![1, 2]);
    }

    #[test]
    fn test_sparse_term_powers() {
        let term = SparseTerm::new(vec![(1, 2), (1, 3), (2, 3)]);
        assert_eq!(term.powers(), vec![5, 3]);
    }

    #[test]
    fn test_sparse_term_is_constant() {
        let constant_term = SparseTerm::new(vec![]);
        assert!(constant_term.is_constant());

        let non_constant_term = SparseTerm::new(vec![(1, 2)]);
        assert!(!non_constant_term.is_constant());
    }

    #[test]
    fn test_evaluate() {
        let term = SparseTerm::new(vec![(0, 2), (1, 3)]);
        let point = vec![F5::from(1u64), F5::from(2u64)];
        let result = term.evaluate::<F5>(&point);
        assert_eq!(result, F5::from(8u64)); // (1^2 * 2^3) = 8 in F5
    }

    #[test]
    fn test_partial_cmp() {
        let term1 = SparseTerm::new(vec![(1, 2), (2, 3)]);
        let term2 = SparseTerm::new(vec![(1, 2), (2, 2)]);
        let term3 = SparseTerm::new(vec![(2, 3), (1, 2)]);
        let term4 = SparseTerm::new(vec![(1, 2)]);
        let term5 = SparseTerm::new(vec![(2, 2)]);
        // Constant term (all exponents are zero)
        let term6 = SparseTerm::new(vec![(1, 0), (2, 0)]);
        // Empty term, should also be constant
        let term7 = SparseTerm::new(vec![]);

        // Comparing terms with different degrees
        assert_eq!(term1.partial_cmp(&term2), Some(Ordering::Greater)); // term1 > term2
        assert_eq!(term1.partial_cmp(&term3), Some(Ordering::Equal)); // term1 == term3
        assert_eq!(term2.partial_cmp(&term3), Some(Ordering::Less)); // term2 < term3

        // Comparing terms with equal degree but different exponents
        assert_eq!(term1.partial_cmp(&term4), Some(Ordering::Greater)); // term1 > term4
        assert_eq!(term4.partial_cmp(&term5), Some(Ordering::Greater)); // term4 > term5 (x_1 > x_2)
        assert_eq!(term4.partial_cmp(&term6), Some(Ordering::Greater)); // term4 > term6 (degree 2 vs. degree 0)

        // Comparing constant terms
        assert_eq!(term6.partial_cmp(&term7), Some(Ordering::Equal)); // term6 == term7 (both constants)
        assert_eq!(term7.partial_cmp(&term1), Some(Ordering::Less)); // term7 < term1 (constant < non-constant)
    }

    #[test]
    fn test_cmp() {
        let term1 = SparseTerm::new(vec![(1, 2), (2, 3)]);
        let term2 = SparseTerm::new(vec![(1, 2), (2, 2)]);
        let term3 = SparseTerm::new(vec![(2, 3), (1, 2)]);
        let term4 = SparseTerm::new(vec![(1, 2)]);
        let term5 = SparseTerm::new(vec![(2, 2)]);
        // Constant term (all exponents are zero)
        let term6 = SparseTerm::new(vec![(1, 0), (2, 0)]);
        // Empty term, should also be constant
        let term7 = SparseTerm::new(vec![]);

        // Comparing terms with different degrees
        assert_eq!(term1.cmp(&term2), Ordering::Greater); // term1 > term2
        assert_eq!(term1.cmp(&term3), Ordering::Equal); // term1 == term3
        assert_eq!(term2.cmp(&term3), Ordering::Less); // term2 < term3

        // Comparing terms with equal degree but different exponents
        assert_eq!(term1.cmp(&term4), Ordering::Greater); // term1 > term4
        assert_eq!(term4.cmp(&term5), Ordering::Greater); // term4 > term5 (x_1 > x_2)
        assert_eq!(term4.cmp(&term6), Ordering::Greater); // term4 > term6 (degree 2 vs. degree 0)

        // Comparing constant terms
        assert_eq!(term6.cmp(&term7), Ordering::Equal); // term6 == term7 (both constants)
        assert_eq!(term7.cmp(&term1), Ordering::Less); // term7 < term1 (constant < non-constant)
    }
}

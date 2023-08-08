use crate::{
    module::{Scalar, ScalarMul, ScalarExp},
    AdditiveGroup, MultiplicativeGroup,
};
use ark_std::vec::Vec;

/// A helper type that contains all the context required for computing
/// a window NAF multiplication of a group element by a scalar.
pub struct WnafContext {
    pub window_size: usize,
}

impl WnafContext {
    /// Constructs a new context for a window of size `window_size`.
    ///
    /// # Panics
    ///
    /// This function will panic if not `2 <= window_size < 64`
    pub fn new(window_size: usize) -> Self {
        assert!(window_size >= 2);
        assert!(window_size < 64);
        Self { window_size }
    }
}

impl WnafContext {
    pub fn additive_table<G: AdditiveGroup>(&self, mut base: G) -> Vec<G> {
        let mut table = Vec::with_capacity(1 << (self.window_size - 1));
        let dbl = base.double();

        for _ in 0..(1 << (self.window_size - 1)) {
            table.push(base);
            base += &dbl;
        }
        table
    }

    /// Computes scalar multiplication of a group element `g` by `scalar`.
    ///
    /// This method uses the wNAF algorithm to perform the scalar
    /// multiplication; first, it uses `Self::table` to calculate an
    /// appropriate table of multiples of `g`, and then uses the wNAF
    /// algorithm to compute the scalar multiple.
    pub fn mul<G: ScalarMul<S>, S: Scalar>(&self, g: G, scalar: &S) -> G {
        let table = self.additive_table(g);
        self.mul_with_table(&table, scalar).unwrap()
    }

    /// Computes scalar multiplication of a group element by `scalar`.
    /// `base_table` holds precomputed multiples of the group element; it can be
    /// generated using `Self::table`. `scalar` is an element of
    /// `G::ScalarField`.
    ///
    /// Returns `None` if the table is too small.
    pub fn mul_with_table<G: ScalarMul<S>, S: Scalar>(
        &self,
        base_table: &[G],
        scalar: &S,
    ) -> Option<G> {
        if 1 << (self.window_size - 1) > base_table.len() {
            return None;
        }
        let scalar_wnaf = scalar.find_wnaf(self.window_size).unwrap();

        let mut result = G::zero();

        let mut found_non_zero = false;

        for n in scalar_wnaf.iter().rev() {
            if found_non_zero {
                result.double_in_place();
            }

            if *n != 0 {
                found_non_zero = true;

                if *n > 0 {
                    result += &base_table[(n / 2) as usize];
                } else {
                    result -= &base_table[((-n) / 2) as usize];
                }
            }
        }

        Some(result)
    }
}


impl WnafContext {
    pub fn multiplicative_table<G: MultiplicativeGroup>(&self, mut base: G) -> Vec<G> {
        let mut table = Vec::with_capacity(1 << (self.window_size - 1));
        let sqr = base.square();

        for _ in 0..(1 << (self.window_size - 1)) {
            table.push(base);
            base *= &sqr;
        }
        table
    }

    /// Computes scalar multiplication of a group element `g` by `scalar`.
    ///
    /// This method uses the wNAF algorithm to perform the scalar
    /// multiplication; first, it uses `Self::table` to calculate an
    /// appropriate table of multiples of `g`, and then uses the wNAF
    /// algorithm to compute the scalar multiple.
    pub fn exp<G: ScalarExp<S>, S: Scalar>(&self, g: G, scalar: &S) -> G {
        let table = self.multiplicative_table(g);
        self.exp_with_table(&table, scalar).unwrap()
    }

    /// Computes scalar multiplication of a group element by `scalar`.
    /// `base_table` holds precomputed multiples of the group element; it can be
    /// generated using `Self::table`. `scalar` is an element of
    /// `G::ScalarField`.
    ///
    /// Returns `None` if the table is too small.
    pub fn exp_with_table<G: ScalarExp<S>, S: Scalar>(
        &self,
        base_table: &[G],
        scalar: &S,
    ) -> Option<G> {
        if 1 << (self.window_size - 1) > base_table.len() {
            return None;
        }
        let scalar_wnaf = scalar.find_wnaf(self.window_size).unwrap();
        let inv_table = if G::INVERSION_IS_FAST {
            vec![]
        } else {
            G::invert_batch(base_table)
        };

        let mut result = G::one();

        let mut found_non_zero = false;

        for n in scalar_wnaf.iter().rev() {
            if found_non_zero {
                result.square_in_place();
            }

            if *n != 0 {
                found_non_zero = true;

                if *n > 0 {
                    result *= &base_table[(n / 2) as usize];
                } else {
                    result *= &inv_table[(n / 2) as usize];
                }
            }
        }

        Some(result)
    }
}
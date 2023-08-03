use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    cmp::max,
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    UniformRand,
};
use num_traits::{One, Zero};
use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub trait AdditiveGroup:
    Eq
    + 'static
    + Sized
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Clone
    + Default
    + Send
    + Sync
    + Hash
    + Debug
    + Display
    + UniformRand
    + Zeroize
    + Zero
    + Neg<Output = Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> Add<&'a mut Self, Output = Self>
    + for<'a> Sub<&'a mut Self, Output = Self>
    + for<'a> AddAssign<&'a mut Self>
    + for<'a> SubAssign<&'a mut Self>
    + ark_std::iter::Sum<Self>
    + for<'a> ark_std::iter::Sum<&'a Self>
{
    /// The additive identity of the field.
    const ZERO: Self;

    /// Doubles `self`.
    #[must_use]
    fn double(&self) -> Self {
        let mut copy = *self;
        copy.double_in_place();
        copy
    }
    /// Doubles `self` in place.
    fn double_in_place(&mut self) -> &mut Self {
        self.add_assign(*self);
        self
    }

    /// Negates `self` in place.
    fn neg_in_place(&mut self) -> &mut Self {
        *self = -(*self);
        self
    }
}

/// A multiplicative group with an optional zero element.
/// If the multiplicative group has an associated zero element, then the
/// group law applies only to non-zero elements, and the inverse of the zero element
/// is defined as zero.
///
/// Furthermore, since `MultiplicativeGroupWithZero`s are usually used in the context of
/// rings, we assume that the zero element is the additive identity of the ring.
pub trait MultiplicativeGroup:
    Eq
    + 'static
    + Sized
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Clone
    + Default
    + Send
    + Sync
    + Hash
    + Debug
    + Display
    + UniformRand
    + Zeroize
    + One
    + Mul<Self, Output = Self>
    + Div<Self, Output = Self>
    + MulAssign<Self>
    + DivAssign<Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> MulAssign<&'a Self>
    + for<'a> Mul<&'a mut Self, Output = Self>
    + for<'a> MulAssign<&'a mut Self>
    + for<'a> Div<&'a Self, Output = Self>
    + for<'a> DivAssign<&'a Self>
    + for<'a> Div<&'a mut Self, Output = Self>
    + for<'a> DivAssign<&'a mut Self>
    + ark_std::iter::Product<Self>
    + for<'a> ark_std::iter::Product<&'a Self>
{
    const ONE: Self;

    #[doc(hidden)]
    fn _is_zero(&self) -> bool;

    /// Square `self`.
    #[must_use]
    fn square(&self) -> Self {
        let mut copy = *self;
        copy.square_in_place();
        copy
    }
    /// Squares `self` in place.
    fn square_in_place(&mut self) -> &mut Self {
        *self *= *self;
        self
    }

    /// Inverts `self` in place.
    fn invert_in_place(&mut self) -> &mut Self;

    /// Negates `self` in place.
    fn invert(&self) -> Self {
        let mut copy = *self;
        copy.invert_in_place();
        copy
    }

    fn invert_batch_in_place(v: &mut [Self]) {
        invert_and_mul_batch(v, &Self::one());
    }

    fn invert_batch(v: &[Self]) -> Vec<Self> {
        let mut v = v.to_vec();
        Self::invert_batch_in_place(&mut v);
        v
    }
}

#[cfg(not(feature = "parallel"))]
// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}
pub fn invert_and_mul_batch<G: MultiplicativeGroup>(v: &mut [G], coeff: &G) {
    serial_invert_and_mul_batch(v, coeff);
}

#[cfg(feature = "parallel")]
// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}
pub fn invert_and_mul_batch<G: MultiplicativeGroup>(v: &mut [G], coeff: &G) {
    // Divide the vector v evenly between all available cores
    let min_elements_per_thread = 1;
    let num_cpus_available = rayon::current_num_threads();
    let num_elems = v.len();
    let num_elem_per_thread = max(num_elems / num_cpus_available, min_elements_per_thread);

    // Batch invert in parallel, without copying the vector
    v.par_chunks_mut(num_elem_per_thread).for_each(|mut chunk| {
        serial_invert_and_mul_batch(&mut chunk, coeff);
    });
}

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
/// This method is explicitly single-threaded.
fn serial_invert_and_mul_batch<G: MultiplicativeGroup>(v: &mut [G], coeff: &G) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2
    // but with an optimization to multiply every element in the returned vector by
    // coeff

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = G::one();
    for f in v.iter().filter(|f| !f._is_zero()) {
        tmp.mul_assign(f);
        prod.push(tmp);
    }

    // Invert `tmp`.
    tmp = tmp.invert(); // Guaranteed to be nonzero.

    // Multiply product by coeff, so all inverses will be scaled by coeff
    tmp *= coeff;

    // Second pass: iterate backwards to compute inverses
    for (f, s) in v.iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|f| !f._is_zero())
        // Backwards, skip last element, fill in one for last term.
        .zip(prod.into_iter().rev().skip(1).chain(Some(G::one())))
    {
        // tmp := tmp * f; f := tmp * s = 1/f
        let new_tmp = tmp * *f;
        *f = tmp * &s;
        tmp = new_tmp;
    }
}

//! A space-efficient implementation of Pippenger's algorithm.
//!
use crate::AffineCurve;
use ark_ff::{PrimeField, Zero};

use ark_std::{borrow::Borrow, ops::AddAssign, vec::Vec};

/// Struct for the chunked Pippenger algorithm.
pub struct ChunkedPippenger<G: AffineCurve> {
    pub scalars_buffer: Vec<<G::ScalarField as PrimeField>::BigInt>,
    pub bases_buffer: Vec<G>,
    pub result: G::Projective,
    pub buf_size: usize,
}

impl<G: AffineCurve> ChunkedPippenger<G> {
    /// Initialize a chunked Pippenger instance with default parameters.
    pub fn new(max_msm_buffer: usize) -> Self {
        Self {
            scalars_buffer: Vec::with_capacity(max_msm_buffer),
            bases_buffer: Vec::with_capacity(max_msm_buffer),
            result: G::Projective::zero(),
            buf_size: max_msm_buffer,
        }
    }

    /// Initialize a chunked Pippenger instance with the given buffer size.
    pub fn with_size(buf_size: usize) -> Self {
        Self {
            scalars_buffer: Vec::with_capacity(buf_size),
            bases_buffer: Vec::with_capacity(buf_size),
            result: G::Projective::zero(),
            buf_size,
        }
    }

    /// Add a new (base, scalar) pair into the instance.
    #[inline(always)]
    pub fn add<B, S>(&mut self, base: B, scalar: S)
    where
        B: Borrow<G>,
        S: Borrow<<G::ScalarField as PrimeField>::BigInt>,
    {
        self.scalars_buffer.push(*scalar.borrow());
        self.bases_buffer.push(*base.borrow());
        if self.scalars_buffer.len() == self.buf_size {
            self.result.add_assign(crate::msm::VariableBase::msm(
                self.bases_buffer.as_slice(),
                self.scalars_buffer.as_slice(),
            ));
            self.scalars_buffer.clear();
            self.bases_buffer.clear();
        }
    }

    /// Output the final Pippenger algorithm result.
    #[inline(always)]
    pub fn finalize(mut self) -> G::Projective {
        if !self.scalars_buffer.is_empty() {
            self.result.add_assign(crate::msm::VariableBase::msm(
                self.bases_buffer.as_slice(),
                self.scalars_buffer.as_slice(),
            ));
        }
        self.result
    }
}

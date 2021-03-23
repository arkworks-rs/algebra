// The code below is a port of the excellent library of https://github.com/kwantam/fffft by Riad S. Wahby
// to the arkworks APIs

use crate::domain::utils::compute_powers_serial;
use crate::domain::{radix2::*, DomainCoeff};
use ark_ff::FftField;
use ark_std::{cfg_iter_mut, vec::Vec};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(PartialEq, Eq, Debug)]
enum FFTOrder {
    /// Both the input and the output of the FFT must be in-order.
    II,
    /// The input of the FFT must be in-order, but the output does not have to be.
    IO,
    /// The input of the FFT can be out of order, but the output must be in-order.
    OI,
}

impl<F: FftField> Radix2EvaluationDomain<F> {
    pub(crate) fn in_order_fft_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T]) {
        self.fft_helper_in_place(x_s, FFTOrder::II)
    }

    pub(crate) fn in_order_ifft_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T]) {
        self.ifft_helper_in_place(x_s, FFTOrder::II);
        ark_std::cfg_iter_mut!(x_s).for_each(|val| *val *= self.size_inv);
    }

    pub(crate) fn in_order_coset_ifft_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T]) {
        self.ifft_helper_in_place(x_s, FFTOrder::II);
        let coset_shift = self.generator_inv;
        Self::distribute_powers_and_mul_by_const(x_s, coset_shift, self.size_inv);
    }

    fn fft_helper_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T], ord: FFTOrder) {
        use FFTOrder::*;

        let log_len = ark_std::log2(x_s.len());

        if ord == OI {
            self.oi_helper(x_s, self.group_gen);
        } else {
            self.io_helper(x_s, self.group_gen);
        }

        if ord == II {
            derange(x_s, log_len);
        }
    }

    // Handles doing an IFFT with handling of being in order and out of order.
    // The results here must all be divided by |x_s|,
    // which is left up to the caller to do.
    fn ifft_helper_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T], ord: FFTOrder) {
        use FFTOrder::*;

        let log_len = ark_std::log2(x_s.len());

        if ord == II {
            derange(x_s, log_len);
        }

        if ord == IO {
            self.io_helper(x_s, self.group_gen_inv);
        } else {
            self.oi_helper(x_s, self.group_gen_inv);
        }
    }

    /// Computes the first `self.size / 2` roots of unity for the entire domain.
    /// e.g. for the domain [1, g, g^2, ..., g^{n - 1}], it computes
    // [1, g, g^2, ..., g^{(n/2) - 1}]
    #[cfg(not(feature = "parallel"))]
    pub(super) fn roots_of_unity(&self, root: F) -> Vec<F> {
        compute_powers_serial((self.size as usize) / 2, root)
    }

    /// Computes the first `self.size / 2` roots of unity.
    #[cfg(feature = "parallel")]
    pub(super) fn roots_of_unity(&self, root: F) -> Vec<F> {
        // TODO: check if this method can replace parallel compute powers.
        let log_size = ark_std::log2(self.size as usize);
        // early exit for short inputs
        if log_size <= LOG_ROOTS_OF_UNITY_PARALLEL_SIZE {
            compute_powers_serial((self.size as usize) / 2, root)
        } else {
            let mut temp = root;
            // w, w^2, w^4, w^8, ..., w^(2^(log_size - 1))
            let log_powers: Vec<F> = (0..(log_size - 1))
                .map(|_| {
                    let old_value = temp;
                    temp.square_in_place();
                    old_value
                })
                .collect();

            // allocate the return array and start the recursion
            let mut powers = vec![F::zero(); 1 << (log_size - 1)];
            Self::roots_of_unity_recursive(&mut powers, &log_powers);
            powers
        }
    }

    #[cfg(feature = "parallel")]
    fn roots_of_unity_recursive(out: &mut [F], log_powers: &[F]) {
        assert_eq!(out.len(), 1 << log_powers.len());
        // base case: just compute the powers sequentially,
        // g = log_powers[0], out = [1, g, g^2, ...]
        if log_powers.len() <= LOG_ROOTS_OF_UNITY_PARALLEL_SIZE as usize {
            out[0] = F::one();
            for idx in 1..out.len() {
                out[idx] = out[idx - 1] * log_powers[0];
            }
            return;
        }

        // recursive case:
        // 1. split log_powers in half
        let (lr_lo, lr_hi) = log_powers.split_at((1 + log_powers.len()) / 2);
        let mut scr_lo = vec![F::default(); 1 << lr_lo.len()];
        let mut scr_hi = vec![F::default(); 1 << lr_hi.len()];
        // 2. compute each half individually
        rayon::join(
            || Self::roots_of_unity_recursive(&mut scr_lo, lr_lo),
            || Self::roots_of_unity_recursive(&mut scr_hi, lr_hi),
        );
        // 3. recombine halves
        // At this point, out is a blank slice.
        out.par_chunks_mut(scr_lo.len())
            .zip(&scr_hi)
            .for_each(|(out_chunk, scr_hi)| {
                for (out_elem, scr_lo) in out_chunk.iter_mut().zip(&scr_lo) {
                    *out_elem = *scr_hi * scr_lo;
                }
            });
    }

    fn io_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        // In the sequential case, we will keep on making the roots cache-aligned,
        // according to the access pattern that the FFT uses.
        // It is left as a TODO to implement this for the parallel case
        #[allow(unused_mut)]
        let mut roots = self.roots_of_unity(root);

        #[cfg(not(feature = "parallel"))]
        let (mut root_len, mut first_iteration) = (roots.len(), true);

        let mut gap = xi.len() / 2;
        while gap > 0 {
            // each butterfly cluster uses 2*gap positions
            let chunk_size = 2 * gap;
            #[cfg(feature = "parallel")]
            let nchunks = xi.len() / chunk_size;

            // Cache align the FFT roots in the sequential case.
            // In this case, we are aiming to make every root that is accessed one after another,
            // appear one after another in the list of roots.
            #[cfg(not(feature = "parallel"))]
            {
                // Roots are already cache aligned in the first iteration, so we don't need to do anything.
                if !first_iteration {
                    // if the roots are cache aligned in iteration i, then in iteration i+1,
                    // cache alignment requires selecting every other root.
                    // (The even powers relative to the current iterations generator)
                    for i in 1..(root_len / 2) {
                        roots[i] = roots[i * 2];
                    }
                    root_len /= 2;
                    first_iteration = false;
                }
            }

            let butterfly_fn = |(chunk_index, (lo, hi)): (usize, (&mut T, &mut T))| {
                let neg = *lo - *hi;
                *lo += *hi;

                *hi = neg;

                #[cfg(feature = "parallel")]
                let index = nchunks * chunk_index;
                // Due to cache aligning, the index into roots is the chunk index
                #[cfg(not(feature = "parallel"))]
                let index = chunk_index;

                *hi *= roots[index];
            };

            ark_std::cfg_chunks_mut!(xi, chunk_size).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                // If the chunk is sufficiently big that parallelism helps,
                // we parallelize the butterfly operation within the chunk.
                //
                // if chunk_size > MIN_CHUNK_SIZE_FOR_PARALLELIZATION
                if gap > MIN_CHUNK_SIZE_FOR_PARALLELIZATION / 2 {
                    cfg_iter_mut!(lo).zip(hi).enumerate().for_each(butterfly_fn);
                } else {
                    lo.iter_mut().zip(hi).enumerate().for_each(butterfly_fn);
                }
            });
            gap /= 2;
        }
    }

    fn oi_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        let roots = self.roots_of_unity(root);

        let mut gap = 1;
        while gap < xi.len() {
            let chunk_size = 2 * gap;
            let nchunks = xi.len() / chunk_size;

            let butterfly_fn = |(idx, (lo, hi)): (usize, (&mut T, &mut T))| {
                *hi *= roots[nchunks * idx];
                let neg = *lo - *hi;
                *lo += *hi;
                *hi = neg;
            };

            ark_std::cfg_chunks_mut!(xi, chunk_size).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                // If the chunk is sufficiently big that parallelism helps,
                // we parallelize the butterfly operation within the chunk.
                //
                // if chunk_size > MIN_CHUNK_SIZE_FOR_PARALLELIZATION
                if gap > MIN_CHUNK_SIZE_FOR_PARALLELIZATION / 2 {
                    cfg_iter_mut!(lo).zip(hi).enumerate().for_each(butterfly_fn);
                } else {
                    lo.iter_mut().zip(hi).enumerate().for_each(butterfly_fn);
                }
            });
            gap *= 2;
        }
    }
}

// This value controls that when doing a butterfly on a chunk of size c,
// do you parallelize operations on the chunk.
// If c > MIN_CHUNK_SIZE_FOR_PARALLELIZATION,
// then parallelize, else be sequential.
// This value was chosen empirically.
const MIN_CHUNK_SIZE_FOR_PARALLELIZATION: usize = 2048;

// minimum size at which to parallelize.
#[cfg(feature = "parallel")]
const LOG_ROOTS_OF_UNITY_PARALLEL_SIZE: u32 = 7;

#[inline]
fn bitrev(a: u64, log_len: u32) -> u64 {
    a.reverse_bits() >> (64 - log_len)
}

fn derange<T>(xi: &mut [T], log_len: u32) {
    for idx in 1..(xi.len() as u64 - 1) {
        let ridx = bitrev(idx, log_len);
        if idx < ridx {
            xi.swap(idx as usize, ridx as usize);
        }
    }
}

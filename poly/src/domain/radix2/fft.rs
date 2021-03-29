// The code below is a port of the excellent library of https://github.com/kwantam/fffft by Riad S. Wahby
// to the arkworks APIs

use crate::domain::utils::compute_powers_serial;
use crate::domain::{radix2::*, DomainCoeff};
use ark_ff::FftField;
use ark_std::{cfg_chunks_mut, vec::Vec};
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

    #[inline(always)]
    fn butterfly_fn_io<T: DomainCoeff<F>>(((lo, hi), root): ((&mut T, &mut T), &F)) {
        let neg = *lo - *hi;
        *lo += *hi;
        *hi = neg;
        *hi *= *root;
    }

    #[inline(always)]
    fn butterfly_fn_oi<T: DomainCoeff<F>>(((lo, hi), root): ((&mut T, &mut T), &F)) {
        *hi *= *root;
        let neg = *lo - *hi;
        *lo += *hi;
        *hi = neg;
    }

    fn io_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        // In the sequential case, we will keep on making the roots cache-aligned,
        // according to the access pattern that the FFT uses.
        let mut roots = self.roots_of_unity(root);
        let mut step = 1;
        let mut first = true;

        #[cfg(feature = "parallel")]
        let max_threads = rayon::current_num_threads();

        #[cfg(not(feature = "parallel"))]
        let max_threads = 1;

        let mut gap = xi.len() / 2;
        while gap > 0 {
            // each butterfly cluster uses 2*gap positions
            let chunk_size = 2 * gap;
            let num_chunks = xi.len() / chunk_size;

            // Only compact if the roots lookup is done a significant amount of times
            // Which also implies a large lookup stride.
            if num_chunks >= MIN_COMPACTION_CHUNKS {
                if !first {
                    roots = cfg_into_iter!(roots).step_by(step * 2).collect()
                }
                step = 1;
                roots.shrink_to_fit();
            } else {
                step = num_chunks;
            }
            first = false;

            cfg_chunks_mut!(xi, chunk_size).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                // If the chunk is sufficiently big that parallelism helps,
                // we parallelize the butterfly operation within the chunk.

                if gap > MIN_PROBLEM_SIZE && num_chunks < max_threads {
                    cfg_iter_mut!(lo)
                        .zip(cfg_iter_mut!(hi))
                        .zip(cfg_iter!(roots).step_by(step))
                        .for_each(Self::butterfly_fn_io);
                } else {
                    lo.iter_mut()
                        .zip(hi)
                        .zip(roots.iter().step_by(step))
                        .for_each(Self::butterfly_fn_io);
                }
            });

            gap /= 2;
        }
    }

    fn oi_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        let roots_cache = self.roots_of_unity(root);
        let compaction_size = core::cmp::min(
            roots_cache.len() / 2,
            roots_cache.len() / MIN_COMPACTION_CHUNKS,
        );
        let mut compacted_roots = vec![F::default(); compaction_size];

        #[cfg(feature = "parallel")]
        let max_threads = rayon::current_num_threads();

        #[cfg(not(feature = "parallel"))]
        let max_threads = 1;

        let mut gap = 1;
        while gap < xi.len() {
            // each butterfly cluster uses 2*gap positions
            let chunk_size = 2 * gap;
            let num_chunks = xi.len() / chunk_size;

            // Only compact if the roots lookup is done a significant amount of times
            // Which also implies a large lookup stride.
            let (roots, step) = if num_chunks >= MIN_COMPACTION_CHUNKS && gap < xi.len() / 2 {
                if gap > MIN_PROBLEM_SIZE {
                    cfg_iter_mut!(compacted_roots[..gap])
                        .zip(cfg_iter!(roots_cache[..gap * num_chunks]).step_by(num_chunks))
                        .for_each(|(a, b)| *a = *b);
                } else {
                    for i in 0..gap {
                        compacted_roots[i] = roots_cache[num_chunks * i];
                    }
                }
                (&compacted_roots[..gap], 1)
            } else {
                (&roots_cache[..], num_chunks)
            };

            cfg_chunks_mut!(xi, chunk_size).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                // If the chunk is sufficiently big that parallelism helps,
                // we parallelize the butterfly operation within the chunk.

                if gap > MIN_PROBLEM_SIZE && num_chunks < max_threads {
                    cfg_iter_mut!(lo)
                        .zip(cfg_iter_mut!(hi))
                        .zip(cfg_iter!(roots).step_by(step))
                        .for_each(Self::butterfly_fn_oi);
                } else {
                    lo.iter_mut()
                        .zip(hi)
                        .zip(roots.iter().step_by(step))
                        .for_each(Self::butterfly_fn_oi);
                }
            });

            gap *= 2;
        }
    }
}

const MIN_COMPACTION_CHUNKS: usize = 1 << 7;
const LOG_MIN_PROBLEM_SIZE: usize = 10;
const MIN_PROBLEM_SIZE: usize = 1 << LOG_MIN_PROBLEM_SIZE;

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

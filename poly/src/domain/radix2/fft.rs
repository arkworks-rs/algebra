// The code below is a port of the excellent library of https://github.com/kwantam/fffft by Riad S. Wahby
// to the arkworks APIs

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
        self.ifft_helper_in_place(x_s, FFTOrder::II)
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
        ark_std::cfg_iter_mut!(x_s).for_each(|val| *val *= self.size_inv);
    }

    #[cfg(not(feature = "parallel"))]
    fn roots_of_unity(&self, root: F) -> Vec<F> {
        crate::domain::utils::compute_powers_serial(self.size as usize, root)
    }

    #[cfg(feature = "parallel")]
    fn roots_of_unity(&self, root: F) -> Vec<F> {
        crate::domain::utils::compute_powers(self.size as usize, root)
    }

    fn io_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        let roots = self.roots_of_unity(root);

        let mut gap = xi.len() / 2;
        while gap > 0 {
            // each butterfly cluster uses 2*gap positions
            let chunk_size = 2 * gap;
            let nchunks = xi.len() / chunk_size;

            let butterfly_fn = |(idx, (lo, hi)): (usize, (&mut T, &mut T))| {
                let neg = *lo - *hi;
                *lo += *hi;

                *hi = neg;
                *hi *= roots[nchunks * idx];
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

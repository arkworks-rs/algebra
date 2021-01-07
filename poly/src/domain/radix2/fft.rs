use crate::domain::{radix2::*, DomainCoeff};
use ark_ff::FftField;
use ark_std::vec::Vec;

#[derive(PartialEq, Eq, Debug)]
enum FFTOrder {
    /// Both the input and the output of the FFT must be in-order.
    II,
    /// The input of the FFT must be in-order, but the output does not have to be.
    IO,
    /// The input of the FFT can be out of order, but the input must be in-order.
    OI,
}

// minimum size at which to parallelize.
#[cfg(feature = "parallel")]
const LOG_PARALLEL_SIZE: u32 = 7;

impl<F: FftField> Radix2EvaluationDomain<F> {
    pub(crate) fn in_order_fft_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T], root_of_unity: F) {
        self.fft_helper_in_place(x_s, root_of_unity, FFTOrder::II)
    }

    pub(crate) fn in_order_ifft_in_place<T: DomainCoeff<F>>(&self, x_s: &mut [T], root_of_unity: F) {
        self.ifft_helper_in_place(x_s, root_of_unity, FFTOrder::II)
    }

    fn fft_helper_in_place<T: DomainCoeff<F>>(
        &self,
        x_s: &mut [T],
        root_of_unity: F,
        ord: FFTOrder,
    ) {
        use FFTOrder::*;

        let log_len = ark_std::log2(x_s.len());

        if ord == OI {
            self.oi_helper(x_s, root_of_unity);
        } else {
            self.io_helper(x_s, root_of_unity);
        }

        if ord == II {
            derange(x_s, log_len);
        }
    }

    fn ifft_helper_in_place<T: DomainCoeff<F>>(
        &self,
        x_s: &mut [T],
        root_of_unity: F,
        ord: FFTOrder,
    ) {
        use FFTOrder::*;

        let log_len = ark_std::log2(x_s.len());

        if ord == II {
            derange(x_s, log_len);
        }

        if ord == IO {
            self.io_helper(x_s, root_of_unity);
        } else {
            self.oi_helper(x_s, root_of_unity);
        }
    }

    // #[cfg(not(feature = "parallel"))]
    fn roots_of_unity(&self, root: F) -> Vec<F> {
        let mut value = F::one();
        (0..self.size)
            .map(|_| {
                let old_value = value;
                value *= root;
                old_value
            })
            .collect()
    }

    // #[cfg(feature = "parallel")]
    // fn roots_of_unity(&self, root: F) -> Vec<F> {
    //     let log_size = self.log_size_of_group;
    //     let group_gen = self.group_gen;
    //     // early exit for short inputs
    //     if log_size <= LOG_PARALLEL_SIZE {
    //         let mut value = F::one();
    //         (0..self.size)
    //             .map(|_| {
    //                 let old_value = value;
    //                 value *= root;
    //                 old_value
    //             })
    //             .collect()
    //     } else {
    //         let mut value = group_gen;
    //         // w, w^2, w^4, w^8, ..., w^(2^(log_size - 1))
    //         let log_roots: Vec<F> = (0..(log_size - 1))
    //             .map(|_| {
    //                 let old_value = value;
    //                 value.square_in_place();
    //                 old_value
    //             })
    //             .collect();

    //         // allocate the return array and start the recursion
    //         let mut roots = vec![F::zero(); 1 << (log_size - 1)];
    //         Self::roots_of_unity_recursive(&mut roots, &log_roots);
    //         roots
    //     }
    // }

    // #[cfg(feature = "parallel")]
    // fn roots_of_unity_recursive(out: &mut [F], log_roots: &[F]) {
    //     assert_eq!(out.len(), 1 << log_roots.len());

    //     // base case: just compute the roots sequentially
    //     if log_roots.len() <= LOG_PARALLEL_SIZE as usize {
    //         out[0] = F::one();
    //         for idx in 1..out.len() {
    //             out[idx] = out[idx - 1] * log_roots[0];
    //         }
    //         return;
    //     }

    //     // recursive case:
    //     // 1. split log_roots in half
    //     let (lr_lo, lr_hi) = log_roots.split_at((1 + log_roots.len()) / 2);
    //     let mut scr_lo = vec![F::default(); 1 << lr_lo.len()];
    //     let mut scr_hi = vec![F::default(); 1 << lr_hi.len()];
    //     // 2. compute each half individually
    //     rayon::join(
    //         || Self::roots_of_unity_recursive(scr_lo.as_mut(), lr_lo),
    //         || Self::roots_of_unity_recursive(scr_hi.as_mut(), lr_hi),
    //     );
    //     // 3. recombine halves
    //     out.par_chunks_mut(scr_lo.len())
    //         .enumerate()
    //         .for_each(|(idx, rt)| {
    //             for jdx in 0..rt.len() {
    //                 rt[jdx] = scr_hi[idx] * scr_lo[jdx];
    //             }
    //         });
    // }

    fn io_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        let roots = self.roots_of_unity(root);

        let mut gap = xi.len() / 2;
        while gap > 0 {
            // each butterfly cluster uses 2*gap positions
            let nchunks = xi.len() / (2 * gap);
            ark_std::cfg_chunks_mut!(xi, 2 * gap).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                ark_std::cfg_iter_mut!(lo)
                    .zip(hi)
                    .enumerate()
                    .for_each(|(idx, (lo, hi))| {
                        let neg = *lo - *hi;
                        *lo += *hi;

                        *hi = neg;
                        *hi *= roots[nchunks * idx];
                    });
            });
            gap /= 2;
        }
    }

    fn oi_helper<T: DomainCoeff<F>>(&self, xi: &mut [T], root: F) {
        // needed roots of unity
        let roots = self.roots_of_unity(root);

        let mut gap = 1;
        while gap < xi.len() {
            let nchunks = xi.len() / (2 * gap);

            ark_std::cfg_chunks_mut!(xi, 2 * gap).for_each(|cxi| {
                let (lo, hi) = cxi.split_at_mut(gap);
                ark_std::cfg_iter_mut!(lo)
                    .zip(hi)
                    .enumerate()
                    .for_each(|(idx, (lo, hi))| {
                        *hi *= roots[nchunks * idx];
                        let neg = *lo - *hi;
                        *lo += *hi;
                        *hi = neg;
                    });
            });
            gap *= 2;
        }
    }
}

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

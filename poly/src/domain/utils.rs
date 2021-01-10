use crate::domain::DomainCoeff;
use ark_ff::{FftField, Field};
use ark_std::vec::Vec;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

// minimum size at which to parallelize.
#[cfg(feature = "parallel")]
const LOG_PARALLEL_SIZE: u32 = 7;

#[inline]
pub(crate) fn bitreverse(mut n: u32, l: u32) -> u32 {
    let mut r = 0;
    for _ in 0..l {
        r = (r << 1) | (n & 1);
        n >>= 1;
    }
    r
}

pub(crate) fn compute_powers_serial<F: Field>(size: usize, root: F) -> Vec<F> {
    let mut value = F::one();
    (0..size)
        .map(|_| {
            let old_value = value;
            value *= root;
            old_value
        })
        .collect()
}

#[cfg(feature = "parallel")]
pub(crate) fn compute_powers<F: Field>(size: usize, value: F) -> Vec<F> {
    let log_size = ark_std::log2(size);
    // early exit for short inputs
    if log_size <= LOG_PARALLEL_SIZE {
        compute_powers_serial(size, value)
    } else {
        let mut temp = value;
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
        compute_powers_recursive(&mut powers, &log_powers);
        powers
    }
}

#[cfg(feature = "parallel")]
fn compute_powers_recursive<F: Field>(out: &mut [F], log_powers: &[F]) {
    assert_eq!(out.len(), 1 << log_powers.len());
    // base case: just compute the powers sequentially,
    // g = log_powers[0], out = [1, g, g^2, ...]
    if log_powers.len() <= LOG_PARALLEL_SIZE as usize {
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
        || compute_powers_recursive(&mut scr_lo, lr_lo),
        || compute_powers_recursive(&mut scr_hi, lr_hi),
    );
    // 3. recombine halves
    out.par_chunks_mut(scr_lo.len())
        .zip(&scr_hi)
        .for_each(|(rt, scr_hi)| {
            for (rt, scr_lo) in rt.iter_mut().zip(&scr_lo) {
                *rt = *scr_hi * scr_lo;
            }
        });
}

#[cfg(feature = "parallel")]
fn log2_floor(num: usize) -> u32 {
    if num == 0 {
        0
    } else {
        1usize.leading_zeros() - num.leading_zeros()
    }
}

#[cfg(feature = "parallel")]
pub(crate) fn best_fft<T: DomainCoeff<F>, F: FftField>(
    a: &mut [T],
    omega: F,
    log_n: u32,
    serial_fft: fn(&mut [T], F, u32),
) {
    let num_cpus = rayon::current_num_threads();
    let log_cpus = log2_floor(num_cpus);
    if log_n <= log_cpus {
        serial_fft(a, omega, log_n);
    } else {
        parallel_fft(a, omega, log_n, log_cpus, serial_fft);
    }
}

#[cfg(not(feature = "parallel"))]
#[inline]
pub(crate) fn best_fft<T: DomainCoeff<F>, F: FftField>(
    a: &mut [T],
    omega: F,
    log_n: u32,
    serial_fft: fn(&mut [T], F, u32),
) {
    serial_fft(a, omega, log_n)
}

#[cfg(feature = "parallel")]
pub(crate) fn parallel_fft<T: DomainCoeff<F>, F: FftField>(
    a: &mut [T],
    omega: F,
    log_n: u32,
    log_cpus: u32,
    serial_fft: fn(&mut [T], F, u32),
) {
    assert!(log_n >= log_cpus);
    // For documentation purposes, comments explain things
    // as though `a` is a polynomial that we are trying to evaluate.

    // Partition `a` equally into the number of threads.
    // each partition is then of size m / num_threads.
    let m = a.len();
    let num_threads = 1 << (log_cpus as usize);
    let num_cosets = num_threads;
    assert_eq!(m % num_threads, 0);
    let coset_size = m / num_threads;

    // We compute the FFT non-mutatively first in tmp first,
    // and then shuffle it back into a.
    // The evaluations are going to be arranged in cosets, each of size |a| / num_threads.
    // so the first coset is (1, g^{num_cosets}, g^{2*num_cosets}, etc.)
    // the second coset is (g, g^{1 + num_cosets}, g^{1 + 2*num_cosets}, etc.)
    // These are cosets with generator g^{num_cosets}, and varying shifts.
    let mut tmp = vec![vec![T::zero(); coset_size]; num_cosets];
    let new_omega = omega.pow(&[num_cosets as u64]);
    let new_two_adicity = ark_ff::utils::k_adicity(2, coset_size);

    // For each coset, we first build a polynomial of degree |coset size|,
    // whose evaluations over coset k will agree with the evaluations of a over the coset.
    // Denote the kth such polynomial as poly_k
    tmp.par_iter_mut()
        .enumerate()
        .for_each(|(k, kth_poly_coeffs)| {
            // Shuffle into a sub-FFT
            let omega_k = omega.pow(&[k as u64]);
            let omega_step = omega.pow(&[(k * coset_size) as u64]);

            let mut elt = F::one();
            // Construct kth_poly_coeffs, which is a polynomial whose evaluations on this coset
            // should equal the evaluations of a on this coset.
            // `kth_poly_coeffs[i] = sum_{c in num_cosets} g^{k * (i + c * |coset|)} * a[i + c * |coset|]`
            // Where c represents the index of the coset being considered.
            // multiplying by g^{k*i} corresponds to the shift for just being in a different coset.
            //
            // TODO: Come back and improve the speed, and make this a more 'normal' Cooley-Tukey.
            // This appears to be an FFT of the polynomial
            // `P(x) = sum_{c in |coset|} a[i + c |coset|] * x^c`
            // onto this coset.
            // However this is being evaluated in time O(N) instead of time O(|coset|log(|coset|)).
            // If this understanding is the case, its not doing standard Cooley-Tukey.
            // At the moment, this has time complexity of at least 2*N field mul's per thread,
            // so we will be getting pretty bad parallelism.
            // Exact complexity per thread atm is `2N + (N/num threads)log(N/num threads)` field muls
            // Compare to the time complexity of serial is Nlog(N) field muls), with log(N) in [15, 25]
            for i in 0..coset_size {
                for c in 0..num_threads {
                    let idx = i + (c * coset_size);
                    // t = the value of a corresponding to the ith element of the sth coset.
                    let mut t = a[idx];
                    // elt = g^{k * idx}
                    t *= elt;
                    kth_poly_coeffs[i] += t;
                    elt *= &omega_step;
                }
                elt *= &omega_k;
            }

            // Perform sub-FFT
            // Since the sub-FFT is mutative, after this point
            // `kth_poly_coeffs` should be renamed `kth_coset_evals`
            serial_fft(kth_poly_coeffs, new_omega, new_two_adicity);
        });

    // shuffle the values computed above into a
    // The evaluations of a should be ordered as (1, g, g^2, ...)
    a.iter_mut()
        .enumerate()
        .for_each(|(i, a)| *a = tmp[i % num_cosets][i / num_cosets]);
}

/// An iterator over the elements of a domain.
pub struct Elements<F: FftField> {
    pub(crate) cur_elem: F,
    pub(crate) cur_pow: u64,
    pub(crate) size: u64,
    pub(crate) group_gen: F,
}

impl<F: FftField> Iterator for Elements<F> {
    type Item = F;
    fn next(&mut self) -> Option<F> {
        if self.cur_pow == self.size {
            None
        } else {
            let cur_elem = self.cur_elem;
            self.cur_elem *= &self.group_gen;
            self.cur_pow += 1;
            Some(cur_elem)
        }
    }
}

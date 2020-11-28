use crate::domain::DomainCoeff;
use ark_ff::FftField;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[inline]
pub(crate) fn bitreverse(mut n: u32, l: u32) -> u32 {
    let mut r = 0;
    for _ in 0..l {
        r = (r << 1) | (n & 1);
        n >>= 1;
    }
    r
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
    // each partition is then of size m_div_num_threads
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
    // whose evaluations over coset j will agree with the evaluations of a over the coset.
    // Denote the jth such polynomial as poly_j
    tmp.par_iter_mut().enumerate().for_each(|(j, jth_poly_coeffs)| {
        // Shuffle into a sub-FFT
        let omega_j = omega.pow(&[j as u64]);
        let omega_step = omega.pow(&[(j * coset_size) as u64]);

        let mut elt = F::one();
        for i in 0..coset_size {
            // Make jth_poly_coeffs[i] = 
            // `sum_{c in num_cosets} g^{j * (i + c * |coset|)} * a[i + c * |coset|]`
            // Where c represents the index of the coset being considered.
            // TODO: Include or cite a proof that this is correct.
            for c in 0..num_threads {
                let idx = i + (c * coset_size);
                // t = the value of a corresponding to the ith element of the sth coset.
                let mut t = a[idx];
                // elt = g^{j * idx}
                t *= elt;
                jth_poly_coeffs[i] += t;
                elt *= &omega_step;
            }
            elt *= &omega_j;
        }

        // Perform sub-FFT
        // Since the sub-FFt is mutative, after this point
        // `jth_poly_coeffs` should be renamed `jth_coset_evals`
        serial_fft(jth_poly_coeffs, new_omega, new_two_adicity);
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

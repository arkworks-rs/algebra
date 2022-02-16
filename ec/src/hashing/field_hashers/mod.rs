mod ietf_hasher;
pub use ietf_hasher::IETFHasher;
mod expander;
use ark_ff::{Field, PrimeField};

// This function computes the length in bytes that a hash function should output
// for hashing `count` field elements.
// See section 5.1 and 5.3 of the
// [IETF hash standardization draft](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10)
fn get_len_per_elem<F: Field, const SEC_PARAM: usize>() -> usize {
    // ceil(log(p))
    let base_field_size_in_bits = F::BasePrimeField::MODULUS_BIT_SIZE as usize;
    // ceil(log(p)) + security_parameter
    let base_field_size_with_security_padding_in_bits = base_field_size_in_bits + SEC_PARAM;
    // ceil( (ceil(log(p)) + security_parameter) / 8)
    let bytes_per_base_field_elem =
        ((base_field_size_with_security_padding_in_bits + 7) / 8) as u64;
    bytes_per_base_field_elem as usize
}

#[cfg(test)]
mod hasher_tests {
    use super::*;
    use ark_test_curves::bls12_381::{Fq, Fq2};

    #[test]
    fn test_get_len_per_elem() {
        let fq_len = get_len_per_elem::<Fq, 128>();
        let fq2_len = get_len_per_elem::<Fq2, 128>();
        assert_eq!(fq_len, fq2_len);
        assert_eq!(fq_len, 64);
    }
}

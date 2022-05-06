mod expander;
use ark_ff::{Field, PrimeField};

use crate::hashing::{
    field_hashers::expander::ExpanderXmd, map_to_curve_hasher::*, HashToCurveError,
};
use ark_std::vec::Vec;
use digest::DynDigest;
use expander::Expander;

/// This field hasher constructs a Hash-To-Field based on a fixed-output hash function,
/// like SHA2, SHA3 or Blake2.
/// The implementation aims to follow the specification in [Hashing to Elliptic Curves (draft)](https://tools.ietf.org/pdf/draft-irtf-cfrg-hash-to-curve-13.pdf).
///
/// # Examples
///
/// ```
/// use ark_test_curves::bls12_381::Fq;
/// use ark_ec::hashing::field_hashers::DefaultFieldHasher;
/// use sha2::Sha256;
/// use crate::ark_ec::hashing::map_to_curve_hasher::HashToField;
///
/// let hasher = <DefaultFieldHasher<Sha256> as HashToField<Fq>>::new(&[1, 2, 3]).unwrap();
/// let field_elements: Vec<Fq> = hasher.hash_to_field(b"Hello, World!", 2).unwrap();
///
/// assert_eq!(field_elements.len(), 2);
/// ```
pub struct DefaultFieldHasher<H: Default + DynDigest + Clone, const SEC_PARAM: usize = 128> {
    expander: ExpanderXmd<H>,
    len_per_base_elem: usize,
}

impl<F: Field, H: Default + DynDigest + Clone, const SEC_PARAM: usize> HashToField<F>
    for DefaultFieldHasher<H, SEC_PARAM>
{
    fn new(dst: &[u8]) -> Result<Self, HashToCurveError> {
        // The final output of `hash_to_field` will be an array of field
        // elements from F::BaseField, each of size `len_per_elem`.
        let len_per_base_elem = get_len_per_elem::<F, SEC_PARAM>();

        let expander = ExpanderXmd {
            hasher: H::default(),
            dst: dst.to_vec(),
            block_size: len_per_base_elem,
        };

        Ok(DefaultFieldHasher {
            expander,
            len_per_base_elem,
        })
    }

    fn hash_to_field(&self, message: &[u8], count: usize) -> Result<Vec<F>, HashToCurveError> {
        let m = F::extension_degree() as usize;

        // The user imposes a `count` of elements of F_p^m to output per input msg,
        // each field element comprising `m` BasePrimeField elements.
        let len_in_bytes = count * m * self.len_per_base_elem;
        let uniform_bytes = self.expander.expand(message, len_in_bytes);

        let mut output = Vec::with_capacity(count);
        let mut base_prime_field_elems = Vec::with_capacity(m);
        for i in 0..count {
            base_prime_field_elems.clear();
            for j in 0..m {
                let elm_offset = self.len_per_base_elem * (j + i * m);
                let val = F::BasePrimeField::from_be_bytes_mod_order(
                    &uniform_bytes[elm_offset..][..self.len_per_base_elem],
                );
                base_prime_field_elems.push(val);
            }
            let f = F::from_base_prime_field_elems(&base_prime_field_elems).unwrap();
            output.push(f);
        }

        Ok(output)
    }
}

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

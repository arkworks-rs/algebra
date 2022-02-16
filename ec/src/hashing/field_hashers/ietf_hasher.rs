use crate::hashing::*;
use crate::hashing::{field_hashers::expander::ExpanderXmd, map_to_curve_hasher::*};
use ark_ff::{Field, PrimeField};
use ark_std::vec::Vec;
use digest::DynDigest;

use super::expander::Expander;
use super::get_len_per_elem;

/// This field hasher constructs a Hash-To-Field based on a fixed-output hash function,
/// like SHA2, SHA3 or Blake2.
/// The implementation aims to follow the specification in [Hashing to Elliptic Curves (draft)](https://tools.ietf.org/pdf/draft-irtf-cfrg-hash-to-curve-13.pdf).
///
/// # Examples
///
/// ```
/// use ark_test_curves::bls12_381::Fq;
/// use ark_ec::hashing::field_hashers::IETFHasher;
/// use sha2::Sha256;
/// use crate::ark_ec::hashing::map_to_curve_hasher::HashToField;
///
/// let hasher = <IETFHasher<Sha256, 128> as HashToField<Fq>>::new_hash_to_field(&[1, 2, 3]).unwrap();
/// let field_elements: Vec<Fq> = hasher.hash_to_field(b"Hello, World!", 2).unwrap();
///
/// assert_eq!(field_elements.len(), 2);
/// ```
pub struct IETFHasher<H: Default + DynDigest + Clone, const SEC_PARAM: usize> {
    expander: ExpanderXmd<H>,
    len_per_base_elem: usize,
}

impl<F: Field, H: Default + DynDigest + Clone, const SEC_PARAM: usize> HashToField<F>
    for IETFHasher<H, SEC_PARAM>
{
    fn new_hash_to_field(dst: &[u8]) -> Result<Self, HashToCurveError> {
        // The final output of `hash_to_field` will be an array of field
        // elements from F::BaseField, each of size `len_per_elem`.
        let len_per_base_elem = get_len_per_elem::<F, SEC_PARAM>();

        let expander = ExpanderXmd {
            hasher: H::default(),
            dst: dst.to_vec(),
            block_size: len_per_base_elem,
        };

        Ok(IETFHasher {
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

        let mut output: Vec<F> = Vec::with_capacity(count);
        for i in 0..count {
            let mut base_prime_field_elems: Vec<F::BasePrimeField> = Vec::new();
            for j in 0..m {
                let elm_offset = self.len_per_base_elem * (j + i * m);
                let val: F::BasePrimeField = F::BasePrimeField::from_be_bytes_mod_order(
                    &uniform_bytes[elm_offset..elm_offset + self.len_per_base_elem],
                );
                base_prime_field_elems.push(val);
            }
            let f: F = F::from_base_prime_field_elems(&base_prime_field_elems).unwrap();
            output.push(f);
        }

        Ok(output)
    }
}

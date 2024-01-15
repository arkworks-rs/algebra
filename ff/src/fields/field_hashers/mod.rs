mod expander;

use core::marker::PhantomData;

use crate::{Field, PrimeField};

use digest::{FixedOutputReset, XofReader};
use expander::Expander;

use self::expander::ExpanderXmd;

/// Trait for hashing messages to field elements.
pub trait HashToField<F: Field>: Sized {
    /// Initialises a new hash-to-field helper struct.
    ///
    /// # Arguments
    ///
    /// * `domain` - bytes that get concatenated with the `msg` during hashing, in order to separate potentially interfering instantiations of the hasher.
    fn new(domain: &[u8]) -> Self;

    /// Hash an arbitrary `msg` to `N` elements of the field `F`.
    fn hash_to_field<const N: usize>(&self, msg: &[u8]) -> [F; N];
}

/// This field hasher constructs a Hash-To-Field based on a fixed-output hash function,
/// like SHA2, SHA3 or Blake2.
/// The implementation aims to follow the specification in [Hashing to Elliptic Curves (draft)](https://tools.ietf.org/pdf/draft-irtf-cfrg-hash-to-curve-13.pdf).
///
/// # Examples
///
/// ```
/// use ark_ff::fields::field_hashers::{DefaultFieldHasher, HashToField};
/// use ark_test_curves::bls12_381::Fq;
/// use sha2::Sha256;
///
/// let hasher = <DefaultFieldHasher<Sha256> as HashToField<Fq>>::new(&[1, 2, 3]);
/// let field_elements: [Fq; 2] = hasher.hash_to_field(b"Hello, World!");
///
/// assert_eq!(field_elements.len(), 2);
/// ```
pub struct DefaultFieldHasher<H: FixedOutputReset + Default + Clone, const SEC_PARAM: usize = 128> {
    expander: ExpanderXmd<H>,
    len_per_base_elem: usize,
}

impl<F: Field, H: FixedOutputReset + Default + Clone, const SEC_PARAM: usize> HashToField<F>
    for DefaultFieldHasher<H, SEC_PARAM>
{
    fn new(dst: &[u8]) -> Self {
        // The final output of `hash_to_field` will be an array of field
        // elements from F::BaseField, each of size `len_per_elem`.
        let len_per_base_elem = get_len_per_elem::<F, SEC_PARAM>();

        let expander = ExpanderXmd {
            hasher: PhantomData,
            dst: dst.to_vec(),
            block_size: len_per_base_elem,
        };

        DefaultFieldHasher {
            expander,
            len_per_base_elem,
        }
    }

    fn hash_to_field<const N: usize>(&self, message: &[u8]) -> [F; N] {
        let m = F::extension_degree() as usize;

        // The user requests `N` of elements of F_p^m to output per input msg,
        // each field element comprising `m` BasePrimeField elements.
        let len_in_bytes = N * m * self.len_per_base_elem;
        let uniform_bytes = self.expander.expand(message, len_in_bytes);

        let cb = |i| {
            let base_prime_field_elem = |j| {
                let elm_offset = self.len_per_base_elem * (j + i * m);
                F::BasePrimeField::from_be_bytes_mod_order(
                    &uniform_bytes[elm_offset..][..self.len_per_base_elem],
                )
            };
            F::from_base_prime_field_elems((0..m).map(base_prime_field_elem)).unwrap()
        };
        ark_std::array::from_fn::<F, N, _>(cb)
    }
}

pub fn hash_to_field<F: Field, H: XofReader, const SEC_PARAM: usize>(h: &mut H) -> F {
    // The final output of `hash_to_field` will be an array of field
    // elements from F::BaseField, each of size `len_per_elem`.
    let len_per_base_elem = get_len_per_elem::<F, SEC_PARAM>();
    // Rust *still* lacks alloca, hence this ugly hack.
    let mut alloca = [0u8; 2048];
    let alloca = &mut alloca[0..len_per_base_elem];

    let m = F::extension_degree() as usize;

    let base_prime_field_elem = |_| {
        h.read(alloca);
        F::BasePrimeField::from_be_bytes_mod_order(alloca)
    };
    F::from_base_prime_field_elems((0..m).map(base_prime_field_elem)).unwrap()
}

/// This function computes the length in bytes that a hash function should output
/// for hashing an element of type `Field`.
/// See section 5.1 and 5.3 of the
/// [IETF hash standardization draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/14/)
const fn get_len_per_elem<F: Field, const SEC_PARAM: usize>() -> usize {
    // ceil(log(p))
    let base_field_size_in_bits = F::BasePrimeField::MODULUS_BIT_SIZE as usize;
    // ceil(log(p)) + security_parameter
    let base_field_size_with_security_padding_in_bits = base_field_size_in_bits + SEC_PARAM;
    // ceil( (ceil(log(p)) + security_parameter) / 8)
    let bytes_per_base_field_elem =
        ((base_field_size_with_security_padding_in_bits + 7) / 8) as u64;
    bytes_per_base_field_elem as usize
}

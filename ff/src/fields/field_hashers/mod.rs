mod expander;

use crate::{Field, PrimeField};

use ark_std::vec::Vec;
pub use digest::{self,Update};
use digest::{ExtendableOutput,FixedOutputReset,XofReader};
pub use expander::{DST, Zpad, Expander};


// pub trait HashToField: Field {
//     fn hash_to_field() -> Self;
// }

/* 
/// Trait for hashing messages to field elements.
pub trait HashToField<F: Field>: Sized {
    /// Initialises a new hash-to-field helper struct.
    ///
    /// # Arguments
    ///
    /// * `domain` - bytes that get concatenated with the `msg` during hashing, in order to separate potentially interfering instantiations of the hasher.
    fn new(domain: &[u8]) -> Self;

    /// Hash an arbitrary `msg` to #`count` elements from field `F`.
    fn hash_to_field<const N: usize>(&self, msg: &[u8]) -> [F; N];
}
*/

/// This field hasher constructs a Hash-To-Field based on a fixed-output hash function,
/// like SHA2, SHA3 or Blake2.
/// The implementation aims to follow the specification in [Hashing to Elliptic Curves (draft)](https://tools.ietf.org/pdf/draft-irtf-cfrg-hash-to-curve-13.pdf).
///
/// # Examples
///
/// ```
/// use ark_ff::fields::field_hashers::{xmd_hash_to_field};
/// use ark_test_curves::bls12_381::Fq;
/// use sha2::Sha256;
///
/// let field_elements: [Fq; 2] = xmd_hash_to_field::<Sha256,128,Fq,2>(b"Application",b"Hello, World!");
///
/// assert_eq!(field_elements.len(), 2);
/// ```
pub fn xmd_hash_to_field<H,const SEC_PARAM: u16,F,const N: usize>(dst: &[u8], msg: &[u8]) -> [F; N]
where F: Field, H: FixedOutputReset+Default,
{
    let dst = DST::new_xmd::<H>(dst);
    let mut xmd = Zpad::<H>::new_for_field::<SEC_PARAM,F>().chain(msg).expand_for_field::<SEC_PARAM,F,2>(&dst);
    let h2f = |_| hash_to_field::<SEC_PARAM,F,_>(&mut xmd);
    ark_std::array::from_fn::<F,N,_>(h2f)
}

pub fn xof_hash_to_field<H,const SEC_PARAM: u16,F,const N: usize>(dst: &[u8], msg: &[u8]) -> [F; N]
where F: Field, H: ExtendableOutput+Default,
{
    let dst = DST::new_xof::<H>(dst,Some(SEC_PARAM));
    let mut xof = H::default().chain(msg).expand_for_field::<SEC_PARAM,F,2>(&dst);
    let h2f = |_| hash_to_field::<SEC_PARAM,F,_>(&mut xof);
    ark_std::array::from_fn::<F,N,_>(h2f)
}

pub fn hash_to_field<const SEC_PARAM: u16,F: Field,H: XofReader>(h: &mut H) -> F {
    // The final output of `hash_to_field` will be an array of field
    // elements from F::BaseField, each of size `len_per_elem`.
    let len_per_base_elem = get_len_per_elem::<F, SEC_PARAM>();
    // Rust *still* lacks alloca, hence this ugly hack.
    let mut alloca = [0u8; 256];
    let mut vec = Vec::new();
    let bytes = if len_per_base_elem > 256 {
        vec.resize(len_per_base_elem, 0u8);
        vec.as_mut()
    } else {
        &mut alloca[0..len_per_base_elem]
    };

    let m = F::extension_degree() as usize;

    let base_prime_field_elem = |_| {
        h.read(&mut *bytes);
        bytes.reverse();  // Need BE but Arkworks' LE is faster 
        F::BasePrimeField::from_le_bytes_mod_order(&mut *bytes)
    };
    F::from_base_prime_field_elems( (0..m).map(base_prime_field_elem) ).unwrap()
}

/// This function computes the length in bytes that a hash function should output
/// for hashing an element of type `Field`.
/// See section 5.1 and 5.3 of the
/// [IETF hash standardization draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/14/)
const fn get_len_per_elem<F: Field, const SEC_PARAM: u16>() -> usize {
    // ceil(log(p))
    let base_field_size_in_bits = F::BasePrimeField::MODULUS_BIT_SIZE as usize;
    // ceil(log(p)) + security_parameter
    let base_field_size_with_security_padding_in_bits = base_field_size_in_bits + (SEC_PARAM as usize);
    // ceil( (ceil(log(p)) + security_parameter) / 8)
    let bytes_per_base_field_elem =
        ((base_field_size_with_security_padding_in_bits + 7) / 8) as u64;
    bytes_per_base_field_elem as usize
}

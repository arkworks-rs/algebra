use ark_ff::{Field, PrimeField};
use ark_std::vec::Vec;

use crate::hashing::{map_to_curve_hasher::*, *};
use ark_std::string::ToString;
use digest::{Update, VariableOutput};

// This function computes the length in bytes that a hash function should output
// for hashing `count` field elements.
// See section 5.1 and 5.3 of the
// [IETF hash standardization draft](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10)
fn hash_len_in_bytes<F: Field, const SEC_PARAM: usize>(count: usize) -> usize {
    // ceil(log(p))
    let base_field_size_in_bits = F::BasePrimeField::MODULUS_BIT_SIZE as usize;
    // ceil(log(p)) + security_parameter
    let base_field_size_with_security_padding_in_bits = base_field_size_in_bits + SEC_PARAM;
    // ceil( (ceil(log(p)) + security_parameter) / 8)
    let bytes_per_base_field_elem =
        ((base_field_size_with_security_padding_in_bits + 7) / 8) as u64;
    let len_in_bytes = F::extension_degree() * (count as u64) * bytes_per_base_field_elem;
    len_in_bytes as usize
}

fn map_bytes_to_field_elem<F: Field>(bz: &[u8]) -> Option<F> {
    let d: usize = F::extension_degree() as usize;
    let len_per_elem = bz.len() / d;
    let mut base_field_elems = Vec::new();
    for i in 0..d {
        let val =
            F::BasePrimeField::from_be_bytes_mod_order(&bz[(i * len_per_elem)..][..len_per_elem]);
        base_field_elems.push(val);
    }
    F::from_base_prime_field_elems(&base_field_elems)
}

// This field hasher constructs a Hash to Field from a variable output hash
// function. It handles domains by hashing the input domain into 256 bits, and
// prefixes these bits to every message it computes the hash of.
// The state after prefixing the domain is cached.
pub struct DefaultFieldHasher<H: VariableOutput + Update + Sized + Clone, const SEC_PARAM: usize> {
    // This hasher should already have the domain applied to it.
    domain_seperated_hasher: H,
    count: usize,
}

// Implement HashToField from F and a variable output hash
impl<F: Field, H: VariableOutput + Update + Sized + Clone, const SEC_PARAM: usize> HashToField<F>
    for DefaultFieldHasher<H, SEC_PARAM>
{
    fn new_hash_to_field(domain: &[u8], count: usize) -> Result<Self, HashToCurveError> {
        // Hardcode security parameter
        let bytes_per_base_field_elem = hash_len_in_bytes::<F, SEC_PARAM>(count);
        // Create hasher and map the error type
        let wrapped_hasher = H::new(bytes_per_base_field_elem);
        let mut hasher = match wrapped_hasher {
            Ok(hasher) => hasher,
            Err(err) => return Err(HashToCurveError::DomainError(err.to_string())),
        };

        // DefaultFieldHasher handles domains by hashing them into 256 bits / 32 bytes
        // using the same hasher. The hashed domain is then prefixed to all
        // messages that get hashed.
        let hashed_domain_length_in_bytes = 32;
        let mut hashed_domain = [0u8; 32];
        // Create hasher and map the error type
        let wrapped_domain_hasher = H::new(hashed_domain_length_in_bytes);
        let mut domain_hasher = match wrapped_domain_hasher {
            Ok(hasher) => hasher,
            Err(err) => return Err(HashToCurveError::DomainError(err.to_string())),
        };

        domain_hasher.update(domain);
        match domain_hasher.finalize_variable(&mut hashed_domain) {
            Err(err) => return Err(HashToCurveError::DomainError(err.to_string())),
            _ => (),
        }

        // Prefix the 32 byte hashed domain to our hasher
        hasher.update(&hashed_domain);
        Ok(DefaultFieldHasher {
            domain_seperated_hasher: hasher,
            count,
        })
    }

    fn hash_to_field(&self, msg: &[u8]) -> Result<Vec<F>, HashToCurveError> {
        // Clone the hasher, and hash our message
        let mut cur_hasher = self.domain_seperated_hasher.clone();
        cur_hasher.update(msg);
        let mut hashed_bytes = vec![0u8; cur_hasher.output_size()];
        match cur_hasher.finalize_variable(&mut hashed_bytes) {
            Err(err) => return Err(HashToCurveError::DomainError(err.to_string())),
            _ => (),
        }
        // Now separate the hashed bytes according to each field element.
        let mut result = Vec::with_capacity(self.count);
        let len_per_elem = hashed_bytes.len() / self.count;
        for i in 0..self.count {
            let bz_per_elem = &hashed_bytes[i * len_per_elem..][..len_per_elem];
            let val = map_bytes_to_field_elem::<F>(bz_per_elem).unwrap();
            result.push(val);
        }

        Ok(result)
    }
}

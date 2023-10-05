use ark_ff::{BigInteger, Field, PrimeField, Zero};
pub mod elligator2;
pub mod swu;
pub mod wb;

//// parity method on the Field elements based on [\[1\]] Section 4.1
//// which is used by multiple curve maps including Elligator2 and SWU
/// - [\[1\]] <https://datatracker.ietf.org/doc/html/rfc9380/>
pub fn parity<F: Field>(element: &F) -> bool {
    element
        .to_base_prime_field_elements()
        .find(|&x| !x.is_zero())
        .map_or(false, |x| x.into_bigint().is_odd())
}

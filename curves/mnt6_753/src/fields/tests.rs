use crate::*;
use ark_algebra_test_templates::*;
use ark_ff::fields::{models::fp6_2over3::*, quadratic_extension::QuadExtConfig};
use ark_std::{rand::Rng, test_rng};

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_field!(fq3; Fq3);
test_field!(fq6; Fq6);

#[test]
fn test_fq3_more() {
    let mut rng = test_rng();
    let mut a: Fq3 = rng.gen();
    assert_eq!(
        a * Fq6Config::NONRESIDUE,
        *<Fp6ConfigWrapper<Fq6Config>>::mul_base_field_by_nonresidue_in_place(&mut a)
    );
}

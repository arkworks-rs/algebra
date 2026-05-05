#[cfg(feature = "mnt4_753_base_field")]
use crate::mnt4_753::Fq;
#[cfg(feature = "mnt4_753_scalar_field")]
use crate::mnt4_753::Fr;
#[cfg(feature = "mnt4_753_curve")]
use crate::mnt4_753::G1Projective;
use ark_algebra_test_templates::test_field;
#[cfg(feature = "mnt4_753_curve")]
use ark_ec_test_templates::test_group;

#[cfg(feature = "mnt4_753_base_field")]
test_field!(fq; Fq; mont_prime_field);
#[cfg(feature = "mnt4_753_scalar_field")]
test_field!(fr; Fr; mont_prime_field);
#[cfg(feature = "mnt4_753_curve")]
test_group!(g1; G1Projective);

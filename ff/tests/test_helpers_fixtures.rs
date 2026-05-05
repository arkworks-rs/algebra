//! Property-based tests that exercise the field fixtures under
//! `ark_ff::test_helpers`. Kept as an integration test (outside `ff/src/`) so
//! `ark_algebra_test_templates::test_field!` / `test_small_field!` expand in
//! an external-crate context — this avoids the self-referential trait bound
//! resolution that blocks embedding them directly inside fixture files.
#![cfg(feature = "test_helpers")]

use ark_algebra_test_templates::*;
use ark_ff::test_helpers::{
    bls12_381::{
        Fq as Bls12_381Fq, Fq12 as Bls12_381Fq12, Fq2 as Bls12_381Fq2, Fq6 as Bls12_381Fq6,
        Fr as Bls12_381Fr,
    },
    bn384_small_two_adicity::{Fq as Bn384Fq, Fr as Bn384Fr},
    ed_on_bls12_381::{Fq as EdOnBls12_381Fq, Fr as EdOnBls12_381Fr},
    fp128::Fq as Fp128Fq,
    mnt4_753::{Fq as Mnt4Fq, Fr as Mnt4Fr},
    mnt6_753::{Fq as Mnt6Fq, Fq3 as Mnt6Fq3, Fr as Mnt6Fr},
    secp256k1::{Fq as Secp256k1Fq, Fr as Secp256k1Fr},
    smallfp::{
        SmallFp16, SmallFp16M13, SmallFp32Babybear, SmallFp32Koalabear, SmallFp32M31,
        SmallFp64Goldilock, SmallFp8,
    },
};

test_field!(fp128_fq; Fp128Fq; mont_prime_field);

test_field!(bls12_381_fr; Bls12_381Fr; mont_prime_field);
test_field!(bls12_381_fq; Bls12_381Fq; mont_prime_field);
test_field!(bls12_381_fq2; Bls12_381Fq2);
test_field!(bls12_381_fq6; Bls12_381Fq6);
test_field!(bls12_381_fq12; Bls12_381Fq12);

test_field!(mnt4_fq; Mnt4Fq; mont_prime_field);
test_field!(mnt4_fr; Mnt4Fr; mont_prime_field);
test_field!(mnt6_fq; Mnt6Fq; mont_prime_field);
test_field!(mnt6_fr; Mnt6Fr; mont_prime_field);
test_field!(mnt6_fq3; Mnt6Fq3);

test_field!(bn384_fq; Bn384Fq; mont_prime_field);
test_field!(bn384_fr; Bn384Fr; mont_prime_field);

test_field!(ed_on_bls12_381_fq; EdOnBls12_381Fq; mont_prime_field);
test_field!(ed_on_bls12_381_fr; EdOnBls12_381Fr; mont_prime_field);

test_field!(secp256k1_fq; Secp256k1Fq; mont_prime_field);
test_field!(secp256k1_fr; Secp256k1Fr; mont_prime_field);

test_small_field!(smallfp_f8; SmallFp8);
test_small_field!(smallfp_f16; SmallFp16);
test_small_field!(smallfp_f16_mont_m13; SmallFp16M13);
test_small_field!(smallfp_f32_m31; SmallFp32M31);
test_small_field!(smallfp_f32_babybear; SmallFp32Babybear);
test_small_field!(smallfp_f32_koalabear; SmallFp32Koalabear);
test_small_field!(smallfp_f64_goldilock; SmallFp64Goldilock);

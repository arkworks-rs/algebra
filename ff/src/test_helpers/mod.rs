//! Concrete field fixtures used by `ark-ff`'s own tests, doctests, and
//! downstream test-only consumers (e.g. `ark-test-curves`).
//!
//! Gated behind the `test_helpers` feature. Not part of the public stable API —
//! production code should depend on `ark-bls12-381` / `ark-mnt6-753` / etc.
//! instead of importing from here.
//!
//! The `bls12_381`, `mnt4_753`, etc. submodules contain pure field definitions
//! (base / scalar / extension fields) named after the curves that those fields
//! support; no `ark-ec` dependency.

pub mod fp128;
pub mod smallfp;

pub mod bls12_381;
pub mod bn384_small_two_adicity;
pub mod ed_on_bls12_381;
pub mod mnt4_753;
pub mod mnt6_753;
pub mod secp256k1;

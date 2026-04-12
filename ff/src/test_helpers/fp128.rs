//! Prime field `Fp` where `p = 2^127 - 1`.
use crate::fields::{Fp128, MontBackend};

#[derive(ark_ff::MontConfig)]
#[modulus = "170141183460469231731687303715884105727"]
#[generator = "43"]
pub struct FqConfig;
pub type Fq = Fp128<MontBackend<FqConfig, 2>>;

// NOTE: the property-based `test_field!` invocations for this fixture live in
// `ff/tests/test_helpers_fixtures.rs`. They can't sit here because
// `test_field!` expands to `ark_ff::Field` bounds which don't resolve cleanly
// when the macro expansion happens inside ark-ff itself (the crate can't bound
// its own types by its own re-exported trait during macro expansion).

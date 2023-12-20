use ark_r1cs_std::fields::{fp::FpVar, fp3::Fp3Var, fp6_2over3::Fp6Var};

use crate::{Fq, Fq3Config, Fq6Config};

/// A variable that is the R1CS equivalent of `crate::Fq`.
pub type FqVar = FpVar<Fq>;
/// A variable that is the R1CS equivalent of `crate::Fq3`.
pub type Fq3Var = Fp3Var<Fq3Config>;
/// A variable that is the R1CS equivalent of `crate::Fq6`.
pub type Fq6Var = Fp6Var<Fq6Config>;

#[test]
fn mnt6_298_field_gadgets_test() {
    use super::*;
    use crate::{Fq, Fq3, Fq6};
    use ark_curve_constraint_tests::fields::*;

    field_test::<_, _, FqVar>().unwrap();
    frobenius_tests::<Fq, _, FqVar>(13).unwrap();

    field_test::<_, _, Fq3Var>().unwrap();
    frobenius_tests::<Fq3, _, Fq3Var>(13).unwrap();

    field_test::<_, _, Fq6Var>().unwrap();
    frobenius_tests::<Fq6, _, Fq6Var>(13).unwrap();
}

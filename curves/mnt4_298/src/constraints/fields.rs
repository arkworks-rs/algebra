use ark_r1cs_std::fields::{fp::FpVar, fp2::Fp2Var, fp4::Fp4Var};

use crate::{Fq, Fq2Config, Fq4Config};

/// A variable that is the R1CS equivalent of `crate::Fq`.
pub type FqVar = FpVar<Fq>;
/// A variable that is the R1CS equivalent of `crate::Fq2`.
pub type Fq2Var = Fp2Var<Fq2Config>;
/// A variable that is the R1CS equivalent of `crate::Fq4`.
pub type Fq4Var = Fp4Var<Fq4Config>;

#[test]
fn mnt4_298_field_gadgets_test() {
    use super::*;
    use crate::{Fq, Fq2, Fq4};
    use ark_curve_constraint_tests::fields::*;

    field_test::<_, _, FqVar>().unwrap();
    frobenius_tests::<Fq, _, FqVar>(13).unwrap();

    field_test::<_, _, Fq2Var>().unwrap();
    frobenius_tests::<Fq2, _, Fq2Var>(13).unwrap();

    field_test::<_, _, Fq4Var>().unwrap();
    frobenius_tests::<Fq4, _, Fq4Var>(13).unwrap();
}

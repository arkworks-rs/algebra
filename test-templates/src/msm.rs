use ark_ec::{msm::VariableBaseMSM, CurveGroup, GroupUniqueRepr};
use ark_ff::{PrimeField, UniformRand};
use pretty_assertions::assert_eq;

fn naive_var_base_msm<G: CurveGroup>(
    bases: &[G::UniqueRepr],
    scalars: &[<G::ScalarField as PrimeField>::BigInt],
) -> G::UniqueRepr {
    let mut acc = G::zero();

    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        acc += base.mul(*scalar);
    }
    acc.into()
}

pub fn test_var_base_msm<G: CurveGroup>() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let v = (0..SAMPLES - 1)
        .map(|_| G::ScalarField::rand(&mut rng).into_repr())
        .collect::<Vec<_>>();
    let g = (0..SAMPLES)
        .map(|_| G::UniqueRepr::rand(&mut rng))
        .collect::<Vec<_>>();

    let naive: G::UniqueRepr = naive_var_base_msm::<G>(g.as_slice(), v.as_slice());
    let fast: G = VariableBaseMSM::multi_scalar_mul(g.as_slice(), v.as_slice());

    assert_eq!(naive, fast.into());
}
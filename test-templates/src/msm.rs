use ark_ec::{
    msm::{ChunkedPippenger, HashMapPippenger, VariableBaseMSM},
    AffineCurve, ProjectiveCurve,
};
use ark_ff::{PrimeField, UniformRand, Zero};

fn naive_var_base_msm<G: AffineCurve>(bases: &[G], scalars: &[G::ScalarField]) -> G::Projective {
    let mut acc = G::Projective::zero();

    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        acc += &base.mul(scalar.into_bigint());
    }
    acc
}

pub fn test_var_base_msm<G>()
where
    G: AffineCurve,
    G::Projective: VariableBaseMSM<MSMBase = G, Scalar = G::ScalarField>,
{
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let v = (0..SAMPLES)
        .map(|_| G::ScalarField::rand(&mut rng))
        .collect::<Vec<_>>();
    let g = (0..SAMPLES)
        .map(|_| G::Projective::rand(&mut rng))
        .collect::<Vec<_>>();
    let g = <G::Projective as ProjectiveCurve>::batch_normalization_into_affine(&g);

    let naive = naive_var_base_msm(g.as_slice(), v.as_slice());
    let fast = <G::Projective as VariableBaseMSM>::msm(g.as_slice(), v.as_slice());

    // assert!(ark_std::panic::catch_unwind(||  <G::Projective as VariableBaseMSM>::msm(&g[.. SAMPLES], &v[.. SAMPLES-1])).is_err());
    assert_eq!(naive.into_affine(), fast.into_affine());
}

pub fn test_chunked_pippenger<G>()
where
    G: AffineCurve,
    G::Projective: VariableBaseMSM<MSMBase = G, Scalar = G::ScalarField>,
{
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let v = (0..SAMPLES)
        .map(|_| G::ScalarField::rand(&mut rng).into_bigint())
        .collect::<Vec<_>>();
    let g = (0..SAMPLES)
        .map(|_| G::Projective::rand(&mut rng))
        .collect::<Vec<_>>();
    let g = <G::Projective as ProjectiveCurve>::batch_normalization_into_affine(&g);

    let arkworks = <G::Projective as VariableBaseMSM>::msm_bigint(g.as_slice(), v.as_slice());

    let mut p = ChunkedPippenger::<G>::new(1 << 20);
    for (s, g) in v.iter().zip(g) {
        p.add(g, s);
    }
    let mine = p.finalize();
    assert_eq!(arkworks.into_affine(), mine.into_affine());
}

pub fn test_hashmap_pippenger<G>()
where
    G: AffineCurve,
    G::Projective: VariableBaseMSM<MSMBase = G, Scalar = G::ScalarField>,
{
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let mut v_scal = Vec::new();
    let v = (0..SAMPLES)
        .map(|_| {
            let x = G::ScalarField::rand(&mut rng);
            v_scal.push(x);
            x.into_bigint()
        })
        .collect::<Vec<_>>();
    let g = (0..SAMPLES)
        .map(|_| G::Projective::rand(&mut rng))
        .collect::<Vec<_>>();
    let g = <G::Projective as ProjectiveCurve>::batch_normalization_into_affine(&g);

    let arkworks = <G::Projective as VariableBaseMSM>::msm_bigint(g.as_slice(), v.as_slice());

    let mut p = HashMapPippenger::<G>::new(1 << 20);
    for (s, g) in v_scal.iter().zip(g) {
        p.add(g, s);
    }
    let mine = p.finalize();
    assert_eq!(arkworks.into_affine(), mine.into_affine());
}

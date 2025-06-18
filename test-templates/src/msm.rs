use ark_ec::{
    scalar_mul::variable_base::{ChunkedPippenger, HashMapPippenger, VariableBaseMSM},
    ScalarMul,
};
use ark_ff::{PrimeField, UniformRand};
use ark_std::{rand::seq::SliceRandom, vec::*};

fn naive_var_base_msm<G: ScalarMul>(bases: &[G::MulBase], scalars: &[G::ScalarField]) -> G {
    let mut acc = G::zero();

    for (base, scalar) in bases.iter().zip(scalars.iter()) {
        acc += *base * scalar;
    }
    acc
}

pub fn test_var_base_msm<G: VariableBaseMSM>() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let v = (0..SAMPLES)
        .map(|_| G::ScalarField::rand(&mut rng))
        .collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();
    let g = G::batch_convert_to_mul_base(&g);

    let naive = naive_var_base_msm::<G>(g.as_slice(), v.as_slice());
    let fast = G::msm(g.as_slice(), v.as_slice()).unwrap();

    assert_eq!(naive, fast);
}

type F<G> = <G as ark_ec::PrimeGroup>::ScalarField;

pub fn test_var_base_msm_mixed_scalars<G: VariableBaseMSM>() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();
    let mut v = Vec::<F<G>>::with_capacity(SAMPLES * 11);
    // Positive and negative u1s
    v.extend((0..SAMPLES).map(|_| F::<G>::from(bool::rand(&mut rng))));
    v.extend((0..SAMPLES).map(|_| -F::<G>::from(bool::rand(&mut rng))));

    // Positive and negative u8s
    v.extend((0..SAMPLES).map(|_| F::<G>::from(u8::rand(&mut rng))));
    v.extend((0..SAMPLES).map(|_| -F::<G>::from(u8::rand(&mut rng))));

    // Positive and negative u16s
    v.extend((0..SAMPLES).map(|_| F::<G>::from(u16::rand(&mut rng))));
    v.extend((0..SAMPLES).map(|_| -F::<G>::from(u16::rand(&mut rng))));

    // Positive and negative u32s
    v.extend((0..SAMPLES).map(|_| F::<G>::from(u32::rand(&mut rng))));
    v.extend((0..SAMPLES).map(|_| -F::<G>::from(u32::rand(&mut rng))));

    // Positive and negative u64s
    v.extend((0..SAMPLES).map(|_| F::<G>::from(u64::rand(&mut rng))));
    v.extend((0..SAMPLES).map(|_| -F::<G>::from(u64::rand(&mut rng))));

    // Random scalars
    v.extend((0..SAMPLES).map(|_| F::<G>::from(G::ScalarField::rand(&mut rng))));
    v.shuffle(&mut rng);

    let g = (0..v.len()).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();
    let g = G::batch_convert_to_mul_base(&g);

    let naive = naive_var_base_msm::<G>(g.as_slice(), v.as_slice());
    let fast = G::msm(g.as_slice(), v.as_slice()).unwrap();

    assert_eq!(naive, fast);
}

pub fn test_var_base_msm_specialized<G: VariableBaseMSM>() {
    const SAMPLES: usize = (1 << 10) * 5;

    let rng = &mut ark_std::test_rng();
    let g = (0..SAMPLES).map(|_| G::rand(rng)).collect::<Vec<_>>();
    let g = G::batch_convert_to_mul_base(&g);

    let v = (0..SAMPLES).map(|_| bool::rand(rng)).collect::<Vec<_>>();
    let v_fe = v.iter().map(|&b| F::<G>::from(b)).collect::<Vec<_>>();
    let naive = naive_var_base_msm::<G>(g.as_slice(), v_fe.as_slice());
    let fast = G::msm_u1(g.as_slice(), v.as_slice());
    assert_eq!(naive, fast);

    let v = (0..SAMPLES).map(|_| u8::rand(rng)).collect::<Vec<_>>();
    let v_fe = v.iter().map(|&b| F::<G>::from(b)).collect::<Vec<_>>();
    let naive = naive_var_base_msm::<G>(g.as_slice(), v_fe.as_slice());
    let fast = G::msm_u8(g.as_slice(), v.as_slice());
    assert_eq!(naive, fast);

    let v = (0..SAMPLES).map(|_| u16::rand(rng)).collect::<Vec<_>>();
    let v_fe = v.iter().map(|&b| F::<G>::from(b)).collect::<Vec<_>>();
    let naive = naive_var_base_msm::<G>(g.as_slice(), v_fe.as_slice());
    let fast = G::msm_u16(g.as_slice(), v.as_slice());
    assert_eq!(naive, fast);

    let v = (0..SAMPLES).map(|_| u32::rand(rng)).collect::<Vec<_>>();
    let v_fe = v.iter().map(|&b| F::<G>::from(b)).collect::<Vec<_>>();
    let naive = naive_var_base_msm::<G>(g.as_slice(), v_fe.as_slice());
    let fast = G::msm_u32(g.as_slice(), v.as_slice());
    assert_eq!(naive, fast);

    let v = (0..SAMPLES).map(|_| u64::rand(rng)).collect::<Vec<_>>();
    let v_fe = v.iter().map(|&b| F::<G>::from(b)).collect::<Vec<_>>();
    let naive = naive_var_base_msm::<G>(g.as_slice(), v_fe.as_slice());
    let fast = G::msm_u64(g.as_slice(), v.as_slice());
    assert_eq!(naive, fast);
}

pub fn test_chunked_pippenger<G: VariableBaseMSM>() {
    const SAMPLES: usize = 1 << 10;

    let mut rng = ark_std::test_rng();

    let v = (0..SAMPLES)
        .map(|_| G::ScalarField::rand(&mut rng).into_bigint())
        .collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();
    let g = G::batch_convert_to_mul_base(&g);

    let arkworks = G::msm_bigint(g.as_slice(), v.as_slice());

    let mut p = ChunkedPippenger::<G>::new(1 << 20);
    for (s, g) in v.iter().zip(g) {
        p.add(g, s);
    }
    let mine = p.finalize();
    assert_eq!(arkworks, mine);
}

pub fn test_hashmap_pippenger<G: VariableBaseMSM>() {
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
    let g = (0..SAMPLES).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();
    let g = G::batch_convert_to_mul_base(&g);

    let arkworks = G::msm_bigint(g.as_slice(), v.as_slice());

    let mut p = HashMapPippenger::<G>::new(1 << 20);
    for (s, g) in v_scal.iter().zip(g) {
        p.add(g, s);
    }
    let mine = p.finalize();
    assert_eq!(arkworks, mine);
}

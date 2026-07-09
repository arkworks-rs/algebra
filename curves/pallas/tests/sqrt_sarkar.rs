use ark_ff::{Field, LegendreSymbol};
use ark_std::test_rng;

fn check<F: Field>() {
    assert!(F::SQRT_PRECOMP.is_some());

    let rng = &mut test_rng();

    assert_eq!(F::ZERO.sqrt(), Some(F::ZERO));
    let one = F::ONE;
    assert_eq!(one.sqrt().map(|r| r * r), Some(one));

    let mut squares = 0u32;
    let mut nonsquares = 0u32;
    for _ in 0..3000 {
        let x = F::rand(rng);
        match x.legendre() {
            LegendreSymbol::Zero => {},
            LegendreSymbol::QuadraticResidue => {
                squares += 1;
                let r = x
                    .sqrt()
                    .expect("a quadratic residue must have a square root");
                assert_eq!(r * r, x, "returned root does not square back to input");
            },
            LegendreSymbol::QuadraticNonResidue => {
                nonsquares += 1;
                assert!(
                    x.sqrt().is_none(),
                    "a quadratic non-residue must not yield a square root"
                );
            },
        }
    }
    // Sanity that we actually exercised both branches.
    assert!(squares > 0 && nonsquares > 0);
}

#[test]
fn pallas_fq_p_field() {
    check::<ark_pallas::Fq>();
}

#[test]
fn pallas_fr_q_field() {
    check::<ark_pallas::Fr>();
}

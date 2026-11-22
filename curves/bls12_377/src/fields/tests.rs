use ark_algebra_test_templates::*;
use ark_ff::{
    biginteger::{BigInt, BigInteger, BigInteger384},
    fields::{FftField, Field, Fp6Config, PrimeField},
    Fp384, One, UniformRand, Zero,
};
use ark_std::{cmp::Ordering, ops::MulAssign, test_rng};

use crate::{Fq, Fq12, Fq2, Fq6, Fq6Config, Fr};

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_field!(fq2; Fq2);
test_field!(fq6; Fq6);
test_field!(fq12; Fq12);

#[test]
fn test_fq_repr_from() {
    assert_eq!(BigInt::from(100u64), BigInt::new([100, 0, 0, 0, 0, 0]));
}

#[test]
fn test_fq_repr_is_odd() {
    assert!(!BigInteger384::from(0u64).is_odd());
    assert!(BigInteger384::from(0u64).is_even());
    assert!(BigInteger384::from(1u64).is_odd());
    assert!(!BigInteger384::from(1u64).is_even());
    assert!(!BigInteger384::from(324834872u64).is_odd());
    assert!(BigInteger384::from(324834872u64).is_even());
    assert!(BigInteger384::from(324834873u64).is_odd());
    assert!(!BigInteger384::from(324834873u64).is_even());
}

#[test]
fn test_fq_repr_is_zero() {
    assert!(BigInteger384::from(0u64).is_zero());
    assert!(!BigInteger384::from(1u64).is_zero());
    assert!(!BigInt::new([0, 0, 0, 0, 1, 0]).is_zero());
}

#[test]
fn test_fq_repr_num_bits() {
    let mut a = BigInteger384::from(0u64);
    assert_eq!(0, a.num_bits());
    a = BigInteger384::from(1u64);
    for i in 1..385 {
        assert_eq!(i, a.num_bits());
        a.mul2();
    }
    assert_eq!(0, a.num_bits());
}

#[test]
fn test_fq_num_bits() {
    assert_eq!(Fq::MODULUS_BIT_SIZE, 377);
}

#[test]
fn test_fq_root_of_unity() {
    assert_eq!(Fq::TWO_ADICITY, 46);
    assert_eq!(
        Fq::GENERATOR.pow([
            0x7510c00000021423,
            0x88bee82520005c2d,
            0x67cc03d44e3c7bcd,
            0x1701b28524ec688b,
            0xe9185f1443ab18ec,
            0x6b8
        ]),
        Fq::TWO_ADIC_ROOT_OF_UNITY
    );
    assert_eq!(
        Fq::TWO_ADIC_ROOT_OF_UNITY.pow([1 << Fq::TWO_ADICITY]),
        Fq::one()
    );
    assert!(Fq::GENERATOR.sqrt().is_none());
}

#[test]
fn test_fq_ordering() {
    // BigInteger384's ordering is well-tested, but we still need to make sure the
    // Fq elements aren't being compared in Montgomery form.
    for i in 0..100u64 {
        assert!(Fq::from(Fp384::from(i + 1)) > Fq::from(Fp384::from(i)));
    }
}

#[test]
fn test_fq_legendre() {
    use ark_ff::fields::LegendreSymbol::*;

    assert_eq!(QuadraticResidue, Fq::one().legendre());
    assert_eq!(Zero, Fq::zero().legendre());
    assert_eq!(QuadraticResidue, Fq::from(Fp384::from(4u64)).legendre());
    assert_eq!(QuadraticNonResidue, Fq::from(Fp384::from(5u64)).legendre());
}

#[test]
fn test_fq2_ordering() {
    let mut a = Fq2::new(Fq::zero(), Fq::zero());
    let mut b = a.clone();

    assert!(a.cmp(&b) == Ordering::Equal);
    b.c0 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Equal);
    b.c1 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Less);
    a.c1 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Greater);
    b.c0 += &Fq::one();
    assert!(a.cmp(&b) == Ordering::Equal);
}

#[test]
fn test_fq2_basics() {
    assert_eq!(Fq2::new(Fq::zero(), Fq::zero(),), Fq2::zero());
    assert_eq!(Fq2::new(Fq::one(), Fq::zero(),), Fq2::one());
    assert!(Fq2::zero().is_zero());
    assert!(!Fq2::one().is_zero());
    assert!(!Fq2::new(Fq::zero(), Fq::one(),).is_zero());
}

#[test]
fn test_fq2_legendre() {
    use ark_ff::fields::LegendreSymbol::*;

    assert_eq!(Zero, Fq2::zero().legendre());
    // i^2 = -1
    let mut m1 = -Fq2::one();
    assert_eq!(QuadraticResidue, m1.legendre());
    Fq6Config::mul_fp2_by_nonresidue_in_place(&mut m1);
    assert_eq!(QuadraticNonResidue, m1.legendre());
}

#[test]
fn test_fq6_mul_by_1() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c1 = Fq2::rand(&mut rng);
        let mut a = Fq6::rand(&mut rng);
        let mut b = a;

        a.mul_by_1(&c1);
        b *= &Fq6::new(Fq2::zero(), c1, Fq2::zero());

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq6_mul_by_01() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c1 = Fq2::rand(&mut rng);
        let mut a = Fq6::rand(&mut rng);
        let mut b = a;

        a.mul_by_01(&c0, &c1);
        b *= &Fq6::new(c0, c1, Fq2::zero());

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq12_mul_by_014() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c1 = Fq2::rand(&mut rng);
        let c5 = Fq2::rand(&mut rng);
        let mut a = Fq12::rand(&mut rng);
        let mut b = a;

        a.mul_by_014(&c0, &c1, &c5);
        b.mul_assign(&Fq12::new(
            Fq6::new(c0, c1, Fq2::zero()),
            Fq6::new(Fq2::zero(), c5, Fq2::zero()),
        ));

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq12_mul_by_034() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c3 = Fq2::rand(&mut rng);
        let c4 = Fq2::rand(&mut rng);
        let mut a = Fq12::rand(&mut rng);
        let mut b = a;

        a.mul_by_034(&c0, &c3, &c4);
        b.mul_assign(&Fq12::new(
            Fq6::new(c0, Fq2::zero(), Fq2::zero()),
            Fq6::new(c3, c4, Fq2::zero()),
        ));

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq12_karabina_cyclotomic_exp_z2_zero_and_edge_exponents() {
    use ark_ff::{AdditiveGroup, CyclotomicMultSubgroup};

    // Construct deterministic nontrivial g in G_{Phi_6(q^2)} over BLS12-377 with z2 == 0, z3 != 0
    // via genus-0 curve xi * z3^3 - 6 * z4 * z3 + 8 * z4^3 = 0 (hit at m = 8 + u).
    let xi = Fq6Config::NONRESIDUE;
    let xi_inv = xi.inverse().unwrap();
    let mut g_opt = None;
    for m_c0 in 1u64..64 {
        let m = Fq2::new(Fq::from(m_c0), Fq::one());
        let m3 = m.square() * m;
        let Some(den_inv) = (xi + Fq2::from(8u8) * m3).inverse() else {
            continue;
        };
        let z3 = (Fq2::from(6u8) * m) * den_inv;
        if z3.is_zero() {
            continue;
        }
        let z4 = m * z3;
        let z4_sq = z4.square();
        let rhs = (z3.double() - (z4_sq.double() + z4_sq)) * xi_inv;
        if let Some(z5) = rhs.sqrt() {
            let z1 = (m * z5).double();
            let z34 = z3 * z4;
            let inner = z1.square().double() - (z34.double() + z34);
            let z0 = Fq6Config::mul_fp2_by_nonresidue(inner) + Fq2::one();
            g_opt = Some(Fq12::new(
                Fq6::new(z0, z4, z3),
                Fq6::new(Fq2::zero(), z1, z5),
            ));
            break;
        }
    }
    let g = g_opt.expect("must find deterministic z2 == 0, z3 != 0 witness over BLS12-377");
    assert!(g.c1.c0.is_zero() && !g.c0.c2.is_zero());

    // Check g^(q^4 - q^2 + 1) == 1 using Frobenius: g^(q^4) * g == g^(q^2)
    let mut g_q4 = g;
    g_q4.frobenius_map_in_place(4);
    let mut g_q2 = g;
    g_q2.frobenius_map_in_place(2);
    assert_eq!(g_q4 * g, g_q2);

    // Random cyclotomic element + edge exponents (`[0x0002_aaaa_aaaa_0000]`, `[u64::MAX]`, seed)
    let mut rng = test_rng();
    let x = Fq12::rand(&mut rng);
    let mut conj_x = x;
    conj_x.conjugate_in_place();
    let r = conj_x * x.inverse().unwrap();
    let mut r_q2 = r;
    r_q2.frobenius_map_in_place(2);
    let h = r_q2 * r;

    for exp in [
        &[0u64][..],
        &[1u64][..],
        &[2u64][..],
        &[6u64][..],
        &[0x0002_aaaa_aaaa_0000u64][..],
        &[u64::MAX][..],
        &[0x8508_c000_0000_0001u64][..],
        &[u64::MAX, u64::MAX][..],
    ] {
        assert_eq!(g.cyclotomic_exp(exp), g.pow(exp));
        assert_eq!(h.cyclotomic_exp(exp), h.pow(exp));
    }
}

#![allow(unused)]
#![allow(clippy::eq_op)]
use ark_ff::{
    fields::{FftField, Field, LegendreSymbol, PrimeField, SquareRootField},
    Fp, MontBackend, MontConfig,
};
use ark_serialize::{buffer_bit_byte_size, Flags, SWFlags};
use ark_std::{io::Cursor, rand::Rng};

pub const ITERATIONS: u32 = 40;

fn random_negation_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let a = F::rand(rng);
        let mut b = -a;
        b += &a;

        assert!(b.is_zero());
    }
}

fn random_addition_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let a = F::rand(rng);
        let b = F::rand(rng);
        let c = F::rand(rng);

        let t0 = (a + &b) + &c; // (a + b) + c

        let t1 = (a + &c) + &b; // (a + c) + b

        let t2 = (b + &c) + &a; // (b + c) + a

        assert_eq!(t0, t1);
        assert_eq!(t1, t2);
    }
}

fn random_subtraction_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let a = F::rand(rng);
        let b = F::rand(rng);

        let t0 = a - &b; // (a - b)

        let mut t1 = b; // (b - a)
        t1 -= &a;

        let mut t2 = t0; // (a - b) + (b - a) = 0
        t2 += &t1;

        assert!(t2.is_zero());
    }
}

fn random_multiplication_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let a = F::rand(rng);
        let b = F::rand(rng);
        let c = F::rand(rng);

        let mut t0 = a; // (a * b) * c
        t0 *= &b;
        t0 *= &c;

        let mut t1 = a; // (a * c) * b
        t1 *= &c;
        t1 *= &b;

        let mut t2 = b; // (b * c) * a
        t2 *= &c;
        t2 *= &a;

        assert_eq!(t0, t1);
        assert_eq!(t1, t2);
    }
}

fn random_inversion_tests<F: Field, R: Rng>(rng: &mut R) {
    assert!(F::zero().inverse().is_none());

    for _ in 0..ITERATIONS {
        let mut a = F::rand(rng);
        let b = a.inverse().map(|b| {
            a *= &b;
            assert_eq!(a, F::one());
        });
    }
}

fn random_doubling_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let mut a = F::rand(rng);
        let mut b = a;
        a += &b;
        b.double_in_place();

        assert_eq!(a, b);
    }
}

fn random_squaring_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        let mut a = F::rand(rng);
        let mut b = a;
        a *= &b;
        b.square_in_place();

        assert_eq!(a, b);
    }
}

fn random_expansion_tests<F: Field, R: Rng>(rng: &mut R) {
    for _ in 0..ITERATIONS {
        // Compare (a + b)(c + d) and (a*c + b*c + a*d + b*d)

        let a = F::rand(rng);
        let b = F::rand(rng);
        let c = F::rand(rng);
        let d = F::rand(rng);

        let mut t0 = a;
        t0 += &b;
        let mut t1 = c;
        t1 += &d;
        t0 *= &t1;

        let mut t2 = a;
        t2 *= &c;
        let mut t3 = b;
        t3 *= &c;
        let mut t4 = a;
        t4 *= &d;
        let mut t5 = b;
        t5 *= &d;

        t2 += &t3;
        t2 += &t4;
        t2 += &t5;

        assert_eq!(t0, t2);
    }

    for _ in 0..ITERATIONS {
        // Compare (a + b)c and (a*c + b*c)

        let a = F::rand(rng);
        let b = F::rand(rng);
        let c = F::rand(rng);

        let t0 = (a + &b) * &c;
        let t2 = a * &c + &(b * &c);

        assert_eq!(t0, t2);
    }
}

fn random_field_tests<F: Field>() {
    let mut rng = ark_std::test_rng();

    random_negation_tests::<F, _>(&mut rng);
    random_addition_tests::<F, _>(&mut rng);
    random_subtraction_tests::<F, _>(&mut rng);
    random_multiplication_tests::<F, _>(&mut rng);
    random_inversion_tests::<F, _>(&mut rng);
    random_doubling_tests::<F, _>(&mut rng);
    random_squaring_tests::<F, _>(&mut rng);
    random_expansion_tests::<F, _>(&mut rng);

    assert!(F::zero().is_zero());
    {
        let z = -F::zero();
        assert!(z.is_zero());
    }

    assert!(F::zero().inverse().is_none());

    // Multiplication by zero
    {
        let a = F::rand(&mut rng) * &F::zero();
        assert!(a.is_zero());
    }

    // Addition by zero
    {
        let mut a = F::rand(&mut rng);
        let copy = a;
        a += &F::zero();
        assert_eq!(a, copy);
    }
}

fn random_sqrt_tests<F: SquareRootField>() {
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        let a = F::rand(&mut rng);
        let b = a.square();
        assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

        let b = b.sqrt().unwrap();
        assert!(a == b || a == -b);
    }

    let mut c = F::one();
    for _ in 0..ITERATIONS {
        let mut b = c.square();
        assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

        b = b.sqrt().unwrap();

        if b != c {
            b = -b;
        }

        assert_eq!(b, c);

        c += &F::one();
    }
}

pub fn from_str_test<F: PrimeField>() {
    {
        let mut rng = ark_std::test_rng();

        for _ in 0..ITERATIONS {
            let n: u64 = rng.gen();

            let a = F::from_str(&ark_std::format!("{}", n))
                .map_err(|_| ())
                .unwrap();
            let b = F::from(n);

            assert_eq!(a, b);
        }
    }

    assert!(F::from_str("").is_err());
    assert!(F::from_str("0").map_err(|_| ()).unwrap().is_zero());
    assert!(F::from_str("00").is_err());
    assert!(F::from_str("00000000000").is_err());
}

pub fn field_test<F: Field>(a: F, b: F) {
    let zero = F::zero();
    assert_eq!(zero, zero);
    assert_eq!(zero.is_zero(), true);
    assert_eq!(zero.is_one(), false);

    let one = F::one();
    assert_eq!(one, one);
    assert_eq!(one.is_zero(), false);
    assert_eq!(one.is_one(), true);
    assert_eq!(zero + &one, one);

    let two = one + &one;
    assert_eq!(two, two);
    assert_ne!(zero, two);
    assert_ne!(one, two);

    // a == a
    assert_eq!(a, a);
    // a + 0 = a
    assert_eq!(a + &zero, a);
    // a - 0 = a
    assert_eq!(a - &zero, a);
    // a - a = 0
    assert_eq!(a - &a, zero);
    // 0 - a = -a
    assert_eq!(zero - &a, -a);
    // a.double() = a + a
    assert_eq!(a.double(), a + &a);
    // b.double() = b + b
    assert_eq!(b.double(), b + &b);
    // a + b = b + a
    assert_eq!(a + &b, b + &a);
    // a - b = -(b - a)
    assert_eq!(a - &b, -(b - &a));
    // (a + b) + a = a + (b + a)
    assert_eq!((a + &b) + &a, a + &(b + &a));
    // (a + b).double() = (a + b) + (b + a)
    assert_eq!((a + &b).double(), (a + &b) + &(b + &a));

    // a * 0 = 0
    assert_eq!(a * &zero, zero);
    // a * 1 = a
    assert_eq!(a * &one, a);
    // a * 2 = a.double()
    assert_eq!(a * &two, a.double());
    // a * a^-1 = 1
    assert_eq!(a * &a.inverse().unwrap(), one);
    // a * a = a^2
    assert_eq!(a * &a, a.square());
    // a * a * a = a^3
    assert_eq!(a * &(a * &a), a.pow([0x3, 0x0, 0x0, 0x0]));
    // a * b = b * a
    assert_eq!(a * &b, b * &a);
    // (a * b) * a = a * (b * a)
    assert_eq!((a * &b) * &a, a * &(b * &a));
    // (a + b)^2 = a^2 + 2ab + b^2
    assert_eq!(
        (a + &b).square(),
        a.square() + &((a * &b) + &(a * &b)) + &b.square()
    );
    // (a - b)^2 = (-(b - a))^2
    assert_eq!((a - &b).square(), (-(b - &a)).square());
    random_field_tests::<F>();
}

pub fn fft_field_test<F: FftField>() {
    assert_eq!(
        F::TWO_ADIC_ROOT_OF_UNITY.pow([1 << F::TWO_ADICITY]),
        F::one()
    );

    if let Some(small_subgroup_base) = F::SMALL_SUBGROUP_BASE {
        let small_subgroup_base_adicity = F::SMALL_SUBGROUP_BASE_ADICITY.unwrap();
        let large_subgroup_root_of_unity = F::LARGE_SUBGROUP_ROOT_OF_UNITY.unwrap();
        let pow =
            (1 << F::TWO_ADICITY) * (small_subgroup_base as u64).pow(small_subgroup_base_adicity);
        assert_eq!(large_subgroup_root_of_unity.pow([pow]), F::one());

        for i in 0..F::TWO_ADICITY {
            for j in 0..small_subgroup_base_adicity {
                use core::convert::TryFrom;
                let size = usize::try_from(1 << i as usize).unwrap()
                    * usize::try_from((small_subgroup_base as u64).pow(j)).unwrap();
                let root = F::get_root_of_unity(size as u64).unwrap();
                assert_eq!(root.pow([size as u64]), F::one());
            }
        }
    } else {
        for i in 0..F::TWO_ADICITY {
            let size = 1 << i;
            let root = F::get_root_of_unity(size).unwrap();
            assert_eq!(root.pow([size as u64]), F::one());
        }
    }
}

pub fn primefield_test<F: PrimeField>() {
    from_str_test::<F>();
    let one = F::one();
    assert_eq!(F::from(one.into_bigint()), one);

    fft_field_test::<F>();
}

pub fn montgomery_primefield_test<T: MontConfig<N>, const N: usize>() {
    use ark_ff::FpConfig;
    use num_bigint::BigUint;
    use num_integer::Integer;
    let modulus: BigUint = T::MODULUS.into();
    let r = BigUint::from(2u8).modpow(&((N * 64) as u64).into(), &modulus);
    let r2 = (&r * &r) % &modulus;
    assert_eq!(r, T::R.into());
    assert_eq!(r2, T::R2.into());
    assert_eq!(
        Fp::<MontBackend<T, N>, N>::MODULUS_BIT_SIZE as u64,
        modulus.bits()
    );

    let modulus_minus_one = &modulus - 1u8;
    assert_eq!(
        BigUint::from(Fp::<MontBackend<T, N>, N>::MODULUS_MINUS_ONE_DIV_TWO),
        &modulus_minus_one / 2u32
    );

    let mut two_adicity = 0;
    let mut trace = modulus_minus_one.clone();
    while trace.is_even() {
        trace /= 2u8;
        two_adicity += 1;
    }
    assert_eq!(two_adicity, MontBackend::<T, N>::TWO_ADICITY);
    assert_eq!(BigUint::from(Fp::<MontBackend<T, N>, N>::TRACE), trace);
    let trace_minus_one_div_two = (&trace - 1u8) / 2u8;
    assert_eq!(
        BigUint::from(Fp::<MontBackend<T, N>, N>::TRACE_MINUS_ONE_DIV_TWO),
        trace_minus_one_div_two
    );

    let two_adic_root_of_unity: BigUint = <MontBackend<T, N>>::TWO_ADIC_ROOT_OF_UNITY.into();
    let generator: BigUint = <MontBackend<T, N>>::GENERATOR.into_bigint().into();
    assert_eq!(two_adic_root_of_unity, generator.modpow(&trace, &modulus));
    match (T::SMALL_SUBGROUP_BASE, T::SMALL_SUBGROUP_BASE_ADICITY) {
        (Some(base), Some(adicity)) => {
            let mut e = generator.clone();
            for _i in 0..adicity {
                e = e.modpow(&base.into(), &modulus)
            }
        },
        (None, None) => {},
        (_, _) => {
            panic!("Should specify both `SMALL_SUBGROUP_BASE` and `SMALL_SUBGROUP_BASE_ADICITY`")
        },
    }
}

pub fn sqrt_field_test<F: SquareRootField>(elem: F) {
    let square = elem.square();
    let sqrt = square.sqrt().unwrap();
    assert!(sqrt == elem || sqrt == -elem);
    if let Some(sqrt) = elem.sqrt() {
        assert!(sqrt.square() == elem || sqrt.square() == -elem);
    }
    random_sqrt_tests::<F>();
}

pub fn frobenius_test<F: Field, C: AsRef<[u64]>>(characteristic: C, maxpower: usize) {
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        let a = F::rand(&mut rng);

        let mut a_0 = a;
        a_0.frobenius_map(0);
        assert_eq!(a, a_0);

        let mut a_q = a.pow(&characteristic);
        for power in 1..maxpower {
            let mut a_qi = a;
            a_qi.frobenius_map(power);
            assert_eq!(a_qi, a_q, "failed on power {}", power);

            a_q = a_q.pow(&characteristic);
        }
    }
}

pub fn field_serialization_test<F: Field>(buf_size: usize) {
    let mut rng = ark_std::test_rng();

    for _ in 0..ITERATIONS {
        let a = F::rand(&mut rng);
        {
            let mut serialized = vec![0u8; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = F::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let mut serialized = vec![0u8; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = F::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let mut serialized = vec![0u8; buf_size + 1];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_with_flags(&mut cursor, SWFlags::from_y_sign(true))
                .unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let (b, flags) = F::deserialize_with_flags::<_, SWFlags>(&mut cursor).unwrap();
            assert_eq!(flags.is_positive(), Some(true));
            assert!(!flags.is_infinity());
            assert_eq!(a, b);
        }

        #[derive(Default, Clone, Copy, Debug)]
        struct DummyFlags;
        impl Flags for DummyFlags {
            const BIT_SIZE: usize = 200;

            fn u8_bitmask(&self) -> u8 {
                0
            }

            fn from_u8(_value: u8) -> Option<Self> {
                Some(DummyFlags)
            }
        }

        use ark_serialize::SerializationError;
        {
            let mut serialized = vec![0; buf_size];
            assert!(if let SerializationError::NotEnoughSpace = a
                .serialize_with_flags(&mut &mut serialized[..], DummyFlags)
                .unwrap_err()
            {
                true
            } else {
                false
            });
            assert!(if let SerializationError::NotEnoughSpace =
                F::deserialize_with_flags::<_, DummyFlags>(&mut &serialized[..]).unwrap_err()
            {
                true
            } else {
                false
            });
        }

        {
            let mut serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize(&mut cursor).unwrap_err();

            let mut cursor = Cursor::new(&serialized[..]);
            F::deserialize(&mut cursor).unwrap_err();
        }
    }
}

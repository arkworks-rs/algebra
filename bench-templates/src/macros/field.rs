#[macro_export]
macro_rules! f_bench {
    // Use this for base fields
    ($f:ident, $f_type:ty, $f_repr:ident, $f_repr_type:ty, $modname:ident) => {
        pub mod $modname {
            use super::*;
            field_common!($f, $f_type);
            sqrt!($f, $f_type);
            prime_field!($f, $f_type, $f_repr, $f_repr_type);
            $crate::benchmark_group!(
                $modname,
                // common stuff
                add_assign,
                sub_assign,
                double,
                negate,
                mul_assign,
                square,
                inverse,
                ser,
                deser,
                ser_unchecked,
                deser_unchecked,
                // sqrt field stuff
                sqrt,
                // prime field stuff
                repr_add_nocarry,
                repr_sub_noborrow,
                repr_num_bits,
                repr_mul2,
                repr_div2,
                into_repr,
                from_repr,
            );
        }
        use $modname::$modname;
    };
    // use this for intermediate fields
    (extension, $f:ident, $f_type:ty, $modname:ident) => {
        mod $modname {
            use super::*;
            field_common!($f, $f_type);
            sqrt!($f, $f_type);
            $crate::benchmark_group!(
                $modname,
                // common stuff
                add_assign,
                sub_assign,
                double,
                negate,
                mul_assign,
                square,
                inverse,
                ser,
                deser,
                ser_unchecked,
                deser_unchecked,
                // sqrt field stuff
                sqrt,
            );
        }
        use $modname::$modname;
    };
    // Use this for the full extension field Fqk
    (target, $f:ident, $f_type:ty, $modname:ident) => {
        mod $modname {
            use super::*;
            field_common!($f, $f_type);
            $crate::benchmark_group!(
                $modname,
                // common stuff
                add_assign,
                sub_assign,
                double,
                negate,
                mul_assign,
                square,
                inverse,
                ser,
                deser,
                ser_unchecked,
                deser_unchecked,
            );
        }
        use $modname::$modname;
    };
}

#[macro_export]
macro_rules! field_common {
    ($f:ident, $f_type:ty) => {
        fn add_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| ($f::rand(&mut rng), $f::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, add_assign, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn sub_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| ($f::rand(&mut rng), $f::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, sub_assign, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn double(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                n_fold!(tmp, double_in_place);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn negate(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                tmp = -tmp;
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn mul_assign(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| ($f::rand(&mut rng), $f::rand(&mut rng)))
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, mul_assign, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn square(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                n_fold!(tmp, square_in_place);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn inverse(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count].inverse();
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn deser(b: &mut $crate::bencher::Bencher) {
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut num_bytes = 0;
            let v: Vec<_> = (0..SAMPLES)
                .flat_map(|_| {
                    let mut bytes = Vec::with_capacity(1000);
                    let tmp = $f::rand(&mut rng);
                    tmp.serialize(&mut bytes).unwrap();
                    num_bytes = bytes.len();
                    bytes
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let index = count * num_bytes;
                <$f_type>::deserialize(&v[index..(index + num_bytes)]).unwrap()
            });
        }

        fn ser(b: &mut $crate::bencher::Bencher) {
            use ark_serialize::CanonicalSerialize;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();
            let mut bytes = Vec::with_capacity(1000);

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count];
                count = (count + 1) % SAMPLES;
                bytes.clear();
                tmp.serialize(&mut bytes)
            });
        }

        fn deser_unchecked(b: &mut $crate::bencher::Bencher) {
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let mut num_bytes = 0;
            let v: Vec<_> = (0..SAMPLES)
                .flat_map(|_| {
                    let mut bytes = Vec::with_capacity(1000);
                    let tmp = $f::rand(&mut rng);
                    tmp.serialize_unchecked(&mut bytes).unwrap();
                    num_bytes = bytes.len();
                    bytes
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let index = count * num_bytes;
                <$f_type>::deserialize_unchecked(&v[index..(index + num_bytes)]).unwrap()
            });
        }

        fn ser_unchecked(b: &mut $crate::bencher::Bencher) {
            use ark_serialize::CanonicalSerialize;
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();
            let mut bytes = Vec::with_capacity(1000);

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count];
                count = (count + 1) % SAMPLES;
                bytes.clear();
                tmp.serialize_unchecked(&mut bytes)
            });
        }
    };
}

#[macro_export]
macro_rules! sqrt {
    ($f:ident, $f_type:ty) => {
        pub fn sqrt(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES)
                .map(|_| {
                    let mut tmp = $f::rand(&mut rng);
                    tmp.square_in_place();
                    tmp
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                v[count].sqrt()
            });
        }
    };
}

#[macro_export]
macro_rules! prime_field {
    ($f:ident, $f_type:ty, $f_repr:ident, $f_repr_type:ty) => {
        fn repr_add_nocarry(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| {
                    let mut tmp1 = $f_repr::rand(&mut rng);
                    let mut tmp2 = $f_repr::rand(&mut rng);
                    // Shave a few bits off to avoid overflow.
                    for _ in 0..3 {
                        tmp1.div2();
                        tmp2.div2();
                    }
                    (tmp1, tmp2)
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, add_with_carry, count);
                count = (count + 1) % SAMPLES;
                tmp
            });
        }

        fn repr_sub_noborrow(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<_> = (0..SAMPLES)
                .map(|_| {
                    let tmp1 = $f_repr::rand(&mut rng);
                    let mut tmp2 = tmp1;
                    // Ensure tmp2 is smaller than tmp1.
                    for _ in 0..10 {
                        tmp2.div2();
                    }
                    (tmp1, tmp2)
                })
                .collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count].0;
                n_fold!(tmp, v, sub_with_borrow, count);
                count = (count + 1) % SAMPLES;
                tmp;
            });
        }

        fn repr_num_bits(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_repr_type> = (0..SAMPLES).map(|_| $f_repr::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let tmp = v[count].num_bits();
                count = (count + 1) % SAMPLES;
                tmp;
            });
        }

        fn repr_mul2(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_repr_type> = (0..SAMPLES).map(|_| $f_repr::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                n_fold!(tmp, mul2);
                count = (count + 1) % SAMPLES;
                tmp;
            });
        }

        fn repr_div2(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_repr_type> = (0..SAMPLES).map(|_| $f_repr::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                let mut tmp = v[count];
                n_fold!(tmp, div2);
                count = (count + 1) % SAMPLES;
                tmp;
            });
        }

        fn into_repr(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_type> = (0..SAMPLES).map(|_| $f::rand(&mut rng)).collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                v[count].into_bigint();
            });
        }

        fn from_repr(b: &mut $crate::bencher::Bencher) {
            const SAMPLES: usize = 1000;

            let mut rng = ark_std::test_rng();

            let v: Vec<$f_repr_type> = (0..SAMPLES)
                .map(|_| $f::rand(&mut rng).into_bigint())
                .collect();

            let mut count = 0;
            b.iter(|| {
                count = (count + 1) % SAMPLES;
                let _ = $f::from(v[count]);
            });
        }
    };
}

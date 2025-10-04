use super::*;
use crate::small_fp::utils::{
    compute_two_adic_root_of_unity, compute_two_adicity, generate_bigint_casts,
    generate_sqrt_precomputation,
};

pub(crate) fn backend_impl(
    ty: proc_macro2::TokenStream,
    modulus: u128,
    generator: u128,
) -> proc_macro2::TokenStream {
    let two_adicity = compute_two_adicity(modulus);
    let two_adic_root_of_unity = compute_two_adic_root_of_unity(modulus, two_adicity);

    let (from_bigint_impl, into_bigint_impl) = generate_bigint_casts(modulus);
    let sqrt_precomp_impl = generate_sqrt_precomputation(modulus, two_adicity);

    quote! {
        type T = #ty;
        const MODULUS: Self::T = #modulus as Self::T;
        const MODULUS_128: u128 = #modulus;
        const GENERATOR: SmallFp<Self> = SmallFp::new(#generator as Self::T);
        const ZERO: SmallFp<Self> = SmallFp::new(0 as Self::T);
        const ONE: SmallFp<Self> = SmallFp::new(1 as Self::T);
        const NEG_ONE: SmallFp<Self> = SmallFp::new((Self::MODULUS - 1) as Self::T);

        const TWO_ADICITY: u32 = #two_adicity;
        const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self> = SmallFp::new(#two_adic_root_of_unity as Self::T);
        #sqrt_precomp_impl

        fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            a.value = match a.value.overflowing_add(b.value) {
                (val, false) => val % Self::MODULUS,
                (val, true) => (Self::T::MAX - Self::MODULUS + 1 + val) % Self::MODULUS,
            };
        }

        fn sub_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            if a.value >= b.value {
                a.value -= b.value;
            } else {
                a.value = Self::MODULUS - (b.value - a.value);
            }
        }

        fn double_in_place(a: &mut SmallFp<Self>) {
            //* Note: This might be faster using bitshifts
            let tmp = *a;
            Self::add_assign(a, &tmp);
        }

        fn neg_in_place(a: &mut SmallFp<Self>) {
            if a.value != (0 as Self::T) {
                a.value = Self::MODULUS - a.value;
            }
        }

        // TODO: this could be done faster
        // a = a1*C + a0, b = b1*C + b0
        // a*b = a1*b1*C^2 + (a1*b0 + a0*b1)*C + a0*b0
        fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>) {
            let a_128 = (a.value as u128) % #modulus;
            let b_128 = (b.value as u128) % #modulus;
            let mod_add = |x: u128, y: u128| -> u128 {
                if x >= #modulus - y {
                    x - (#modulus - y)
                } else {
                    x + y
                }
            };
            a.value = match a_128.overflowing_mul(b_128) {
                (val, false) => (val % #modulus) as Self::T,
                (_, true) => {
                    let mut result = 0u128;
                    let mut base = a_128 % #modulus;
                    let mut exp = b_128;
                    while exp > 0 {
                        if exp & 1 == 1 {
                            result = mod_add(result, base);
                        }
                        base = mod_add(base, base);
                        exp >>= 1;
                    }
                    result as Self::T
                }
            };
        }

        fn sum_of_products<const T: usize>(
            a: &[SmallFp<Self>; T],
            b: &[SmallFp<Self>; T],) -> SmallFp<Self> {
            let mut acc = SmallFp::new(0 as Self::T);
            for (x, y) in a.iter().zip(b.iter()) {
                let mut prod = *x;
                Self::mul_assign(&mut prod, y);
                Self::add_assign(&mut acc, &prod);
            }
            acc
        }

        fn square_in_place(a: &mut SmallFp<Self>) {
            let tmp = *a;
            Self::mul_assign(a, &tmp);
        }

        fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>> {
            if a.value == 0 {
                return None;
            }
            let mut base = *a;
            let mut exp = Self::MODULUS - 2;
            let mut acc = Self::ONE;
            while exp > 0 {
                if (exp & 1) == 1 {
                    Self::mul_assign(&mut acc, &base);
                }
                let mut sq = base;
                Self::mul_assign(&mut sq, &base);
                base = sq;
                exp >>= 1;
            }
            Some(acc)
        }

        #from_bigint_impl

        #into_bigint_impl
    }
}

pub(crate) fn new() -> proc_macro2::TokenStream {
    quote! {
        pub fn new(value: <Self as SmallFpConfig>::T) -> SmallFp<Self> {
                SmallFp::new(value % <Self as SmallFpConfig>::MODULUS)
        }
    }
}

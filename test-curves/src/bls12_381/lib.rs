#![feature(prelude_import)]
#![no_std]
#[prelude_import]
use core::prelude::rust_2021::*;
#[macro_use]
extern crate core;
#[macro_use]
extern crate compiler_builtins;
extern crate ark_ff;
pub use ark_ff::*;
extern crate ark_ec;
pub use ark_ec::*;
#[cfg(any(feature = "bls12_381_scalar_field", feature = "bls12_381_curve"))]
pub mod bls12_381 {
    pub mod fr {
        use ark_ff::fields::{Fp256, MontBackend, MontConfig};
        #[modulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
        #[generator = "7"]
        #[small_subgroup_base = "3"]
        #[small_subgroup_power = "1"]
        pub struct FrConfig;
        fn frconfig___() {
            use ark_ff::{
                fields::Fp, BigInt, BigInteger, biginteger::arithmetic as fa, fields::*,
            };
            type B = BigInt<4usize>;
            type F = Fp<MontBackend<FrConfig, 4usize>, 4usize>;
            #[automatically_derived]
            impl MontConfig<4usize> for FrConfig {
                const MODULUS: B = BigInt([
                    18446744069414584321u64,
                    6034159408538082302u64,
                    3691218898639771653u64,
                    8353516859464449352u64,
                ]);
                const GENERATOR: F = {
                    let (is_positive, limbs) = (true, [7u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                };
                const TWO_ADIC_ROOT_OF_UNITY: F = {
                    let (is_positive, limbs) = (
                        true,
                        [
                            4046931900703378731u64,
                            13129826145616953529u64,
                            15031722638446171060u64,
                            1631043718794977056u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                };
                const SMALL_SUBGROUP_BASE: Option<u32> = Some(3u32);
                const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = Some(1u32);
                const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<F> = Some({
                    let (is_positive, limbs) = (
                        true,
                        [
                            196249104034986263u64,
                            9632877624223158608u64,
                            16881125688358416649u64,
                            4331619260936696776u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                });
                #[inline(always)]
                fn add_assign(a: &mut F, b: &F) {
                    __add_with_carry(&mut a.0, &b.0);
                    __subtract_modulus(a);
                }
                #[inline(always)]
                fn sub_assign(a: &mut F, b: &F) {
                    if b.0 > a.0 {
                        __add_with_carry(
                            &mut a.0,
                            &BigInt([
                                18446744069414584321u64,
                                6034159408538082302u64,
                                3691218898639771653u64,
                                8353516859464449352u64,
                            ]),
                        );
                    }
                    __sub_with_borrow(&mut a.0, &b.0);
                }
                #[inline(always)]
                fn double_in_place(a: &mut F) {
                    a.0.mul2();
                    __subtract_modulus(a);
                }
                /// Sets `a = -a`.
                #[inline(always)]
                fn neg_in_place(a: &mut F) {
                    if *a != F::ZERO {
                        let mut tmp = BigInt([
                            18446744069414584321u64,
                            6034159408538082302u64,
                            3691218898639771653u64,
                            8353516859464449352u64,
                        ]);
                        __sub_with_borrow(&mut tmp, &a.0);
                        a.0 = tmp;
                    }
                }
                #[inline(always)]
                fn mul_assign(a: &mut F, b: &F) {
                    {
                        if false {} else {
                            #[cfg(
                                not(
                                    all(
                                        feature = "asm",
                                        target_feature = "bmi2",
                                        target_feature = "adx",
                                        target_arch = "x86_64"
                                    )
                                )
                            )]
                            {
                                let mut r = [0u64; 4usize];
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry2,
                                );
                                r[4usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry2,
                                );
                                r[4usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry2,
                                );
                                r[4usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry2,
                                );
                                r[4usize - 1] = carry1 + carry2;
                                (a.0).0 = r;
                            }
                        }
                    }
                    __subtract_modulus(a);
                }
                #[inline(always)]
                fn square_in_place(a: &mut F) {
                    {
                        if false {} else {
                            #[cfg(
                                not(
                                    all(
                                        feature = "asm",
                                        target_feature = "bmi2",
                                        target_feature = "adx",
                                        target_arch = "x86_64"
                                    )
                                )
                            )]
                            {
                                let mut r = [0u64; 8usize];
                                let mut carry = 0;
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[0usize],
                                    (a.0).0[1usize],
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[0usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[0usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[4usize + 0usize] = carry;
                                carry = 0;
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[1usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[1usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[4usize + 1usize] = carry;
                                carry = 0;
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[2usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[4usize + 2usize] = carry;
                                carry = 0;
                                r[8usize - 1] = r[8usize - 2] >> 63;
                                r[6usize] = (r[6usize] << 1) | (r[6usize - 1] >> 63);
                                r[5usize] = (r[5usize] << 1) | (r[5usize - 1] >> 63);
                                r[4usize] = (r[4usize] << 1) | (r[4usize - 1] >> 63);
                                r[3usize] = (r[3usize] << 1) | (r[3usize - 1] >> 63);
                                r[2usize] = (r[2usize] << 1) | (r[2usize - 1] >> 63);
                                r[1] <<= 1;
                                r[0usize] = fa::mac_with_carry(
                                    r[0usize],
                                    (a.0).0[0usize],
                                    (a.0).0[0usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[0usize + 1], 0, carry);
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[1usize],
                                    (a.0).0[1usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[2usize + 1], 0, carry);
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[2usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[4usize + 1], 0, carry);
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    (a.0).0[3usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[6usize + 1], 0, carry);
                                let mut carry2 = 0;
                                let k = r[0usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[0usize],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[4usize + 0usize], carry, carry2);
                                let k = r[1usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[1usize],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[4usize + 1usize], carry, carry2);
                                let k = r[2usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[2usize],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[4usize + 2usize], carry, carry2);
                                let k = r[3usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[3usize],
                                    k,
                                    18446744069414584321u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    6034159408538082302u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    3691218898639771653u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    8353516859464449352u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[4usize + 3usize], carry, carry2);
                                (a.0).0 = r[4usize..].try_into().unwrap();
                            }
                        }
                    }
                    __subtract_modulus(a);
                }
                fn sum_of_products<const M: usize>(a: &[F; M], b: &[F; M]) -> F {
                    a.iter().zip(b).map(|(a, b)| *a * b).sum()
                }
            }
            #[inline(always)]
            fn __subtract_modulus(a: &mut F) {
                if a.is_geq_modulus() {
                    __sub_with_borrow(
                        &mut a.0,
                        &BigInt([
                            18446744069414584321u64,
                            6034159408538082302u64,
                            3691218898639771653u64,
                            8353516859464449352u64,
                        ]),
                    );
                }
            }
            #[inline(always)]
            fn __subtract_modulus_with_carry(a: &mut F, carry: bool) {
                if a.is_geq_modulus() || carry {
                    __sub_with_borrow(
                        &mut a.0,
                        &BigInt([
                            18446744069414584321u64,
                            6034159408538082302u64,
                            3691218898639771653u64,
                            8353516859464449352u64,
                        ]),
                    );
                }
            }
            #[inline(always)]
            fn __add_with_carry(a: &mut B, b: &B) -> bool {
                use ark_ff::biginteger::arithmetic::adc_for_add_with_carry as adc;
                let mut carry = 0;
                carry = adc(&mut a.0[0usize], b.0[0usize], carry);
                carry = adc(&mut a.0[1usize], b.0[1usize], carry);
                carry = adc(&mut a.0[2usize], b.0[2usize], carry);
                carry = adc(&mut a.0[3usize], b.0[3usize], carry);
                carry != 0
            }
            #[inline(always)]
            fn __sub_with_borrow(a: &mut B, b: &B) -> bool {
                use ark_ff::biginteger::arithmetic::sbb_for_sub_with_borrow as sbb;
                let mut borrow = 0;
                borrow = sbb(&mut a.0[0usize], b.0[0usize], borrow);
                borrow = sbb(&mut a.0[1usize], b.0[1usize], borrow);
                borrow = sbb(&mut a.0[2usize], b.0[2usize], borrow);
                borrow = sbb(&mut a.0[3usize], b.0[3usize], borrow);
                borrow != 0
            }
        }
        pub type Fr = Fp256<MontBackend<FrConfig, 4>>;
        extern crate test;
        #[cfg(test)]
        #[rustc_test_marker = "bls12_381::fr::test_inv"]
        pub const test_inv: test::TestDescAndFn = test::TestDescAndFn {
            desc: test::TestDesc {
                name: test::StaticTestName("bls12_381::fr::test_inv"),
                ignore: false,
                ignore_message: ::core::option::Option::None,
                compile_fail: false,
                no_run: false,
                should_panic: test::ShouldPanic::No,
                test_type: test::TestType::UnitTest,
            },
            testfn: test::StaticTestFn(|| test::assert_test_result(test_inv())),
        };
        fn test_inv() {
            match (&FrConfig::INV, &0xffff_fffe_ffff_ffff) {
                (left_val, right_val) => {
                    if !(*left_val == *right_val) {
                        let kind = ::core::panicking::AssertKind::Eq;
                        ::core::panicking::assert_failed(
                            kind,
                            &*left_val,
                            &*right_val,
                            ::core::option::Option::None,
                        );
                    }
                }
            };
        }
        extern crate test;
        #[cfg(test)]
        #[rustc_test_marker = "bls12_381::fr::test_modulus"]
        pub const test_modulus: test::TestDescAndFn = test::TestDescAndFn {
            desc: test::TestDesc {
                name: test::StaticTestName("bls12_381::fr::test_modulus"),
                ignore: false,
                ignore_message: ::core::option::Option::None,
                compile_fail: false,
                no_run: false,
                should_panic: test::ShouldPanic::No,
                test_type: test::TestType::UnitTest,
            },
            testfn: test::StaticTestFn(|| test::assert_test_result(test_modulus())),
        };
        fn test_modulus() {
            match (
                &FrConfig::MODULUS.0,
                &[
                    0xffff_ffff_0000_0001,
                    0x53bd_a402_fffe_5bfe,
                    0x3339_d808_09a1_d805,
                    0x73ed_a753_299d_7d48,
                ],
            ) {
                (left_val, right_val) => {
                    if !(*left_val == *right_val) {
                        let kind = ::core::panicking::AssertKind::Eq;
                        ::core::panicking::assert_failed(
                            kind,
                            &*left_val,
                            &*right_val,
                            ::core::option::Option::None,
                        );
                    }
                }
            };
        }
    }
    pub use fr::*;
    #[cfg(feature = "bls12_381_curve")]
    pub mod fq {
        use ark_ff::fields::{Fp384, MontBackend};
        #[modulus = "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"]
        #[generator = "2"]
        pub struct FqConfig;
        fn fqconfig___() {
            use ark_ff::{
                fields::Fp, BigInt, BigInteger, biginteger::arithmetic as fa, fields::*,
            };
            type B = BigInt<6usize>;
            type F = Fp<MontBackend<FqConfig, 6usize>, 6usize>;
            #[automatically_derived]
            impl MontConfig<6usize> for FqConfig {
                const MODULUS: B = BigInt([
                    13402431016077863595u64,
                    2210141511517208575u64,
                    7435674573564081700u64,
                    7239337960414712511u64,
                    5412103778470702295u64,
                    1873798617647539866u64,
                ]);
                const GENERATOR: F = {
                    let (is_positive, limbs) = (true, [2u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                };
                const TWO_ADIC_ROOT_OF_UNITY: F = {
                    let (is_positive, limbs) = (
                        true,
                        [
                            13402431016077863594u64,
                            2210141511517208575u64,
                            7435674573564081700u64,
                            7239337960414712511u64,
                            5412103778470702295u64,
                            1873798617647539866u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                };
                #[inline(always)]
                fn add_assign(a: &mut F, b: &F) {
                    __add_with_carry(&mut a.0, &b.0);
                    __subtract_modulus(a);
                }
                #[inline(always)]
                fn sub_assign(a: &mut F, b: &F) {
                    if b.0 > a.0 {
                        __add_with_carry(
                            &mut a.0,
                            &BigInt([
                                13402431016077863595u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ]),
                        );
                    }
                    __sub_with_borrow(&mut a.0, &b.0);
                }
                #[inline(always)]
                fn double_in_place(a: &mut F) {
                    a.0.mul2();
                    __subtract_modulus(a);
                }
                /// Sets `a = -a`.
                #[inline(always)]
                fn neg_in_place(a: &mut F) {
                    if *a != F::ZERO {
                        let mut tmp = BigInt([
                            13402431016077863595u64,
                            2210141511517208575u64,
                            7435674573564081700u64,
                            7239337960414712511u64,
                            5412103778470702295u64,
                            1873798617647539866u64,
                        ]);
                        __sub_with_borrow(&mut tmp, &a.0);
                        a.0 = tmp;
                    }
                }
                #[inline(always)]
                fn mul_assign(a: &mut F, b: &F) {
                    {
                        if false {} else {
                            #[cfg(
                                not(
                                    all(
                                        feature = "asm",
                                        target_feature = "bmi2",
                                        target_feature = "adx",
                                        target_arch = "x86_64"
                                    )
                                )
                            )]
                            {
                                let mut r = [0u64; 6usize];
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[0usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[1usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[2usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[3usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[4usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                let mut carry1 = 0u64;
                                r[0] = fa::mac(
                                    r[0],
                                    (a.0).0[0],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                let k = r[0].wrapping_mul(Self::INV);
                                let mut carry2 = 0u64;
                                fa::mac_discard(
                                    r[0],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry2,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[1usize],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                r[0usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry2,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[2usize],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry2,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[3usize],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry2,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[4usize],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry2,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[5usize],
                                    (b.0).0[5usize],
                                    &mut carry1,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry2,
                                );
                                r[6usize - 1] = carry1 + carry2;
                                (a.0).0 = r;
                            }
                        }
                    }
                    __subtract_modulus(a);
                }
                #[inline(always)]
                fn square_in_place(a: &mut F) {
                    {
                        if false {} else {
                            #[cfg(
                                not(
                                    all(
                                        feature = "asm",
                                        target_feature = "bmi2",
                                        target_feature = "adx",
                                        target_arch = "x86_64"
                                    )
                                )
                            )]
                            {
                                let mut r = [0u64; 12usize];
                                let mut carry = 0;
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    (a.0).0[0usize],
                                    (a.0).0[1usize],
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[0usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[0usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[0usize],
                                    (a.0).0[4usize],
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[0usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                r[6usize + 0usize] = carry;
                                carry = 0;
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    (a.0).0[1usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[1usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[1usize],
                                    (a.0).0[4usize],
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    (a.0).0[1usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                r[6usize + 1usize] = carry;
                                carry = 0;
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    (a.0).0[2usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    (a.0).0[2usize],
                                    (a.0).0[4usize],
                                    &mut carry,
                                );
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    (a.0).0[2usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                r[6usize + 2usize] = carry;
                                carry = 0;
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    (a.0).0[3usize],
                                    (a.0).0[4usize],
                                    &mut carry,
                                );
                                r[8usize] = fa::mac_with_carry(
                                    r[8usize],
                                    (a.0).0[3usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                r[6usize + 3usize] = carry;
                                carry = 0;
                                r[9usize] = fa::mac_with_carry(
                                    r[9usize],
                                    (a.0).0[4usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                r[6usize + 4usize] = carry;
                                carry = 0;
                                r[12usize - 1] = r[12usize - 2] >> 63;
                                r[10usize] = (r[10usize] << 1) | (r[10usize - 1] >> 63);
                                r[9usize] = (r[9usize] << 1) | (r[9usize - 1] >> 63);
                                r[8usize] = (r[8usize] << 1) | (r[8usize - 1] >> 63);
                                r[7usize] = (r[7usize] << 1) | (r[7usize - 1] >> 63);
                                r[6usize] = (r[6usize] << 1) | (r[6usize - 1] >> 63);
                                r[5usize] = (r[5usize] << 1) | (r[5usize - 1] >> 63);
                                r[4usize] = (r[4usize] << 1) | (r[4usize - 1] >> 63);
                                r[3usize] = (r[3usize] << 1) | (r[3usize - 1] >> 63);
                                r[2usize] = (r[2usize] << 1) | (r[2usize - 1] >> 63);
                                r[1] <<= 1;
                                r[0usize] = fa::mac_with_carry(
                                    r[0usize],
                                    (a.0).0[0usize],
                                    (a.0).0[0usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[0usize + 1], 0, carry);
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    (a.0).0[1usize],
                                    (a.0).0[1usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[2usize + 1], 0, carry);
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    (a.0).0[2usize],
                                    (a.0).0[2usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[4usize + 1], 0, carry);
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    (a.0).0[3usize],
                                    (a.0).0[3usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[6usize + 1], 0, carry);
                                r[8usize] = fa::mac_with_carry(
                                    r[8usize],
                                    (a.0).0[4usize],
                                    (a.0).0[4usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[8usize + 1], 0, carry);
                                r[10usize] = fa::mac_with_carry(
                                    r[10usize],
                                    (a.0).0[5usize],
                                    (a.0).0[5usize],
                                    &mut carry,
                                );
                                carry = fa::adc(&mut r[10usize + 1], 0, carry);
                                let mut carry2 = 0;
                                let k = r[0usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[0usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[1usize] = fa::mac_with_carry(
                                    r[1usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 0usize], carry, carry2);
                                let k = r[1usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[1usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[2usize] = fa::mac_with_carry(
                                    r[2usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 1usize], carry, carry2);
                                let k = r[2usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[2usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[3usize] = fa::mac_with_carry(
                                    r[3usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 2usize], carry, carry2);
                                let k = r[3usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[3usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[4usize] = fa::mac_with_carry(
                                    r[4usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[8usize] = fa::mac_with_carry(
                                    r[8usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 3usize], carry, carry2);
                                let k = r[4usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[4usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[5usize] = fa::mac_with_carry(
                                    r[5usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[8usize] = fa::mac_with_carry(
                                    r[8usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[9usize] = fa::mac_with_carry(
                                    r[9usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 4usize], carry, carry2);
                                let k = r[5usize].wrapping_mul(Self::INV);
                                let mut carry = 0;
                                fa::mac_discard(
                                    r[5usize],
                                    k,
                                    13402431016077863595u64,
                                    &mut carry,
                                );
                                r[6usize] = fa::mac_with_carry(
                                    r[6usize],
                                    k,
                                    2210141511517208575u64,
                                    &mut carry,
                                );
                                r[7usize] = fa::mac_with_carry(
                                    r[7usize],
                                    k,
                                    7435674573564081700u64,
                                    &mut carry,
                                );
                                r[8usize] = fa::mac_with_carry(
                                    r[8usize],
                                    k,
                                    7239337960414712511u64,
                                    &mut carry,
                                );
                                r[9usize] = fa::mac_with_carry(
                                    r[9usize],
                                    k,
                                    5412103778470702295u64,
                                    &mut carry,
                                );
                                r[10usize] = fa::mac_with_carry(
                                    r[10usize],
                                    k,
                                    1873798617647539866u64,
                                    &mut carry,
                                );
                                carry2 = fa::adc(&mut r[6usize + 5usize], carry, carry2);
                                (a.0).0 = r[6usize..].try_into().unwrap();
                            }
                        }
                    }
                    __subtract_modulus(a);
                }
                fn sum_of_products<const M: usize>(a: &[F; M], b: &[F; M]) -> F {
                    if M <= 5usize {
                        let result = (0..6usize)
                            .fold(
                                BigInt::zero(),
                                |mut result, j| {
                                    let mut carry_a = 0;
                                    let mut carry_b = 0;
                                    for (a, b) in a.iter().zip(b) {
                                        let a = &a.0;
                                        let b = &b.0;
                                        let mut carry2 = 0;
                                        result
                                            .0[0] = fa::mac(result.0[0], a.0[j], b.0[0], &mut carry2);
                                        result
                                            .0[1usize] = fa::mac_with_carry(
                                            result.0[1usize],
                                            a.0[j],
                                            b.0[1usize],
                                            &mut carry2,
                                        );
                                        result
                                            .0[2usize] = fa::mac_with_carry(
                                            result.0[2usize],
                                            a.0[j],
                                            b.0[2usize],
                                            &mut carry2,
                                        );
                                        result
                                            .0[3usize] = fa::mac_with_carry(
                                            result.0[3usize],
                                            a.0[j],
                                            b.0[3usize],
                                            &mut carry2,
                                        );
                                        result
                                            .0[4usize] = fa::mac_with_carry(
                                            result.0[4usize],
                                            a.0[j],
                                            b.0[4usize],
                                            &mut carry2,
                                        );
                                        result
                                            .0[5usize] = fa::mac_with_carry(
                                            result.0[5usize],
                                            a.0[j],
                                            b.0[5usize],
                                            &mut carry2,
                                        );
                                        carry_b = fa::adc(&mut carry_a, carry_b, carry2);
                                    }
                                    let k = result.0[0].wrapping_mul(Self::INV);
                                    let mut carry2 = 0;
                                    fa::mac_discard(
                                        result.0[0],
                                        k,
                                        13402431016077863595u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[1usize
                                        - 1] = fa::mac_with_carry(
                                        result.0[1usize],
                                        k,
                                        2210141511517208575u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[2usize
                                        - 1] = fa::mac_with_carry(
                                        result.0[2usize],
                                        k,
                                        7435674573564081700u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[3usize
                                        - 1] = fa::mac_with_carry(
                                        result.0[3usize],
                                        k,
                                        7239337960414712511u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[4usize
                                        - 1] = fa::mac_with_carry(
                                        result.0[4usize],
                                        k,
                                        5412103778470702295u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[5usize
                                        - 1] = fa::mac_with_carry(
                                        result.0[5usize],
                                        k,
                                        1873798617647539866u64,
                                        &mut carry2,
                                    );
                                    result
                                        .0[6usize
                                        - 1] = fa::adc_no_carry(carry_a, carry_b, &mut carry2);
                                    result
                                },
                            );
                        let mut result = F::new_unchecked(result);
                        __subtract_modulus(&mut result);
                        if true {
                            match (
                                &a.iter().zip(b).map(|(a, b)| *a * b).sum::<F>(),
                                &result,
                            ) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        result
                    } else {
                        a.chunks(5usize)
                            .zip(b.chunks(5usize))
                            .map(|(a, b)| {
                                if a.len() == 5usize {
                                    Self::sum_of_products::<
                                        5usize,
                                    >(a.try_into().unwrap(), b.try_into().unwrap())
                                } else {
                                    a.iter().zip(b).map(|(a, b)| *a * b).sum()
                                }
                            })
                            .sum()
                    }
                }
            }
            #[inline(always)]
            fn __subtract_modulus(a: &mut F) {
                if a.is_geq_modulus() {
                    __sub_with_borrow(
                        &mut a.0,
                        &BigInt([
                            13402431016077863595u64,
                            2210141511517208575u64,
                            7435674573564081700u64,
                            7239337960414712511u64,
                            5412103778470702295u64,
                            1873798617647539866u64,
                        ]),
                    );
                }
            }
            #[inline(always)]
            fn __subtract_modulus_with_carry(a: &mut F, carry: bool) {
                if a.is_geq_modulus() || carry {
                    __sub_with_borrow(
                        &mut a.0,
                        &BigInt([
                            13402431016077863595u64,
                            2210141511517208575u64,
                            7435674573564081700u64,
                            7239337960414712511u64,
                            5412103778470702295u64,
                            1873798617647539866u64,
                        ]),
                    );
                }
            }
            #[inline(always)]
            fn __add_with_carry(a: &mut B, b: &B) -> bool {
                use ark_ff::biginteger::arithmetic::adc_for_add_with_carry as adc;
                let mut carry = 0;
                carry = adc(&mut a.0[0usize], b.0[0usize], carry);
                carry = adc(&mut a.0[1usize], b.0[1usize], carry);
                carry = adc(&mut a.0[2usize], b.0[2usize], carry);
                carry = adc(&mut a.0[3usize], b.0[3usize], carry);
                carry = adc(&mut a.0[4usize], b.0[4usize], carry);
                carry = adc(&mut a.0[5usize], b.0[5usize], carry);
                carry != 0
            }
            #[inline(always)]
            fn __sub_with_borrow(a: &mut B, b: &B) -> bool {
                use ark_ff::biginteger::arithmetic::sbb_for_sub_with_borrow as sbb;
                let mut borrow = 0;
                borrow = sbb(&mut a.0[0usize], b.0[0usize], borrow);
                borrow = sbb(&mut a.0[1usize], b.0[1usize], borrow);
                borrow = sbb(&mut a.0[2usize], b.0[2usize], borrow);
                borrow = sbb(&mut a.0[3usize], b.0[3usize], borrow);
                borrow = sbb(&mut a.0[4usize], b.0[4usize], borrow);
                borrow = sbb(&mut a.0[5usize], b.0[5usize], borrow);
                borrow != 0
            }
        }
        pub type Fq = Fp384<MontBackend<FqConfig, 6>>;
        pub const FQ_ONE: Fq = {
            let (is_positive, limbs) = (true, [1u64]);
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        pub const FQ_ZERO: Fq = {
            let (is_positive, limbs) = (true, [0u64]);
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        #[cfg(test)]
        mod tests {
            use core::marker::PhantomData;
            use super::*;
            use ark_ff::{BigInt, FpConfig, One};
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::fq::tests::test_constants"]
            pub const test_constants: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::fq::tests::test_constants"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_constants())),
            };
            fn test_constants() {
                use ark_ff::{MontConfig, PrimeField};
                match (&Fq::MODULUS_BIT_SIZE, &381) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&FqConfig::INV, &0x89f3fffcfffcfffd) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &FqConfig::R,
                    &BigInt::<
                        6,
                    >([
                        0x760900000002fffd,
                        0xebf4000bc40c0002,
                        0x5f48985753c758ba,
                        0x77ce585370525745,
                        0x5c071a97a256ec6d,
                        0x15f65ec3fa80e493,
                    ]),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &FqConfig::R2,
                    &BigInt::<
                        6,
                    >([
                        0xf4df1f341c341746,
                        0xa76e6a609d104f1,
                        0x8de5476c4c95b6d5,
                        0x67eb88a9939d83c0,
                        0x9a793e85b519952d,
                        0x11988fe592cae3aa,
                    ]),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &Fq::TRACE,
                    &BigInt::<
                        6,
                    >([
                        0xdcff7fffffffd555,
                        0xf55ffff58a9ffff,
                        0xb39869507b587b12,
                        0xb23ba5c279c2895f,
                        0x258dd3db21a5d66b,
                        0xd0088f51cbff34d,
                    ]),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &Fq::MODULUS_MINUS_ONE_DIV_TWO,
                    &BigInt::<
                        6,
                    >([
                        0xdcff7fffffffd555,
                        0xf55ffff58a9ffff,
                        0xb39869507b587b12,
                        0xb23ba5c279c2895f,
                        0x258dd3db21a5d66b,
                        0xd0088f51cbff34d,
                    ]),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &Fq::TRACE_MINUS_ONE_DIV_TWO,
                    &BigInt::<
                        6,
                    >([
                        0xee7fbfffffffeaaa,
                        0x7aaffffac54ffff,
                        0xd9cc34a83dac3d89,
                        0xd91dd2e13ce144af,
                        0x92c6e9ed90d2eb35,
                        0x680447a8e5ff9a6,
                    ]),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (
                    &FqConfig::GENERATOR,
                    &ark_ff::Fp(
                        BigInt::new([
                            0x321300000006554f,
                            0xb93c0018d6c40005,
                            0x57605e0db0ddbb51,
                            0x8b256521ed1f9bcb,
                            0x6cf28d7901622c03,
                            0x11ebab9dbb81e28c,
                        ]),
                        PhantomData,
                    ),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&FQ_ONE, &Fq::one()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&FQ_ONE, &<MontBackend<FqConfig, 6>>::ONE) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod fq12 {
        use crate::bls12_381::*;
        use ark_ff::{fields::*, MontFp};
        pub type Fq12 = Fp12<Fq12Config>;
        pub struct Fq12Config;
        #[automatically_derived]
        impl ::core::clone::Clone for Fq12Config {
            #[inline]
            fn clone(&self) -> Fq12Config {
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Fq12Config {}
        impl Fp12Config for Fq12Config {
            type Fp6Config = Fq6Config;
            const NONRESIDUE: Fq6 = Fq6::new(FQ2_ZERO, FQ2_ONE, FQ2_ZERO);
            const FROBENIUS_COEFF_FP12_C1: &'static [Fq2] = &[
                Fp2::new(
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10162220747404304312u64,
                                17761815663483519293u64,
                                8873291758750579140u64,
                                1141103941765652303u64,
                                13993175198059990303u64,
                                1802798568193066599u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3240210268673559283u64,
                                2895069921743240898u64,
                                17009126888523054175u64,
                                6098234018649060207u64,
                                9865672654120263608u64,
                                71000049454473266u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040831u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                17433006465011670690u64,
                                3478017852528130570u64,
                                17237919592439788638u64,
                                2035044123721977696u64,
                                16350815739277094105u64,
                                1392179521213474446u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                14416168624775744521u64,
                                17178867732698629620u64,
                                8644499054833844677u64,
                                5204293836692734814u64,
                                7508032112903159806u64,
                                481619096434065419u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040830u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                2226472659975678357u64,
                                6373087774271371469u64,
                                15800302407253291197u64,
                                8133278142371037904u64,
                                7769744319687806097u64,
                                1463179570667947713u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                11175958356102185238u64,
                                14283797810955388722u64,
                                10082116240020342118u64,
                                17552803891753226222u64,
                                16089103532492447813u64,
                                410619046979592152u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (false, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3240210268673559283u64,
                                2895069921743240898u64,
                                17009126888523054175u64,
                                6098234018649060207u64,
                                9865672654120263608u64,
                                71000049454473266u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10162220747404304312u64,
                                17761815663483519293u64,
                                8873291758750579140u64,
                                1141103941765652303u64,
                                13993175198059990303u64,
                                1802798568193066599u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822764u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                14416168624775744521u64,
                                17178867732698629620u64,
                                8644499054833844677u64,
                                5204293836692734814u64,
                                7508032112903159806u64,
                                481619096434065419u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                17433006465011670690u64,
                                3478017852528130570u64,
                                17237919592439788638u64,
                                2035044123721977696u64,
                                16350815739277094105u64,
                                1392179521213474446u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822765u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fp2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                11175958356102185238u64,
                                14283797810955388722u64,
                                10082116240020342118u64,
                                17552803891753226222u64,
                                16089103532492447813u64,
                                410619046979592152u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                2226472659975678357u64,
                                6373087774271371469u64,
                                15800302407253291197u64,
                                8133278142371037904u64,
                                7769744319687806097u64,
                                1463179570667947713u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ];
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod fq2 {
        use crate::bls12_381::*;
        use ark_ff::{fields::*, MontFp};
        pub type Fq2 = Fp2<Fq2Config>;
        pub struct Fq2Config;
        impl Fp2Config for Fq2Config {
            type Fp = Fq;
            /// NONRESIDUE = -1
            #[rustfmt::skip]
            const NONRESIDUE: Fq = {
                let (is_positive, limbs) = (false, [1u64]);
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            /// Coefficients for the Frobenius automorphism.
            #[rustfmt::skip]
            const FROBENIUS_COEFF_FP2_C1: &'static [Fq] = &[
                {
                    let (is_positive, limbs) = (true, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (false, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            ];
            #[inline(always)]
            fn mul_fp_by_nonresidue_in_place(fp: &mut Self::Fp) -> &mut Self::Fp {
                fp.neg_in_place()
            }
            #[inline(always)]
            fn mul_fp_by_nonresidue_and_add(y: &mut Self::Fp, x: &Self::Fp) {
                y.neg_in_place();
                *y += x;
            }
            #[inline(always)]
            fn mul_fp_by_nonresidue_plus_one_and_add(y: &mut Self::Fp, x: &Self::Fp) {
                *y = *x;
            }
            #[inline(always)]
            fn sub_and_mul_fp_by_nonresidue(y: &mut Self::Fp, x: &Self::Fp) {
                *y += x;
            }
        }
        pub const FQ2_ZERO: Fq2 = Fq2::new(FQ_ZERO, FQ_ZERO);
        pub const FQ2_ONE: Fq2 = Fq2::new(FQ_ONE, FQ_ZERO);
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod fq6 {
        use crate::bls12_381::*;
        use ark_ff::{fields::*, MontFp};
        pub type Fq6 = Fp6<Fq6Config>;
        pub struct Fq6Config;
        #[automatically_derived]
        impl ::core::clone::Clone for Fq6Config {
            #[inline]
            fn clone(&self) -> Fq6Config {
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Fq6Config {}
        impl Fp6Config for Fq6Config {
            type Fp2Config = Fq2Config;
            /// NONRESIDUE = (U + 1)
            const NONRESIDUE: Fq2 = Fq2::new(
                {
                    let (is_positive, limbs) = (true, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (true, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            );
            #[rustfmt::skip]
            const FROBENIUS_COEFF_FP6_C1: &'static [Fq2] = &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822764u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040830u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822764u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040830u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ];
            #[rustfmt::skip]
            const FROBENIUS_COEFF_FP6_C2: &'static [Fq2] = &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822765u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10087218740379822764u64,
                                4653388206581612541u64,
                                9907120269317136283u64,
                                12253596935368579796u64,
                                17006226088849104517u64,
                                1873798617647539865u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (false, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040830u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                3315212275698040831u64,
                                16003497378645147650u64,
                                15975298377956497032u64,
                                13432485098755684330u64,
                                6852621763331149393u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ];
            /// Multiply this element by the quadratic nonresidue 1 + u.
            /// Make this generic.
            fn mul_fp2_by_nonresidue_in_place(fe: &mut Fq2) -> &mut Fq2 {
                let t0 = fe.c0;
                fe.c0 -= &fe.c1;
                fe.c1 += &t0;
                fe
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod g1 {
        use crate::bls12_381::*;
        use ark_ec::{
            hashing::curve_maps::wb::{IsogenyMap, WBConfig},
            models::CurveConfig, short_weierstrass::{self, *},
        };
        use ark_ff::{MontFp, Zero};
        pub type G1Affine = Affine<Config>;
        pub type G1Projective = Projective<Config>;
        pub struct Config;
        #[automatically_derived]
        impl ::core::clone::Clone for Config {
            #[inline]
            fn clone(&self) -> Config {
                Config
            }
        }
        #[automatically_derived]
        impl ::core::default::Default for Config {
            #[inline]
            fn default() -> Config {
                Config {}
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for Config {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for Config {
            #[inline]
            fn eq(&self, other: &Config) -> bool {
                true
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralEq for Config {}
        #[automatically_derived]
        impl ::core::cmp::Eq for Config {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl CurveConfig for Config {
            type BaseField = Fq;
            type ScalarField = Fr;
            /// COFACTOR = (x - 1)^2 / 3  = 76329603384216526031706109802092473003
            const COFACTOR: &'static [u64] = &[0x8c00aaab0000aaab, 0x396c8c005555e156];
            /// COFACTOR_INV = COFACTOR^{-1} mod r
            /// = 52435875175126190458656871551744051925719901746859129887267498875565241663483
            #[rustfmt::skip]
            const COFACTOR_INV: Fr = {
                let (is_positive, limbs) = (
                    true,
                    [
                        17005592201541320699u64,
                        15023040749026494473u64,
                        16379322676018133793u64,
                        8353516859464449348u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
        }
        impl short_weierstrass::SWCurveConfig for Config {
            /// COEFF_A = 0
            const COEFF_A: Fq = {
                let (is_positive, limbs) = (true, [0u64]);
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            /// COEFF_B = 4
            #[rustfmt::skip]
            const COEFF_B: Fq = {
                let (is_positive, limbs) = (true, [4u64]);
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
            const GENERATOR: G1Affine = G1Affine::new_unchecked(
                G1_GENERATOR_X,
                G1_GENERATOR_Y,
            );
            #[inline(always)]
            fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
                Self::BaseField::zero()
            }
            #[inline]
            fn clear_cofactor(p: &G1Affine) -> G1Affine {
                let h_eff: &[u64] = &[0xd201000000010001];
                Config::mul_affine(p, h_eff).into()
            }
        }
        impl WBConfig for Config {
            type IsogenousCurve = g1_swu_iso::SwuIsoConfig;
            const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self> = g1_swu_iso::ISOGENY_MAP_TO_G1;
        }
        /// G1_GENERATOR_X =
        /// 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
        #[rustfmt::skip]
        pub const G1_GENERATOR_X: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    18103045581585958587u64,
                    7806400890582735599u64,
                    11623291730934869080u64,
                    14080658508445169925u64,
                    2780237799254240271u64,
                    1725392847304644500u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        /// G1_GENERATOR_Y =
        /// 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569
        #[rustfmt::skip]
        pub const G1_GENERATOR_Y: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    912580534683953121u64,
                    15005087156090211044u64,
                    61670280795567085u64,
                    18227722000993880822u64,
                    11573741888802228964u64,
                    627113611842199793u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        #[cfg(test)]
        mod test {
            use super::*;
            use ark_ec::CurveGroup;
            use ark_std::UniformRand;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::g1::test::batch_normalization"]
            pub const batch_normalization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::g1::test::batch_normalization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    batch_normalization(),
                )),
            };
            fn batch_normalization() {
                let mut rng = ark_std::test_rng();
                let mut g_s = [G1Projective::zero(); 100];
                for i in 0..100 {
                    g_s[i] = G1Projective::rand(&mut rng);
                }
                let mut g_s_affine_naive = [G1Affine::identity(); 100];
                for (i, g) in g_s.iter().enumerate() {
                    g_s_affine_naive[i] = g.into_affine();
                }
                let g_s_affine_fast = G1Projective::normalize_batch(&g_s);
                match (&g_s_affine_naive.as_ref(), &g_s_affine_fast.as_slice()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod g1_swu_iso {
        use crate::bls12_381::*;
        use ark_ec::{
            hashing::curve_maps::{swu::SWUConfig, wb::IsogenyMap},
            models::{
                short_weierstrass::{Affine, SWCurveConfig},
                CurveConfig,
            },
        };
        use ark_ff::MontFp;
        type G1Affine = Affine<SwuIsoConfig>;
        pub struct SwuIsoConfig;
        #[automatically_derived]
        impl ::core::clone::Clone for SwuIsoConfig {
            #[inline]
            fn clone(&self) -> SwuIsoConfig {
                SwuIsoConfig
            }
        }
        #[automatically_derived]
        impl ::core::default::Default for SwuIsoConfig {
            #[inline]
            fn default() -> SwuIsoConfig {
                SwuIsoConfig {}
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for SwuIsoConfig {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for SwuIsoConfig {
            #[inline]
            fn eq(&self, other: &SwuIsoConfig) -> bool {
                true
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralEq for SwuIsoConfig {}
        #[automatically_derived]
        impl ::core::cmp::Eq for SwuIsoConfig {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl CurveConfig for SwuIsoConfig {
            type BaseField = Fq;
            type ScalarField = Fr;
            /// COFACTOR = (x - 1)^2 / 3  = 76329603384216526031706109802092473003
            const COFACTOR: &'static [u64] = &[0x8c00aaab0000aaab, 0x396c8c005555e156];
            /// COFACTOR_INV = COFACTOR^{-1} mod r
            /// = 52435875175126190458656871551744051925719901746859129887267498875565241663483
            #[rustfmt::skip]
            const COFACTOR_INV: Fr = {
                let (is_positive, limbs) = (
                    true,
                    [
                        17005592201541320699u64,
                        15023040749026494473u64,
                        16379322676018133793u64,
                        8353516859464449348u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
        }
        impl SWCurveConfig for SwuIsoConfig {
            const COEFF_A: Fq = {
                let (is_positive, limbs) = (
                    true,
                    [
                        6698022561392380957u64,
                        10994253769421683071u64,
                        15629909748249821612u64,
                        12748169179688756904u64,
                        4425131892511951234u64,
                        5707120929990979u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            #[rustfmt::skip]
            const COEFF_B: Fq = {
                let (is_positive, limbs) = (
                    true,
                    [
                        15117538217124375520u64,
                        6495071758858381989u64,
                        11581500465278574325u64,
                        2312248699302920304u64,
                        111203405409480251u64,
                        1360808972976160816u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            const GENERATOR: G1Affine = G1Affine::new_unchecked(
                G1_GENERATOR_X,
                G1_GENERATOR_Y,
            );
        }
        /// Lexicographically smallest, valid x-coordinate of a point P on the curve (with its corresponding y) multiplied by the cofactor.
        /// P_x = 2
        /// P_y = 658522096176515125667361255350269797307718222519385801637008089782287711363858559738763090642304321670226247205569
        /// P = E(P_x, P_y)
        /// G = P * COFACTOR
        const G1_GENERATOR_X: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    15712601745595139539u64,
                    15629851001509372639u64,
                    16843629557626034441u64,
                    15035185667047981839u64,
                    2695840349023996032u64,
                    785312167295077746u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        const G1_GENERATOR_Y: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    8285371724728395211u64,
                    6266748553944385227u64,
                    15612735626375763941u64,
                    3809655030962639295u64,
                    778042012541862486u64,
                    657821437089064656u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        impl SWUConfig for SwuIsoConfig {
            const ZETA: Fq = {
                let (is_positive, limbs) = (true, [11u64]);
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
        }
        pub const ISOGENY_MAP_TO_G1: IsogenyMap<'_, SwuIsoConfig, g1::Config> = IsogenyMap {
            x_map_numerator: &[
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            12586459670690286007u64,
                            6201670911048166766u64,
                            17465657917644792520u64,
                            7723742117508874335u64,
                            13261148298159854981u64,
                            1270119733718627136u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            16732261237459223483u64,
                            5204176168283587414u64,
                            17682789360670468203u64,
                            8941869963990959127u64,
                            398773841247578140u64,
                            1668951808976071471u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            16147550488514976944u64,
                            10776056440809943711u64,
                            7528018573573808732u64,
                            14844748873776858085u64,
                            2094253841180170779u64,
                            960393023080265964u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            14245880009877842017u64,
                            5996228842464768403u64,
                            17416319752018800771u64,
                            15561595211679121189u64,
                            5622191986793862162u64,
                            1691355743628586423u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            5842660658088809945u64,
                            10978131499682789316u64,
                            607681821319080984u64,
                            11086623519836470079u64,
                            7368650625050054228u64,
                            1051997788391994435u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            14777367860349315459u64,
                            11567228658253249817u64,
                            11444679715590672272u64,
                            15797696746983946651u64,
                            130921168661596853u64,
                            1598992431623377919u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            15985511645807504772u64,
                            10205808941053849290u64,
                            10378793938173061930u64,
                            12760252618317466849u64,
                            7653628713030275775u64,
                            967946631563726121u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            11298218755092433038u64,
                            4159013751748851119u64,
                            11998370262181639475u64,
                            3849985779734105521u64,
                            16750075057192140371u64,
                            1709149555065084898u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            7886252005760951063u64,
                            5738313744366653077u64,
                            11728946595272970718u64,
                            14140024565662700916u64,
                            8903813505199544589u64,
                            580186936973955012u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            9161465579737517214u64,
                            11752436998487615353u64,
                            7449821001803307903u64,
                            15937899882900905113u64,
                            3318087848058654498u64,
                            1628930385436977092u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            14584871380308065147u64,
                            17769927732099571180u64,
                            15351349873550116966u64,
                            18049808134997311382u64,
                            8275623842221021965u64,
                            1167027828517898210u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            12234233096825917993u64,
                            14000314106239596831u64,
                            2576269112800734056u64,
                            3591512392926246844u64,
                            13627494601717575229u64,
                            495550047642324592u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            ],
            x_map_denominator: &[
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            11041975239630265116u64,
                            13067430171545714168u64,
                            11283074393783708770u64,
                            132274872219551930u64,
                            1779737893574802031u64,
                            633474091881273774u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            16557527386785790975u64,
                            1430641118356186857u64,
                            82967328719421271u64,
                            8089002360232247308u64,
                            5238936591227237942u64,
                            1321272531362356291u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            18213183315621985817u64,
                            15466434890074226396u64,
                            18205324308570099372u64,
                            8037026956533927121u64,
                            9311163821600184607u64,
                            804282852993868382u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            1373009181854280920u64,
                            5293652763671852484u64,
                            6110444250091843536u64,
                            6559532710647391569u64,
                            14428037799351479124u64,
                            234844145893171966u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            6025034940388909598u64,
                            11228207967368476701u64,
                            10190314345946351322u64,
                            18437674587247370939u64,
                            751851957792514173u64,
                            1416629893867312296u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            13847998906088228005u64,
                            8358912131254619921u64,
                            739642499118176303u64,
                            4131830461445745997u64,
                            6140956605115975401u64,
                            1041270466333271993u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            17016134625831438906u64,
                            16894043798660571244u64,
                            5633448088282521244u64,
                            6273329123533496713u64,
                            1098328982230230817u64,
                            536714149743900185u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            1294742680819751518u64,
                            1127511003250156243u64,
                            1843909372225399896u64,
                            7962192351555381416u64,
                            3509418672874520985u64,
                            1488347500898461874u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            5149562959837648449u64,
                            252877309218538352u64,
                            8363199516777220149u64,
                            16176803544133875307u64,
                            6814521545734988748u64,
                            725340084226051970u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            3270603789344496906u64,
                            10599026333335446784u64,
                            8565656522589412373u64,
                            17762958817130696759u64,
                            5146891164735334016u64,
                            675470927100193492u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (true, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            ],
            y_map_numerator: &[
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            13733803417833814835u64,
                            14775319642720936898u64,
                            3121750372618945491u64,
                            1273695771440998738u64,
                            2710356675495255290u64,
                            652344406751465184u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            16183658160488302230u64,
                            15475889019760388287u64,
                            1121505450578652468u64,
                            1307144967559264317u64,
                            15352831428748068483u64,
                            1389807578337138705u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            13321614990632673782u64,
                            15162865775551710499u64,
                            14070580367580990887u64,
                            2689461337731570914u64,
                            17628079362768849300u64,
                            57553299067792998u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            11976580453200426187u64,
                            16014900032503684588u64,
                            712874875091754233u64,
                            15288216298323671324u64,
                            8689824239172478807u64,
                            141972750621744161u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            4735212769449148123u64,
                            3379943669301788840u64,
                            8755912272271186652u64,
                            1825425679455244472u64,
                            6678644607214234052u64,
                            633886036738506515u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            11074978966450447856u64,
                            2323684950984523890u64,
                            8525415512662168654u64,
                            8405916841409361853u64,
                            2454990789666711200u64,
                            1612358804494830442u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            14511152726087948018u64,
                            5163511947597922654u64,
                            5922586712221110071u64,
                            16671121624101127371u64,
                            12882959944969186108u64,
                            336375361001233340u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            11627815551290637097u64,
                            4825120264949852469u64,
                            18231571463891878950u64,
                            1660145734357211167u64,
                            16039894141796533876u64,
                            686738286210365551u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            6933025920263103879u64,
                            7626373186594408355u64,
                            2200974244968450750u64,
                            10320769399998235244u64,
                            16756942182913253819u64,
                            719520515476580427u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            3147922594245844016u64,
                            11186783513499056751u64,
                            475233659467912251u64,
                            14135124294293452542u64,
                            2466492548686891555u64,
                            1016611174344998325u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            16722834201330696498u64,
                            3584647998681889532u64,
                            15066861003931772432u64,
                            14785260176242854207u64,
                            1007974600900082579u64,
                            1833315000454533566u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            14846055306840460686u64,
                            5321510883028162054u64,
                            3345046972101780530u64,
                            5923739534552515142u64,
                            13337622794239929804u64,
                            1780164921828767454u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            958146249756188408u64,
                            488730451382505970u64,
                            13846054168121598783u64,
                            8838227588559581326u64,
                            15083972834952036164u64,
                            799438051374502809u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            4817114329354076467u64,
                            14325828012864645732u64,
                            1433942577299613084u64,
                            8465424830341846400u64,
                            8285498163857659356u64,
                            163716820423854747u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            9685868895687483979u64,
                            7755485098777620407u64,
                            15684647020317539556u64,
                            6802473390048830824u64,
                            189531577938912252u64,
                            414658151749832465u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            338991247778166276u64,
                            13142913832013798519u64,
                            6317940024988860850u64,
                            14634479491382401593u64,
                            5666948055268535989u64,
                            1578157964224562126u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            ],
            y_map_denominator: &[
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            92203205520679873u64,
                            572916540828819565u64,
                            17204633670617869946u64,
                            6924968209373727718u64,
                            5915497081334721257u64,
                            1590100849350973618u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            3672140328108400701u64,
                            8693114993904885301u64,
                            11862766565471805471u64,
                            9640042925497046428u64,
                            1877083417397643448u64,
                            1829261189398470686u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            2172204746352322546u64,
                            11994630442058346377u64,
                            879791671491744492u64,
                            8702226981475745585u64,
                            8046435537999802711u64,
                            400243331105348135u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            12164906044230685718u64,
                            8247046336453711789u64,
                            1314387578457599809u64,
                            15066165676546511630u64,
                            17441636237435581649u64,
                            1637008473169220501u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            15724621714793234461u64,
                            11676450493790612973u64,
                            6066025509460822294u64,
                            14326404096614579120u64,
                            12685735333705453020u64,
                            855930740911588324u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            199925847119476652u64,
                            5328758613570342114u64,
                            14262012144631372388u64,
                            13186912195705886849u64,
                            11507373155986977154u64,
                            637792788410719021u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            4402853133867972444u64,
                            15418807805142572985u64,
                            6760859324815900753u64,
                            6840121186619029743u64,
                            14103733843373163083u64,
                            1612297190139091759u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            6984591927261867737u64,
                            13339932232668798692u64,
                            18353100669930795314u64,
                            16547411811928854487u64,
                            269334146695233390u64,
                            1631410310868805610u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            7720081932193848650u64,
                            5967237584920922243u64,
                            12377427846571989832u64,
                            18013005311323887904u64,
                            1881349400343039172u64,
                            1758313625630302499u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            3778226018344582997u64,
                            14355327869992416094u64,
                            5983130161189999867u64,
                            3609344159736760251u64,
                            16898074901591262352u64,
                            1619701357752249884u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            70004379462101672u64,
                            8189165486932690436u64,
                            1033887512062764488u64,
                            11271894388753671721u64,
                            5255719044972187933u64,
                            347606589330687421u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            10845992994110574738u64,
                            1655469341950262250u64,
                            10092455202333888821u64,
                            9193253711563866834u64,
                            17691595219776375879u64,
                            778202887894139711u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            2204988348113831372u64,
                            10592474449179118273u64,
                            9033357708497886086u64,
                            6067271023149908518u64,
                            14078588081290548374u64,
                            781015344221683683u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            15130647872920159991u64,
                            4757234684169342080u64,
                            14660498759553796110u64,
                            13787308004332873665u64,
                            7101012286790006514u64,
                            172830037692534587u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (
                        true,
                        [
                            4905905684016745359u64,
                            6675167463148394368u64,
                            3625112747029342752u64,
                            8197694151986493523u64,
                            7720336747103001025u64,
                            1013206390650290238u64,
                        ],
                    );
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (true, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            ],
        };
        #[cfg(test)]
        mod test {
            use super::*;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::g1_swu_iso::test::test_gen"]
            pub const test_gen: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::g1_swu_iso::test::test_gen"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_gen())),
            };
            fn test_gen() {
                let gen: G1Affine = SwuIsoConfig::GENERATOR;
                if !gen.is_on_curve() {
                    ::core::panicking::panic("assertion failed: gen.is_on_curve()")
                }
                if !gen.is_in_correct_subgroup_assuming_on_curve() {
                    ::core::panicking::panic(
                        "assertion failed: gen.is_in_correct_subgroup_assuming_on_curve()",
                    )
                }
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod g2 {
        use core::ops::Neg;
        use crate::bls12_381::*;
        use ark_ec::{
            bls12::{self, Bls12Config},
            hashing::curve_maps::wb::{IsogenyMap, WBConfig},
            models::CurveConfig, short_weierstrass::{self, *},
            AffineRepr, CurveGroup, Group,
        };
        use ark_ff::{BigInt, Field, MontFp, Zero};
        pub type G2Affine = bls12::G2Affine<crate::bls12_381::Config>;
        pub type G2Projective = bls12::G2Projective<crate::bls12_381::Config>;
        pub struct Config;
        #[automatically_derived]
        impl ::core::clone::Clone for Config {
            #[inline]
            fn clone(&self) -> Config {
                Config
            }
        }
        #[automatically_derived]
        impl ::core::default::Default for Config {
            #[inline]
            fn default() -> Config {
                Config {}
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for Config {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for Config {
            #[inline]
            fn eq(&self, other: &Config) -> bool {
                true
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralEq for Config {}
        #[automatically_derived]
        impl ::core::cmp::Eq for Config {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl CurveConfig for Config {
            type BaseField = Fq2;
            type ScalarField = Fr;
            /// COFACTOR = (x^8 - 4 x^7 + 5 x^6) - (4 x^4 + 6 x^3 - 4 x^2 - 4 x + 13) //
            /// 9
            /// = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041616661285803823378372096355777062779109
            #[rustfmt::skip]
            const COFACTOR: &'static [u64] = &[
                0xcf1c38e31c7238e5,
                0x1616ec6e786f0c70,
                0x21537e293a6691ae,
                0xa628f1cb4d9e82ef,
                0xa68a205b2e5a7ddf,
                0xcd91de4547085aba,
                0x91d50792876a202,
                0x5d543a95414e7f1,
            ];
            /// COFACTOR_INV = COFACTOR^{-1} mod r
            /// 26652489039290660355457965112010883481355318854675681319708643586776743290055
            #[rustfmt::skip]
            const COFACTOR_INV: Fr = {
                let (is_positive, limbs) = (
                    true,
                    [
                        17479440281642183u64,
                        7893276552997957004u64,
                        3449160833254235888u64,
                        4245986470004029505u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
        }
        impl short_weierstrass::SWCurveConfig for Config {
            /// COEFF_A = [0, 0]
            const COEFF_A: Fq2 = Fq2::new(g1::Config::COEFF_A, g1::Config::COEFF_A);
            /// COEFF_B = [4, 4]
            const COEFF_B: Fq2 = Fq2::new(g1::Config::COEFF_B, g1::Config::COEFF_B);
            /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
            const GENERATOR: G2Affine = G2Affine::new_unchecked(
                G2_GENERATOR_X,
                G2_GENERATOR_Y,
            );
            #[inline(always)]
            fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
                Self::BaseField::zero()
            }
            fn is_in_correct_subgroup_assuming_on_curve(point: &G2Affine) -> bool {
                let mut x_times_point = point
                    .mul_bigint(BigInt::new([crate::bls12_381::Config::X[0], 0, 0, 0]));
                if crate::bls12_381::Config::X_IS_NEGATIVE {
                    x_times_point = -x_times_point;
                }
                let p_times_point = p_power_endomorphism(point);
                x_times_point.eq(&p_times_point)
            }
            #[inline]
            fn clear_cofactor(p: &G2Affine) -> G2Affine {
                let x: &'static [u64] = crate::bls12_381::Config::X;
                let p_projective = p.into_group();
                let x_p = Config::mul_affine(p, x).neg();
                let psi_p = p_power_endomorphism(p);
                let mut psi2_p2 = double_p_power_endomorphism(&p_projective.double());
                let tmp = (x_p + psi_p).mul_bigint(x).neg();
                psi2_p2 += tmp;
                psi2_p2 -= x_p;
                psi2_p2 -= psi_p;
                (psi2_p2 - p_projective).into_affine()
            }
        }
        pub const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
        pub const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);
        /// G2_GENERATOR_X_C0 =
        /// 352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160
        #[rustfmt::skip]
        pub const G2_GENERATOR_X_C0: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    15312334153293348280u64,
                    841050694974028783u64,
                    12993178926126977399u64,
                    14331714969349929730u64,
                    2740446039084699729u64,
                    165123225776229009u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        /// G2_GENERATOR_X_C1 =
        /// 3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758
        #[rustfmt::skip]
        pub const G2_GENERATOR_X_C1: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    16549740192668593022u64,
                    3696594454104530263u64,
                    13103893525273989193u64,
                    6443473286224459290u64,
                    9055845637167730533u64,
                    1432192374203850592u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        /// G2_GENERATOR_Y_C0 =
        /// 1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905
        #[rustfmt::skip]
        pub const G2_GENERATOR_Y_C0: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    16254428414758889473u64,
                    10536956157198377609u64,
                    7873024875724591404u64,
                    12537348094477325223u64,
                    10144865889576432922u64,
                    929383263523139089u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        /// G2_GENERATOR_Y_C1 =
        /// 927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582
        #[rustfmt::skip]
        pub const G2_GENERATOR_Y_C1: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    12297368366147926462u64,
                    4555124010822409633u64,
                    2771000935339432363u64,
                    14645187562128761775u64,
                    3651525051980876697u64,
                    434250606344352972u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        pub const P_POWER_ENDOMORPHISM_COEFF_0: Fq2 = Fq2::new(
            FQ_ZERO,
            {
                let (is_positive, limbs) = (
                    true,
                    [
                        10087218740379822765u64,
                        4653388206581612541u64,
                        9907120269317136283u64,
                        12253596935368579796u64,
                        17006226088849104517u64,
                        1873798617647539865u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            },
        );
        pub const P_POWER_ENDOMORPHISM_COEFF_1: Fq2 = Fq2::new(
            {
                let (is_positive, limbs) = (
                    true,
                    [
                        17433006465011670690u64,
                        3478017852528130570u64,
                        17237919592439788638u64,
                        2035044123721977696u64,
                        16350815739277094105u64,
                        1392179521213474446u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            },
            {
                let (is_positive, limbs) = (
                    true,
                    [
                        14416168624775744521u64,
                        17178867732698629620u64,
                        8644499054833844677u64,
                        5204293836692734814u64,
                        7508032112903159806u64,
                        481619096434065419u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            },
        );
        pub const DOUBLE_P_POWER_ENDOMORPHISM: Fq2 = Fq2::new(
            {
                let (is_positive, limbs) = (
                    true,
                    [
                        10087218740379822764u64,
                        4653388206581612541u64,
                        9907120269317136283u64,
                        12253596935368579796u64,
                        17006226088849104517u64,
                        1873798617647539865u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            },
            FQ_ZERO,
        );
        pub fn p_power_endomorphism(p: &Affine<Config>) -> Affine<Config> {
            let mut res = *p;
            res.x.frobenius_map_in_place(1);
            res.y.frobenius_map_in_place(1);
            let tmp_x = res.x;
            res.x.c0 = -P_POWER_ENDOMORPHISM_COEFF_0.c1 * tmp_x.c1;
            res.x.c1 = P_POWER_ENDOMORPHISM_COEFF_0.c1 * tmp_x.c0;
            res.y *= P_POWER_ENDOMORPHISM_COEFF_1;
            res
        }
        /// For a p-power endomorphism psi(P), compute psi(psi(P))
        pub fn double_p_power_endomorphism(
            p: &Projective<Config>,
        ) -> Projective<Config> {
            let mut res = *p;
            res.x *= DOUBLE_P_POWER_ENDOMORPHISM;
            res.y = res.y.neg();
            res
        }
        impl WBConfig for Config {
            type IsogenousCurve = g2_swu_iso::SwuIsoConfig;
            const ISOGENY_MAP: IsogenyMap<'static, Self::IsogenousCurve, Self> = g2_swu_iso::ISOGENY_MAP_TO_G2;
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub mod g2_swu_iso {
        use crate::bls12_381::*;
        use ark_ec::models::{
            short_weierstrass::{Affine, SWCurveConfig},
            CurveConfig,
        };
        use ark_ff::MontFp;
        use ark_ec::hashing::curve_maps::{swu::SWUConfig, wb::IsogenyMap};
        type G2Affine = Affine<SwuIsoConfig>;
        pub struct SwuIsoConfig;
        #[automatically_derived]
        impl ::core::clone::Clone for SwuIsoConfig {
            #[inline]
            fn clone(&self) -> SwuIsoConfig {
                SwuIsoConfig
            }
        }
        #[automatically_derived]
        impl ::core::default::Default for SwuIsoConfig {
            #[inline]
            fn default() -> SwuIsoConfig {
                SwuIsoConfig {}
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for SwuIsoConfig {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for SwuIsoConfig {
            #[inline]
            fn eq(&self, other: &SwuIsoConfig) -> bool {
                true
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralEq for SwuIsoConfig {}
        #[automatically_derived]
        impl ::core::cmp::Eq for SwuIsoConfig {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl CurveConfig for SwuIsoConfig {
            type BaseField = Fq2;
            type ScalarField = Fr;
            /// Cofactors of g2_iso and g2 are the same.
            /// COFACTOR = (x^8 - 4 x^7 + 5 x^6) - (4 x^4 + 6 x^3 - 4 x^2 - 4 x + 13) //
            /// 9
            /// = 305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041616661285803823378372096355777062779109
            #[rustfmt::skip]
            const COFACTOR: &'static [u64] = &[
                0xcf1c38e31c7238e5,
                0x1616ec6e786f0c70,
                0x21537e293a6691ae,
                0xa628f1cb4d9e82ef,
                0xa68a205b2e5a7ddf,
                0xcd91de4547085aba,
                0x91d50792876a202,
                0x5d543a95414e7f1,
            ];
            /// COFACTOR_INV = COFACTOR^{-1} mod r
            /// 26652489039290660355457965112010883481355318854675681319708643586776743290055
            #[rustfmt::skip]
            const COFACTOR_INV: Fr = {
                let (is_positive, limbs) = (
                    true,
                    [
                        17479440281642183u64,
                        7893276552997957004u64,
                        3449160833254235888u64,
                        4245986470004029505u64,
                    ],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
        }
        impl SWCurveConfig for SwuIsoConfig {
            /// COEFF_A = 240 * I
            const COEFF_A: Fq2 = Fq2::new(
                {
                    let (is_positive, limbs) = (true, [0u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (true, [240u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            );
            /// COEFF_B = 1012 + 1012 * I
            const COEFF_B: Fq2 = Fq2::new(
                {
                    let (is_positive, limbs) = (true, [1012u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (true, [1012u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            );
            const GENERATOR: G2Affine = G2Affine::new_unchecked(
                G2_GENERATOR_X,
                G2_GENERATOR_Y,
            );
        }
        /// Lexicographically smallest, valid x-coordinate of a point P on the curve (with its corresponding y) multiplied by the cofactor.
        /// P_x = 1
        /// P_y = 1199519624119946820355795551601605892701128025883245860600494152840508171012839086684258857614063467038089173303263 + 2721622435888802346851223931977585460571674503470326381323808470905804676865417627238564067834747838523978879375704 * I
        /// P = E(P_x, P_y)
        /// G = P * COFACTOR
        const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
        const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);
        const G2_GENERATOR_X_C0: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    16362777407992059015u64,
                    15478464648306213675u64,
                    3497634215687360179u64,
                    10153790186688219934u64,
                    10988752493757311976u64,
                    1215161844648256360u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        const G2_GENERATOR_X_C1: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    12005242627502122392u64,
                    4059737409871022482u64,
                    12691396078736696508u64,
                    5292328760141556539u64,
                    769331904981887046u64,
                    485527169012262540u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        const G2_GENERATOR_Y_C0: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    5720144688094217335u64,
                    16892628323551108676u64,
                    10262410448551172993u64,
                    5310659745561372478u64,
                    16635923103749358706u64,
                    1838929453661769524u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        const G2_GENERATOR_Y_C1: Fq = {
            let (is_positive, limbs) = (
                true,
                [
                    4803496152605443641u64,
                    4564440014637889682u64,
                    1875990686668238752u64,
                    14418541646378570479u64,
                    103036193697627975u64,
                    1545105968736681190u64,
                ],
            );
            ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
        };
        impl SWUConfig for SwuIsoConfig {
            const ZETA: Fq2 = Fq2::new(
                {
                    let (is_positive, limbs) = (false, [2u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
                {
                    let (is_positive, limbs) = (false, [1u64]);
                    ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                },
            );
        }
        pub const ISOGENY_MAP_TO_G2: IsogenyMap<'_, SwuIsoConfig, g2::Config> = IsogenyMap {
            x_map_numerator: &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                7077594464397203414u64,
                                6640057249351452444u64,
                                9850925049107374429u64,
                                3658379999393219626u64,
                                13500519111022079365u64,
                                416399692810564414u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                7077594464397203414u64,
                                6640057249351452444u64,
                                9850925049107374429u64,
                                3658379999393219626u64,
                                13500519111022079365u64,
                                416399692810564414u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                2786039319482058522u64,
                                1473427674344805717u64,
                                11106031073612571672u64,
                                10975139998179658879u64,
                                3608069185647134863u64,
                                1249199078431693244u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                2786039319482058526u64,
                                1473427674344805717u64,
                                11106031073612571672u64,
                                10975139998179658879u64,
                                3608069185647134863u64,
                                1249199078431693244u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10616391696595805069u64,
                                736713837172402858u64,
                                14776387573661061644u64,
                                14710942035944605247u64,
                                1804034592823567431u64,
                                624599539215846622u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                9863633783879261905u64,
                                8113484923696258161u64,
                                2510212049010394485u64,
                                14633519997572878506u64,
                                17108588296669214228u64,
                                1665598771242257658u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ],
            x_map_denominator: &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863523u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [12u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863583u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ],
            y_map_numerator: &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                1355520937843676934u64,
                                18197961889718808424u64,
                                17673314439684154624u64,
                                1116230615302104219u64,
                                6459500568425337235u64,
                                1526798873638736187u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                1355520937843676934u64,
                                18197961889718808424u64,
                                17673314439684154624u64,
                                1116230615302104219u64,
                                6459500568425337235u64,
                                1526798873638736187u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                7077594464397203390u64,
                                6640057249351452444u64,
                                9850925049107374429u64,
                                3658379999393219626u64,
                                13500519111022079365u64,
                                416399692810564414u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                2786039319482058524u64,
                                1473427674344805717u64,
                                11106031073612571672u64,
                                10975139998179658879u64,
                                3608069185647134863u64,
                                1249199078431693244u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                10616391696595805071u64,
                                736713837172402858u64,
                                14776387573661061644u64,
                                14710942035944605247u64,
                                1804034592823567431u64,
                                624599539215846622u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                16263467779354626832u64,
                                5654561228188306393u64,
                                12747851915130467410u64,
                                8510412652460270214u64,
                                18155985086623849168u64,
                                1318599027233453979u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ],
            y_map_denominator: &[
                Fq2::new(
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863163u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863163u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863379u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [18u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (
                            true,
                            [
                                13402431016077863577u64,
                                2210141511517208575u64,
                                7435674573564081700u64,
                                7239337960414712511u64,
                                5412103778470702295u64,
                                1873798617647539866u64,
                            ],
                        );
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
                Fq2::new(
                    {
                        let (is_positive, limbs) = (true, [1u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                    {
                        let (is_positive, limbs) = (true, [0u64]);
                        ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
                    },
                ),
            ],
        };
        #[cfg(test)]
        mod test {
            use super::*;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::g2_swu_iso::test::test_gen"]
            pub const test_gen: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::g2_swu_iso::test::test_gen"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_gen())),
            };
            fn test_gen() {
                let gen: G2Affine = g2_swu_iso::SwuIsoConfig::GENERATOR;
                if !gen.is_on_curve() {
                    ::core::panicking::panic("assertion failed: gen.is_on_curve()")
                }
                if !gen.is_in_correct_subgroup_assuming_on_curve() {
                    ::core::panicking::panic(
                        "assertion failed: gen.is_in_correct_subgroup_assuming_on_curve()",
                    )
                }
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub use {fq::*, fq12::*, fq2::*, fq6::*, g1::*, g1_swu_iso::*, g2::*, g2_swu_iso::*};
    #[cfg(test)]
    mod tests {
        use crate::bls12_381::*;
        use ark_algebra_test_templates::*;
        mod fr {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fr::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fr>::characteristic();
                let max_power = (<Fr>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fr>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fr>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fr as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fr>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fr>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fr>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fr>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fr>::deserialize_with_mode(&mut cursor, compress, validate)
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fr>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fr>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fr>::ZERO.is_zero()")
                }
                match (&<Fr>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fr>::rand(&mut rng);
                    let b = <Fr>::rand(&mut rng);
                    let c = <Fr>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fr>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fr>::rand(&mut rng);
                    let b = <Fr>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fr>::zero();
                let one = <Fr>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fr>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fr>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fr>::rand(&mut rng);
                    let b = <Fr>::rand(&mut rng);
                    let c = <Fr>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fr::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fr>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fr>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fr>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fr>::extension_degree() {
                        result = result.pow(<Fr>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fr,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fr::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fr>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fr>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fr>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fr>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fr>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_fft"]
            pub const test_fft: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fr::test_fft"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_fft())),
            };
            fn test_fft() {
                use ark_ff::FftField;
                match (
                    &<Fr>::TWO_ADIC_ROOT_OF_UNITY.pow([1 << <Fr>::TWO_ADICITY]),
                    &<Fr>::one(),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(small_subgroup_base) = <Fr>::SMALL_SUBGROUP_BASE {
                    let small_subgroup_base_adicity = <Fr>::SMALL_SUBGROUP_BASE_ADICITY
                        .unwrap();
                    let large_subgroup_root_of_unity = <Fr>::LARGE_SUBGROUP_ROOT_OF_UNITY
                        .unwrap();
                    let pow = (1 << <Fr>::TWO_ADICITY)
                        * (small_subgroup_base as u64).pow(small_subgroup_base_adicity);
                    match (&large_subgroup_root_of_unity.pow([pow]), &<Fr>::one()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    for i in 0..=<Fr>::TWO_ADICITY {
                        for j in 0..=small_subgroup_base_adicity {
                            let size = (1u64 << i) * (small_subgroup_base as u64).pow(j);
                            let root = <Fr>::get_root_of_unity(size as u64).unwrap();
                            match (&root.pow([size as u64]), &<Fr>::one()) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                } else {
                    for i in 0..=<Fr>::TWO_ADICITY {
                        let size = 1 << i;
                        let root = <Fr>::get_root_of_unity(size).unwrap();
                        match (&root.pow([size as u64]), &<Fr>::one()) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_sum_of_products_edge_case"]
            pub const test_sum_of_products_edge_case: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_sum_of_products_edge_case",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_edge_case(),
                )),
            };
            fn test_sum_of_products_edge_case() {
                use ark_ff::BigInteger;
                let mut a_max = <Fr>::ZERO.into_bigint();
                for (i, limb) in a_max.as_mut().iter_mut().enumerate() {
                    if i == <Fr as PrimeField>::BigInt::NUM_LIMBS - 1 {
                        let mod_num_bits_mod_64 = 64
                            * <Fr as PrimeField>::BigInt::NUM_LIMBS
                            - (<Fr as PrimeField>::MODULUS_BIT_SIZE as usize);
                        if mod_num_bits_mod_64 == 63 {
                            *limb = 0u64;
                        } else {
                            *limb = u64::MAX >> (mod_num_bits_mod_64 + 1);
                        }
                    } else {
                        *limb = u64::MAX;
                    }
                }
                let a_max = <Fr>::from_bigint(a_max).unwrap();
                let b_max = -<Fr>::one();
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    1,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    2,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    3,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    4,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    5,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    6,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    7,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    8,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    9,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    10,
                >(a_max, b_max);
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_constants"]
            pub const test_constants: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fr::test_constants"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_constants())),
            };
            fn test_constants() {
                use ark_ff::{FpConfig, BigInteger, SqrtPrecomputation};
                use ::ark_algebra_test_templates::num_bigint::BigUint;
                use ::ark_algebra_test_templates::num_integer::Integer;
                let modulus: BigUint = <Fr>::MODULUS.into();
                let modulus_minus_one = &modulus - 1u8;
                match (
                    &BigUint::from(<Fr>::MODULUS_MINUS_ONE_DIV_TWO),
                    &(&modulus_minus_one / 2u32),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&(<Fr>::MODULUS_BIT_SIZE as u64), &modulus.bits()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(SqrtPrecomputation::Case3Mod4 { modulus_plus_one_div_four })
                    = <Fr>::SQRT_PRECOMP {
                    let check = ((&modulus + 1u8) / 4u8).to_u64_digits();
                    let len = check.len();
                    match (&&modulus_plus_one_div_four[..len], &&check) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    if !modulus_plus_one_div_four[len..].iter().all(|l| *l == 0) {
                        ::core::panicking::panic(
                            "assertion failed: modulus_plus_one_div_four[len..].iter().all(|l| *l == 0)",
                        )
                    }
                }
                let mut two_adicity = 0;
                let mut trace = modulus_minus_one;
                while trace.is_even() {
                    trace /= 2u8;
                    two_adicity += 1;
                }
                match (&two_adicity, &<Fr>::TWO_ADICITY) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&BigUint::from(<Fr>::TRACE), &trace) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let trace_minus_one_div_two = (&trace - 1u8) / 2u8;
                match (
                    &BigUint::from(<Fr>::TRACE_MINUS_ONE_DIV_TWO),
                    &trace_minus_one_div_two,
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let two_adic_root_of_unity: BigUint = <Fr>::TWO_ADIC_ROOT_OF_UNITY
                    .into();
                let generator: BigUint = <Fr>::GENERATOR.into_bigint().into();
                match (&two_adic_root_of_unity, &generator.modpow(&trace, &modulus)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (<Fr>::SMALL_SUBGROUP_BASE, <Fr>::SMALL_SUBGROUP_BASE_ADICITY) {
                    (Some(base), Some(adicity)) => {
                        let mut e = generator;
                        for _i in 0..adicity {
                            e = e.modpow(&base.into(), &modulus);
                        }
                    }
                    (None, None) => {}
                    (_, _) => {
                        ::core::panicking::panic_fmt(
                            ::core::fmt::Arguments::new_v1(
                                &[
                                    "Should specify both `SMALL_SUBGROUP_BASE` and `SMALL_SUBGROUP_BASE_ADICITY`",
                                ],
                                &[],
                            ),
                        )
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fr::test_montgomery_config"]
            pub const test_montgomery_config: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fr::test_montgomery_config",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_montgomery_config(),
                )),
            };
            pub fn test_montgomery_config() {
                use ark_ff::{FpConfig, BigInteger};
                use ::ark_algebra_test_templates::num_bigint::{BigUint, BigInt};
                use ::ark_algebra_test_templates::num_integer::Integer;
                use ::ark_algebra_test_templates::num_traits::{
                    Signed, cast::ToPrimitive,
                };
                let limbs = <Fr as PrimeField>::BigInt::NUM_LIMBS;
                let modulus: BigUint = <Fr>::MODULUS.into();
                let r = BigUint::from(2u8)
                    .modpow(&((limbs * 64) as u64).into(), &modulus);
                let r2 = (&r * &r) % &modulus;
                let inv = {
                    let mut inv = 1u128;
                    let two_to_64 = 1u128 << 64;
                    for _ in 0..63 {
                        inv = inv.checked_mul(inv).unwrap() % two_to_64;
                        inv = inv.checked_mul(<Fr>::MODULUS.0[0] as u128).unwrap()
                            % &two_to_64;
                    }
                    let mut inv = inv as i128;
                    let two_to_64 = two_to_64 as i128;
                    inv = (-inv) % two_to_64;
                    inv as u64
                };
                let group_order = 0b111111111111111111111111111111111111111111111111111111111111111u64;
                let group_order_lower = ((group_order << 32) >> 32) as u32;
                let group_order_upper = ((group_order) >> 32) as u32;
                let modulus_lower_limb = <Fr>::MODULUS.0[0];
                let modulus_lower_limb_to2_32 = modulus_lower_limb
                    .wrapping_pow(u32::MAX)
                    .wrapping_mul(modulus_lower_limb);
                let inv2 = modulus_lower_limb
                    .wrapping_pow(group_order_lower)
                    .wrapping_mul(
                        modulus_lower_limb_to2_32.wrapping_pow(group_order_upper),
                    )
                    .wrapping_neg();
                match (&r, &<Fr>::R.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&r2, &<Fr>::R2.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv, &u64::from(<Fr>::INV)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv2, &<Fr>::INV) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
            }
        }
        mod fq {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fq>::characteristic();
                let max_power = (<Fq>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fq>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fq>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fq as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fq>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fq>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fq>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fq>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fq>::deserialize_with_mode(&mut cursor, compress, validate)
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fq>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fq>::ZERO.is_zero()")
                }
                match (&<Fq>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    let c = <Fq>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                let one = <Fq>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fq>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fq>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    let c = <Fq>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fq>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fq>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fq>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fq>::extension_degree() {
                        result = result.pow(<Fq>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fq>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fq>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fq>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fq>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fq>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_fft"]
            pub const test_fft: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq::test_fft"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_fft())),
            };
            fn test_fft() {
                use ark_ff::FftField;
                match (
                    &<Fq>::TWO_ADIC_ROOT_OF_UNITY.pow([1 << <Fq>::TWO_ADICITY]),
                    &<Fq>::one(),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(small_subgroup_base) = <Fq>::SMALL_SUBGROUP_BASE {
                    let small_subgroup_base_adicity = <Fq>::SMALL_SUBGROUP_BASE_ADICITY
                        .unwrap();
                    let large_subgroup_root_of_unity = <Fq>::LARGE_SUBGROUP_ROOT_OF_UNITY
                        .unwrap();
                    let pow = (1 << <Fq>::TWO_ADICITY)
                        * (small_subgroup_base as u64).pow(small_subgroup_base_adicity);
                    match (&large_subgroup_root_of_unity.pow([pow]), &<Fq>::one()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    for i in 0..=<Fq>::TWO_ADICITY {
                        for j in 0..=small_subgroup_base_adicity {
                            let size = (1u64 << i) * (small_subgroup_base as u64).pow(j);
                            let root = <Fq>::get_root_of_unity(size as u64).unwrap();
                            match (&root.pow([size as u64]), &<Fq>::one()) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                } else {
                    for i in 0..=<Fq>::TWO_ADICITY {
                        let size = 1 << i;
                        let root = <Fq>::get_root_of_unity(size).unwrap();
                        match (&root.pow([size as u64]), &<Fq>::one()) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_sum_of_products_edge_case"]
            pub const test_sum_of_products_edge_case: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_sum_of_products_edge_case",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_edge_case(),
                )),
            };
            fn test_sum_of_products_edge_case() {
                use ark_ff::BigInteger;
                let mut a_max = <Fq>::ZERO.into_bigint();
                for (i, limb) in a_max.as_mut().iter_mut().enumerate() {
                    if i == <Fq as PrimeField>::BigInt::NUM_LIMBS - 1 {
                        let mod_num_bits_mod_64 = 64
                            * <Fq as PrimeField>::BigInt::NUM_LIMBS
                            - (<Fq as PrimeField>::MODULUS_BIT_SIZE as usize);
                        if mod_num_bits_mod_64 == 63 {
                            *limb = 0u64;
                        } else {
                            *limb = u64::MAX >> (mod_num_bits_mod_64 + 1);
                        }
                    } else {
                        *limb = u64::MAX;
                    }
                }
                let a_max = <Fq>::from_bigint(a_max).unwrap();
                let b_max = -<Fq>::one();
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    1,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    2,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    3,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    4,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    5,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    6,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    7,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    8,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    9,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    10,
                >(a_max, b_max);
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_constants"]
            pub const test_constants: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq::test_constants"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_constants())),
            };
            fn test_constants() {
                use ark_ff::{FpConfig, BigInteger, SqrtPrecomputation};
                use ::ark_algebra_test_templates::num_bigint::BigUint;
                use ::ark_algebra_test_templates::num_integer::Integer;
                let modulus: BigUint = <Fq>::MODULUS.into();
                let modulus_minus_one = &modulus - 1u8;
                match (
                    &BigUint::from(<Fq>::MODULUS_MINUS_ONE_DIV_TWO),
                    &(&modulus_minus_one / 2u32),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&(<Fq>::MODULUS_BIT_SIZE as u64), &modulus.bits()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(SqrtPrecomputation::Case3Mod4 { modulus_plus_one_div_four })
                    = <Fq>::SQRT_PRECOMP {
                    let check = ((&modulus + 1u8) / 4u8).to_u64_digits();
                    let len = check.len();
                    match (&&modulus_plus_one_div_four[..len], &&check) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    if !modulus_plus_one_div_four[len..].iter().all(|l| *l == 0) {
                        ::core::panicking::panic(
                            "assertion failed: modulus_plus_one_div_four[len..].iter().all(|l| *l == 0)",
                        )
                    }
                }
                let mut two_adicity = 0;
                let mut trace = modulus_minus_one;
                while trace.is_even() {
                    trace /= 2u8;
                    two_adicity += 1;
                }
                match (&two_adicity, &<Fq>::TWO_ADICITY) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&BigUint::from(<Fq>::TRACE), &trace) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let trace_minus_one_div_two = (&trace - 1u8) / 2u8;
                match (
                    &BigUint::from(<Fq>::TRACE_MINUS_ONE_DIV_TWO),
                    &trace_minus_one_div_two,
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let two_adic_root_of_unity: BigUint = <Fq>::TWO_ADIC_ROOT_OF_UNITY
                    .into();
                let generator: BigUint = <Fq>::GENERATOR.into_bigint().into();
                match (&two_adic_root_of_unity, &generator.modpow(&trace, &modulus)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (<Fq>::SMALL_SUBGROUP_BASE, <Fq>::SMALL_SUBGROUP_BASE_ADICITY) {
                    (Some(base), Some(adicity)) => {
                        let mut e = generator;
                        for _i in 0..adicity {
                            e = e.modpow(&base.into(), &modulus);
                        }
                    }
                    (None, None) => {}
                    (_, _) => {
                        ::core::panicking::panic_fmt(
                            ::core::fmt::Arguments::new_v1(
                                &[
                                    "Should specify both `SMALL_SUBGROUP_BASE` and `SMALL_SUBGROUP_BASE_ADICITY`",
                                ],
                                &[],
                            ),
                        )
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq::test_montgomery_config"]
            pub const test_montgomery_config: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq::test_montgomery_config",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_montgomery_config(),
                )),
            };
            pub fn test_montgomery_config() {
                use ark_ff::{FpConfig, BigInteger};
                use ::ark_algebra_test_templates::num_bigint::{BigUint, BigInt};
                use ::ark_algebra_test_templates::num_integer::Integer;
                use ::ark_algebra_test_templates::num_traits::{
                    Signed, cast::ToPrimitive,
                };
                let limbs = <Fq as PrimeField>::BigInt::NUM_LIMBS;
                let modulus: BigUint = <Fq>::MODULUS.into();
                let r = BigUint::from(2u8)
                    .modpow(&((limbs * 64) as u64).into(), &modulus);
                let r2 = (&r * &r) % &modulus;
                let inv = {
                    let mut inv = 1u128;
                    let two_to_64 = 1u128 << 64;
                    for _ in 0..63 {
                        inv = inv.checked_mul(inv).unwrap() % two_to_64;
                        inv = inv.checked_mul(<Fq>::MODULUS.0[0] as u128).unwrap()
                            % &two_to_64;
                    }
                    let mut inv = inv as i128;
                    let two_to_64 = two_to_64 as i128;
                    inv = (-inv) % two_to_64;
                    inv as u64
                };
                let group_order = 0b111111111111111111111111111111111111111111111111111111111111111u64;
                let group_order_lower = ((group_order << 32) >> 32) as u32;
                let group_order_upper = ((group_order) >> 32) as u32;
                let modulus_lower_limb = <Fq>::MODULUS.0[0];
                let modulus_lower_limb_to2_32 = modulus_lower_limb
                    .wrapping_pow(u32::MAX)
                    .wrapping_mul(modulus_lower_limb);
                let inv2 = modulus_lower_limb
                    .wrapping_pow(group_order_lower)
                    .wrapping_mul(
                        modulus_lower_limb_to2_32.wrapping_pow(group_order_upper),
                    )
                    .wrapping_neg();
                match (&r, &<Fq>::R.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&r2, &<Fq>::R2.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv, &u64::from(<Fq>::INV)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv2, &<Fq>::INV) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
            }
        }
        mod fq2 {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq2::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fq2>::characteristic();
                let max_power = (<Fq2>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fq2>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq2::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fq2>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fq2 as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fq2>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fq2>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fq2>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fq2>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fq2>::deserialize_with_mode(
                                            &mut cursor,
                                            compress,
                                            validate,
                                        )
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq2::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq2>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fq2>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fq2>::ZERO.is_zero()")
                }
                match (&<Fq2>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq2>::rand(&mut rng);
                    let b = <Fq2>::rand(&mut rng);
                    let c = <Fq2>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq2::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq2>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq2>::rand(&mut rng);
                    let b = <Fq2>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq2::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq2>::zero();
                let one = <Fq2>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fq2>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fq2>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fq2>::rand(&mut rng);
                    let b = <Fq2>::rand(&mut rng);
                    let c = <Fq2>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq2::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fq2>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fq2>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fq2>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fq2>::extension_degree() {
                        result = result.pow(<Fq2>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq2::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq2,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq2::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq2::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fq2>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fq2>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fq2>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fq2>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fq2>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
        }
        mod fq6 {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq6::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fq6>::characteristic();
                let max_power = (<Fq6>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fq6>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq6::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fq6>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fq6 as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fq6>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fq6>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fq6>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fq6>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fq6>::deserialize_with_mode(
                                            &mut cursor,
                                            compress,
                                            validate,
                                        )
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq6::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq6>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fq6>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fq6>::ZERO.is_zero()")
                }
                match (&<Fq6>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq6>::rand(&mut rng);
                    let b = <Fq6>::rand(&mut rng);
                    let c = <Fq6>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq6::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq6>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq6>::rand(&mut rng);
                    let b = <Fq6>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq6::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq6>::zero();
                let one = <Fq6>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fq6>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fq6>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fq6>::rand(&mut rng);
                    let b = <Fq6>::rand(&mut rng);
                    let c = <Fq6>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq6::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fq6>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fq6>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fq6>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fq6>::extension_degree() {
                        result = result.pow(<Fq6>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq6::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq6,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq6::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq6::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fq6>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fq6>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fq6>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fq6>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fq6>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
        }
        mod fq12 {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq12::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fq12>::characteristic();
                let max_power = (<Fq12>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fq12>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq12::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fq12>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fq12 as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fq12>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fq12>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fq12>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fq12>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fq12>::deserialize_with_mode(
                                            &mut cursor,
                                            compress,
                                            validate,
                                        )
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq12::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq12>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fq12>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fq12>::ZERO.is_zero()")
                }
                match (&<Fq12>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq12>::rand(&mut rng);
                    let b = <Fq12>::rand(&mut rng);
                    let c = <Fq12>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq12::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq12>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq12>::rand(&mut rng);
                    let b = <Fq12>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq12::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq12>::zero();
                let one = <Fq12>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fq12>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fq12>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fq12>::rand(&mut rng);
                    let b = <Fq12>::rand(&mut rng);
                    let c = <Fq12>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq12::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fq12>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fq12>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fq12>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fq12>::extension_degree() {
                        result = result.pow(<Fq12>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::fq12::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq12,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::fq12::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::fq12::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fq12>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fq12>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fq12>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fq12>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fq12>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
        }
        mod g1 {
            use super::*;
            use ark_ff::*;
            use ark_ec::{
                Group, CurveGroup, ScalarMul, AffineRepr, CurveConfig,
                short_weierstrass::SWCurveConfig, twisted_edwards::TECurveConfig,
                scalar_mul::{*, wnaf::*},
            };
            use ark_serialize::*;
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 500;
            type ScalarField = <G1Projective as Group>::ScalarField;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                let mut rng = &mut ark_std::test_rng();
                let zero = <G1Projective>::zero();
                for _ in 0..ITERATIONS {
                    let a = <G1Projective>::rand(rng);
                    let b = <G1Projective>::rand(rng);
                    let c = <G1Projective>::rand(rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b + zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(c + zero), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&zero.double(), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-zero).double(), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <G1Projective>::zero();
                for _ in 0..ITERATIONS {
                    let a = <G1Projective>::rand(&mut rng);
                    let b = <G1Projective>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = ScalarField::zero();
                let one = ScalarField::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic("assertion failed: one.is_one()")
                }
                for _ in 0..ITERATIONS {
                    let a = <G1Projective>::rand(&mut rng);
                    let b = ScalarField::rand(&mut rng);
                    let c = ScalarField::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * one), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * zero), &<G1Projective>::zero()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&((a * b.inverse().unwrap()) * b), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    for w in 2..=5 {
                        let context = WnafContext::new(w);
                        match (&(a * b), &context.mul(a, &b)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let table = context.table(a);
                        match (&(a * b), &context.mul_with_table(&table, &b).unwrap()) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        if w > 2 {
                            let bad_context = WnafContext::new(w - 1);
                            let bad_table = bad_context.table(a);
                            match (&context.mul_with_table(&bad_table, &b), &None) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <G1Projective>::zero().serialized_size(compress);
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <G1Projective>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <G1Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let a = <G1Projective>::zero();
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <G1Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let a = <G1Projective>::zero();
                                let mut serialized = ::alloc::vec::from_elem(
                                    0,
                                    buf_size - 1,
                                );
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                            }
                            {
                                let serialized = ::alloc::vec::from_elem(0, buf_size - 1);
                                let mut cursor = Cursor::new(&serialized[..]);
                                <G1Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap_err();
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_var_base_msm"]
            pub const test_var_base_msm: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_var_base_msm",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_var_base_msm(),
                )),
            };
            fn test_var_base_msm() {
                ::ark_algebra_test_templates::msm::test_var_base_msm::<G1Projective>();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_chunked_pippenger"]
            pub const test_chunked_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_chunked_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_chunked_pippenger(),
                )),
            };
            fn test_chunked_pippenger() {
                ::ark_algebra_test_templates::msm::test_chunked_pippenger::<
                    G1Projective,
                >();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_hashmap_pippenger"]
            pub const test_hashmap_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_hashmap_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_hashmap_pippenger(),
                )),
            };
            fn test_hashmap_pippenger() {
                ::ark_algebra_test_templates::msm::test_hashmap_pippenger::<
                    G1Projective,
                >();
            }
            type Affine = <G1Projective as CurveGroup>::Affine;
            type Config = <G1Projective as CurveGroup>::Config;
            type BaseField = <G1Projective as CurveGroup>::BaseField;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_affine_conversion"]
            pub const test_affine_conversion: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_affine_conversion",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_affine_conversion(),
                )),
            };
            fn test_affine_conversion() {
                let mut rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let g = <G1Projective>::rand(&mut rng);
                    let g_affine = g.into_affine();
                    let g_projective = g_affine.into_group();
                    match (&g, &g_projective) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
                for _ in 0..10 {
                    let mut v = (0..ITERATIONS)
                        .map(|_| <G1Projective>::rand(&mut rng).double())
                        .collect::<Vec<_>>();
                    use ark_std::rand::distributions::{Distribution, Uniform};
                    let between = Uniform::from(0..ITERATIONS);
                    for _ in 0..5 {
                        v[between.sample(&mut rng)] = <G1Projective>::zero();
                    }
                    for _ in 0..5 {
                        let s = between.sample(&mut rng);
                        v[s] = v[s].into_affine().into_group();
                    }
                    let expected_v = v
                        .iter()
                        .map(|v| v.into_affine())
                        .collect::<Vec<_>>();
                    let actual_v = <G1Projective>::normalize_batch(&v);
                    match (&actual_v, &expected_v) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_cofactor_ops"]
            pub const test_cofactor_ops: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_cofactor_ops",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_cofactor_ops(),
                )),
            };
            fn test_cofactor_ops() {
                let rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let a = Affine::rand(rng);
                    match (
                        &a.mul_by_cofactor_to_group(),
                        &a.mul_bigint(&Config::COFACTOR),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor(), &a.mul_bigint(&Config::COFACTOR)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor().mul_by_cofactor_inv(), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor_inv().mul_by_cofactor(), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor_inv(), &(a * Config::COFACTOR_INV)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    if !a.clear_cofactor().is_in_correct_subgroup_assuming_on_curve() {
                        ::core::panicking::panic(
                            "assertion failed: a.clear_cofactor().is_in_correct_subgroup_assuming_on_curve()",
                        )
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_mixed_addition"]
            pub const test_mixed_addition: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_mixed_addition",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mixed_addition(),
                )),
            };
            fn test_mixed_addition() {
                let rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let a = Affine::rand(rng);
                    let a_group = a.into_group();
                    let b = <G1Projective>::rand(rng);
                    if !a.is_on_curve() {
                        ::core::panicking::panic("assertion failed: a.is_on_curve()")
                    }
                    if !b.into_affine().is_on_curve() {
                        ::core::panicking::panic(
                            "assertion failed: b.into_affine().is_on_curve()",
                        )
                    }
                    match (&(b + a), &(b + a_group)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["b + a failed on input ", ", "],
                                            &[
                                                ::core::fmt::ArgumentV1::new_display(&a),
                                                ::core::fmt::ArgumentV1::new_display(&b),
                                            ],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a + b), &(a_group + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["a + b failed on input ", ", "],
                                            &[
                                                ::core::fmt::ArgumentV1::new_display(&a),
                                                ::core::fmt::ArgumentV1::new_display(&b),
                                            ],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1::test_sw_properties"]
            pub const test_sw_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g1::test_sw_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sw_properties(),
                )),
            };
            fn test_sw_properties() {
                let mut rng = &mut ark_std::test_rng();
                let generator = <G1Projective>::generator().into_affine();
                if !generator.is_on_curve() {
                    ::core::panicking::panic("assertion failed: generator.is_on_curve()")
                }
                if !generator.is_in_correct_subgroup_assuming_on_curve() {
                    ::core::panicking::panic(
                        "assertion failed: generator.is_in_correct_subgroup_assuming_on_curve()",
                    )
                }
                for i in 0.. {
                    let x = BaseField::from(i);
                    let rhs = x * x.square() + x * <Config as SWCurveConfig>::COEFF_A
                        + <Config as SWCurveConfig>::COEFF_B;
                    if let Some(y) = rhs.sqrt() {
                        let p = Affine::new_unchecked(x, if y < -y { y } else { -y });
                        if !<<G1Projective as CurveGroup>::Config as CurveConfig>::cofactor_is_one() {
                            if p.is_in_correct_subgroup_assuming_on_curve() {
                                continue;
                            }
                        }
                        let g1 = p.mul_by_cofactor_to_group();
                        if !g1.is_zero() {
                            let g1 = Affine::from(g1);
                            if !g1.is_in_correct_subgroup_assuming_on_curve() {
                                ::core::panicking::panic(
                                    "assertion failed: g1.is_in_correct_subgroup_assuming_on_curve()",
                                )
                            }
                            break;
                        }
                    }
                }
                for _ in 0..ITERATIONS {
                    let f = BaseField::rand(rng);
                    match (
                        &<Config as SWCurveConfig>::mul_by_a(f),
                        &(f * <Config as SWCurveConfig>::COEFF_A),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (
                        &<Config as SWCurveConfig>::add_b(f),
                        &(f + <Config as SWCurveConfig>::COEFF_B),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
                {
                    use ark_ec::models::short_weierstrass::SWFlags;
                    for compress in [Compress::Yes, Compress::No] {
                        for flag in [
                            SWFlags::PointAtInfinity,
                            SWFlags::YIsNegative,
                            SWFlags::YIsPositive,
                        ] {
                            let a = BaseField::rand(&mut rng);
                            let buf_size = a.serialized_size(compress);
                            let mut serialized = ::alloc::vec::from_elem(
                                0u8,
                                buf_size + 1,
                            );
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_flags(&mut cursor, flag).unwrap();
                            let mut cursor = Cursor::new(&serialized[..]);
                            let (b, flags) = BaseField::deserialize_with_flags::<
                                _,
                                SWFlags,
                            >(&mut cursor)
                                .unwrap();
                            match (&flags, &flag) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                }
            }
        }
        mod g2 {
            use super::*;
            use ark_ff::*;
            use ark_ec::{
                Group, CurveGroup, ScalarMul, AffineRepr, CurveConfig,
                short_weierstrass::SWCurveConfig, twisted_edwards::TECurveConfig,
                scalar_mul::{*, wnaf::*},
            };
            use ark_serialize::*;
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 500;
            type ScalarField = <G2Projective as Group>::ScalarField;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_add_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                let mut rng = &mut ark_std::test_rng();
                let zero = <G2Projective>::zero();
                for _ in 0..ITERATIONS {
                    let a = <G2Projective>::rand(rng);
                    let b = <G2Projective>::rand(rng);
                    let c = <G2Projective>::rand(rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b + zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(c + zero), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&zero.double(), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-zero).double(), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_sub_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <G2Projective>::zero();
                for _ in 0..ITERATIONS {
                    let a = <G2Projective>::rand(&mut rng);
                    let b = <G2Projective>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_mul_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = ScalarField::zero();
                let one = ScalarField::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic("assertion failed: one.is_one()")
                }
                for _ in 0..ITERATIONS {
                    let a = <G2Projective>::rand(&mut rng);
                    let b = ScalarField::rand(&mut rng);
                    let c = ScalarField::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * one), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * zero), &<G2Projective>::zero()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&((a * b.inverse().unwrap()) * b), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    for w in 2..=5 {
                        let context = WnafContext::new(w);
                        match (&(a * b), &context.mul(a, &b)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let table = context.table(a);
                        match (&(a * b), &context.mul_with_table(&table, &b).unwrap()) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        if w > 2 {
                            let bad_context = WnafContext::new(w - 1);
                            let bad_table = bad_context.table(a);
                            match (&context.mul_with_table(&bad_table, &b), &None) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_serialization",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <G2Projective>::zero().serialized_size(compress);
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <G2Projective>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <G2Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let a = <G2Projective>::zero();
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <G2Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let a = <G2Projective>::zero();
                                let mut serialized = ::alloc::vec::from_elem(
                                    0,
                                    buf_size - 1,
                                );
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                            }
                            {
                                let serialized = ::alloc::vec::from_elem(0, buf_size - 1);
                                let mut cursor = Cursor::new(&serialized[..]);
                                <G2Projective>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap_err();
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_var_base_msm"]
            pub const test_var_base_msm: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_var_base_msm",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_var_base_msm(),
                )),
            };
            fn test_var_base_msm() {
                ::ark_algebra_test_templates::msm::test_var_base_msm::<G2Projective>();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_chunked_pippenger"]
            pub const test_chunked_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_chunked_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_chunked_pippenger(),
                )),
            };
            fn test_chunked_pippenger() {
                ::ark_algebra_test_templates::msm::test_chunked_pippenger::<
                    G2Projective,
                >();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_hashmap_pippenger"]
            pub const test_hashmap_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_hashmap_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_hashmap_pippenger(),
                )),
            };
            fn test_hashmap_pippenger() {
                ::ark_algebra_test_templates::msm::test_hashmap_pippenger::<
                    G2Projective,
                >();
            }
            type Affine = <G2Projective as CurveGroup>::Affine;
            type Config = <G2Projective as CurveGroup>::Config;
            type BaseField = <G2Projective as CurveGroup>::BaseField;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_affine_conversion"]
            pub const test_affine_conversion: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_affine_conversion",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_affine_conversion(),
                )),
            };
            fn test_affine_conversion() {
                let mut rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let g = <G2Projective>::rand(&mut rng);
                    let g_affine = g.into_affine();
                    let g_projective = g_affine.into_group();
                    match (&g, &g_projective) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
                for _ in 0..10 {
                    let mut v = (0..ITERATIONS)
                        .map(|_| <G2Projective>::rand(&mut rng).double())
                        .collect::<Vec<_>>();
                    use ark_std::rand::distributions::{Distribution, Uniform};
                    let between = Uniform::from(0..ITERATIONS);
                    for _ in 0..5 {
                        v[between.sample(&mut rng)] = <G2Projective>::zero();
                    }
                    for _ in 0..5 {
                        let s = between.sample(&mut rng);
                        v[s] = v[s].into_affine().into_group();
                    }
                    let expected_v = v
                        .iter()
                        .map(|v| v.into_affine())
                        .collect::<Vec<_>>();
                    let actual_v = <G2Projective>::normalize_batch(&v);
                    match (&actual_v, &expected_v) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_cofactor_ops"]
            pub const test_cofactor_ops: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_cofactor_ops",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_cofactor_ops(),
                )),
            };
            fn test_cofactor_ops() {
                let rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let a = Affine::rand(rng);
                    match (
                        &a.mul_by_cofactor_to_group(),
                        &a.mul_bigint(&Config::COFACTOR),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor(), &a.mul_bigint(&Config::COFACTOR)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor().mul_by_cofactor_inv(), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor_inv().mul_by_cofactor(), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.mul_by_cofactor_inv(), &(a * Config::COFACTOR_INV)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    if !a.clear_cofactor().is_in_correct_subgroup_assuming_on_curve() {
                        ::core::panicking::panic(
                            "assertion failed: a.clear_cofactor().is_in_correct_subgroup_assuming_on_curve()",
                        )
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_mixed_addition"]
            pub const test_mixed_addition: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_mixed_addition",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mixed_addition(),
                )),
            };
            fn test_mixed_addition() {
                let rng = &mut ark_std::test_rng();
                for _ in 0..ITERATIONS {
                    let a = Affine::rand(rng);
                    let a_group = a.into_group();
                    let b = <G2Projective>::rand(rng);
                    if !a.is_on_curve() {
                        ::core::panicking::panic("assertion failed: a.is_on_curve()")
                    }
                    if !b.into_affine().is_on_curve() {
                        ::core::panicking::panic(
                            "assertion failed: b.into_affine().is_on_curve()",
                        )
                    }
                    match (&(b + a), &(b + a_group)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["b + a failed on input ", ", "],
                                            &[
                                                ::core::fmt::ArgumentV1::new_display(&a),
                                                ::core::fmt::ArgumentV1::new_display(&b),
                                            ],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a + b), &(a_group + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["a + b failed on input ", ", "],
                                            &[
                                                ::core::fmt::ArgumentV1::new_display(&a),
                                                ::core::fmt::ArgumentV1::new_display(&b),
                                            ],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2::test_sw_properties"]
            pub const test_sw_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::g2::test_sw_properties",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sw_properties(),
                )),
            };
            fn test_sw_properties() {
                let mut rng = &mut ark_std::test_rng();
                let generator = <G2Projective>::generator().into_affine();
                if !generator.is_on_curve() {
                    ::core::panicking::panic("assertion failed: generator.is_on_curve()")
                }
                if !generator.is_in_correct_subgroup_assuming_on_curve() {
                    ::core::panicking::panic(
                        "assertion failed: generator.is_in_correct_subgroup_assuming_on_curve()",
                    )
                }
                for i in 0.. {
                    let x = BaseField::from(i);
                    let rhs = x * x.square() + x * <Config as SWCurveConfig>::COEFF_A
                        + <Config as SWCurveConfig>::COEFF_B;
                    if let Some(y) = rhs.sqrt() {
                        let p = Affine::new_unchecked(x, if y < -y { y } else { -y });
                        if !<<G2Projective as CurveGroup>::Config as CurveConfig>::cofactor_is_one() {
                            if p.is_in_correct_subgroup_assuming_on_curve() {
                                continue;
                            }
                        }
                        let g1 = p.mul_by_cofactor_to_group();
                        if !g1.is_zero() {
                            let g1 = Affine::from(g1);
                            if !g1.is_in_correct_subgroup_assuming_on_curve() {
                                ::core::panicking::panic(
                                    "assertion failed: g1.is_in_correct_subgroup_assuming_on_curve()",
                                )
                            }
                            break;
                        }
                    }
                }
                for _ in 0..ITERATIONS {
                    let f = BaseField::rand(rng);
                    match (
                        &<Config as SWCurveConfig>::mul_by_a(f),
                        &(f * <Config as SWCurveConfig>::COEFF_A),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (
                        &<Config as SWCurveConfig>::add_b(f),
                        &(f + <Config as SWCurveConfig>::COEFF_B),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
                {
                    use ark_ec::models::short_weierstrass::SWFlags;
                    for compress in [Compress::Yes, Compress::No] {
                        for flag in [
                            SWFlags::PointAtInfinity,
                            SWFlags::YIsNegative,
                            SWFlags::YIsPositive,
                        ] {
                            let a = BaseField::rand(&mut rng);
                            let buf_size = a.serialized_size(compress);
                            let mut serialized = ::alloc::vec::from_elem(
                                0u8,
                                buf_size + 1,
                            );
                            let mut cursor = Cursor::new(&mut serialized[..]);
                            a.serialize_with_flags(&mut cursor, flag).unwrap();
                            let mut cursor = Cursor::new(&serialized[..]);
                            let (b, flags) = BaseField::deserialize_with_flags::<
                                _,
                                SWFlags,
                            >(&mut cursor)
                                .unwrap();
                            match (&flags, &flag) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                }
            }
        }
        mod pairing_output {
            use super::*;
            use ark_ff::*;
            use ark_ec::{
                Group, CurveGroup, ScalarMul, AffineRepr, CurveConfig,
                short_weierstrass::SWCurveConfig, twisted_edwards::TECurveConfig,
                scalar_mul::{*, wnaf::*},
            };
            use ark_serialize::*;
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 500;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::pairing_output::test_var_base_msm"]
            pub const test_var_base_msm: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::pairing_output::test_var_base_msm",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_var_base_msm(),
                )),
            };
            fn test_var_base_msm() {
                ::ark_algebra_test_templates::msm::test_var_base_msm::<
                    ark_ec::pairing::PairingOutput<Bls12_381>,
                >();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::pairing_output::test_chunked_pippenger"]
            pub const test_chunked_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::pairing_output::test_chunked_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_chunked_pippenger(),
                )),
            };
            fn test_chunked_pippenger() {
                ::ark_algebra_test_templates::msm::test_chunked_pippenger::<
                    ark_ec::pairing::PairingOutput<Bls12_381>,
                >();
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::pairing_output::test_hashmap_pippenger"]
            pub const test_hashmap_pippenger: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::pairing_output::test_hashmap_pippenger",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_hashmap_pippenger(),
                )),
            };
            fn test_hashmap_pippenger() {
                ::ark_algebra_test_templates::msm::test_hashmap_pippenger::<
                    ark_ec::pairing::PairingOutput<Bls12_381>,
                >();
            }
        }
        mod pairing {
            pub const ITERATIONS: usize = 100;
            use ark_ec::{pairing::*, CurveGroup, Group};
            use ark_ff::{Field, PrimeField};
            use ark_std::{test_rng, One, UniformRand, Zero};
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::pairing::test_bilinearity"]
            pub const test_bilinearity: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::pairing::test_bilinearity",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_bilinearity(),
                )),
            };
            fn test_bilinearity() {
                for _ in 0..100 {
                    let mut rng = test_rng();
                    let a: <crate::bls12_381::Bls12_381 as Pairing>::G1 = UniformRand::rand(
                        &mut rng,
                    );
                    let b: <crate::bls12_381::Bls12_381 as Pairing>::G2 = UniformRand::rand(
                        &mut rng,
                    );
                    let s: <crate::bls12_381::Bls12_381 as Pairing>::ScalarField = UniformRand::rand(
                        &mut rng,
                    );
                    let sa = a * s;
                    let sb = b * s;
                    let ans1 = <crate::bls12_381::Bls12_381>::pairing(sa, b);
                    let ans2 = <crate::bls12_381::Bls12_381>::pairing(a, sb);
                    let ans3 = <crate::bls12_381::Bls12_381>::pairing(a, b) * s;
                    match (&ans1, &ans2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans2, &ans3) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans1, &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if *left_val == *right_val {
                                let kind = ::core::panicking::AssertKind::Ne;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans2, &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if *left_val == *right_val {
                                let kind = ::core::panicking::AssertKind::Ne;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans3, &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if *left_val == *right_val {
                                let kind = ::core::panicking::AssertKind::Ne;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let group_order = <<crate::bls12_381::Bls12_381 as Pairing>::ScalarField>::characteristic();
                    match (&ans1.mul_bigint(group_order), &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans2.mul_bigint(group_order), &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&ans3.mul_bigint(group_order), &PairingOutput::zero()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::pairing::test_multi_pairing"]
            pub const test_multi_pairing: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "bls12_381::tests::pairing::test_multi_pairing",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_multi_pairing(),
                )),
            };
            fn test_multi_pairing() {
                for _ in 0..ITERATIONS {
                    let rng = &mut test_rng();
                    let a = <crate::bls12_381::Bls12_381 as Pairing>::G1::rand(rng)
                        .into_affine();
                    let b = <crate::bls12_381::Bls12_381 as Pairing>::G2::rand(rng)
                        .into_affine();
                    let c = <crate::bls12_381::Bls12_381 as Pairing>::G1::rand(rng)
                        .into_affine();
                    let d = <crate::bls12_381::Bls12_381 as Pairing>::G2::rand(rng)
                        .into_affine();
                    let ans1 = <crate::bls12_381::Bls12_381>::pairing(a, b)
                        + &<crate::bls12_381::Bls12_381>::pairing(c, d);
                    let ans2 = <crate::bls12_381::Bls12_381>::multi_pairing(
                        &[a, c],
                        &[b, d],
                    );
                    match (&ans1, &ans2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
        }
        mod g1_h2c {
            use ark_ff::PrimeField;
            extern crate std;
            use ark_ec::{
                hashing::{
                    curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher,
                    HashToCurve,
                },
                short_weierstrass::{Affine, Projective},
            };
            use ark_ff::{
                field_hashers::{DefaultFieldHasher, HashToField},
                fields::Field, One, UniformRand, Zero,
            };
            use ark_std::{format, string::String, vec::Vec};
            use std::{
                fs::{read_dir, File},
                io::BufReader,
            };
            use ::ark_algebra_test_templates::{decode, Sha256};
            use ::ark_algebra_test_templates::json::SuiteVector;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g1_h2c::test_h2c"]
            pub const test_h2c: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::g1_h2c::test_h2c"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_h2c())),
            };
            fn test_h2c() {
                let filename = {
                    let res = ::alloc::fmt::format(
                        ::core::fmt::Arguments::new_v1(
                            &["", "/", "_XMD-SHA-256_SSWU_RO_.json"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(&"./src/testdata"),
                                ::core::fmt::ArgumentV1::new_display(&"BLS12381G1"),
                            ],
                        ),
                    );
                    res
                };
                let file = File::open(filename).unwrap();
                let data: SuiteVector = ::ark_algebra_test_templates::from_reader(
                        BufReader::new(file),
                    )
                    .unwrap();
                match (&data.hash, &"sha256") {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let dst = data.dst.as_bytes();
                let hasher;
                let g1_mapper = MapToCurveBasedHasher::<
                    Projective<crate::bls12_381::g1::Config>,
                    DefaultFieldHasher<Sha256, 128>,
                    WBMap<crate::bls12_381::g1::Config>,
                >::new(dst)
                    .unwrap();
                hasher = <DefaultFieldHasher<
                    Sha256,
                    128,
                > as HashToField<crate::bls12_381::Fq>>::new(dst);
                for v in data.vectors.iter() {
                    let got: Vec<crate::bls12_381::Fq> = hasher
                        .hash_to_field(&v.msg.as_bytes(), 2 * 1);
                    let want: Vec<crate::bls12_381::Fq> = v
                        .u
                        .iter()
                        .map(read_fq_vec)
                        .flatten()
                        .collect();
                    match (&got, &want) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let x = read_fq_vec(&v.p.x);
                    let y = read_fq_vec(&v.p.y);
                    let got = g1_mapper.hash(&v.msg.as_bytes()).unwrap();
                    let want = Affine::<
                        crate::bls12_381::g1::Config,
                    >::new_unchecked(
                        <crate::bls12_381::Fq>::from_base_prime_field_elems(&x[..])
                            .unwrap(),
                        <crate::bls12_381::Fq>::from_base_prime_field_elems(&y[..])
                            .unwrap(),
                    );
                    if !got.is_on_curve() {
                        ::core::panicking::panic("assertion failed: got.is_on_curve()")
                    }
                    if !want.is_on_curve() {
                        ::core::panicking::panic("assertion failed: want.is_on_curve()")
                    }
                    match (&got, &want) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            pub fn read_fq_vec(input: &String) -> Vec<crate::bls12_381::Fq> {
                input
                    .split(",")
                    .map(|f| {
                        <crate::bls12_381::Fq>::from_be_bytes_mod_order(
                            &decode(f.trim_start_matches("0x")).unwrap(),
                        )
                    })
                    .collect()
            }
        }
        mod g2_hc2 {
            use ark_ff::PrimeField;
            extern crate std;
            use ark_ec::{
                hashing::{
                    curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher,
                    HashToCurve,
                },
                short_weierstrass::{Affine, Projective},
            };
            use ark_ff::{
                field_hashers::{DefaultFieldHasher, HashToField},
                fields::Field, One, UniformRand, Zero,
            };
            use ark_std::{format, string::String, vec::Vec};
            use std::{
                fs::{read_dir, File},
                io::BufReader,
            };
            use ::ark_algebra_test_templates::{decode, Sha256};
            use ::ark_algebra_test_templates::json::SuiteVector;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "bls12_381::tests::g2_hc2::test_h2c"]
            pub const test_h2c: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("bls12_381::tests::g2_hc2::test_h2c"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_h2c())),
            };
            fn test_h2c() {
                let filename = {
                    let res = ::alloc::fmt::format(
                        ::core::fmt::Arguments::new_v1(
                            &["", "/", "_XMD-SHA-256_SSWU_RO_.json"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(&"./src/testdata"),
                                ::core::fmt::ArgumentV1::new_display(&"BLS12381G2"),
                            ],
                        ),
                    );
                    res
                };
                let file = File::open(filename).unwrap();
                let data: SuiteVector = ::ark_algebra_test_templates::from_reader(
                        BufReader::new(file),
                    )
                    .unwrap();
                match (&data.hash, &"sha256") {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let dst = data.dst.as_bytes();
                let hasher;
                let g1_mapper = MapToCurveBasedHasher::<
                    Projective<crate::bls12_381::g2::Config>,
                    DefaultFieldHasher<Sha256, 128>,
                    WBMap<crate::bls12_381::g2::Config>,
                >::new(dst)
                    .unwrap();
                hasher = <DefaultFieldHasher<
                    Sha256,
                    128,
                > as HashToField<crate::bls12_381::Fq2>>::new(dst);
                for v in data.vectors.iter() {
                    let got: Vec<crate::bls12_381::Fq> = hasher
                        .hash_to_field(&v.msg.as_bytes(), 2 * 2);
                    let want: Vec<crate::bls12_381::Fq> = v
                        .u
                        .iter()
                        .map(read_fq_vec)
                        .flatten()
                        .collect();
                    match (&got, &want) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let x = read_fq_vec(&v.p.x);
                    let y = read_fq_vec(&v.p.y);
                    let got = g1_mapper.hash(&v.msg.as_bytes()).unwrap();
                    let want = Affine::<
                        crate::bls12_381::g2::Config,
                    >::new_unchecked(
                        <crate::bls12_381::Fq2>::from_base_prime_field_elems(&x[..])
                            .unwrap(),
                        <crate::bls12_381::Fq2>::from_base_prime_field_elems(&y[..])
                            .unwrap(),
                    );
                    if !got.is_on_curve() {
                        ::core::panicking::panic("assertion failed: got.is_on_curve()")
                    }
                    if !want.is_on_curve() {
                        ::core::panicking::panic("assertion failed: want.is_on_curve()")
                    }
                    match (&got, &want) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            pub fn read_fq_vec(input: &String) -> Vec<crate::bls12_381::Fq> {
                input
                    .split(",")
                    .map(|f| {
                        <crate::bls12_381::Fq>::from_be_bytes_mod_order(
                            &decode(f.trim_start_matches("0x")).unwrap(),
                        )
                    })
                    .collect()
            }
        }
    }
    #[cfg(feature = "bls12_381_curve")]
    pub use pairing::*;
    #[cfg(feature = "bls12_381_curve")]
    mod pairing {
        use super::*;
        use ark_ec::bls12::{Bls12, Bls12Config, TwistType};
        pub type Bls12_381 = Bls12<Config>;
        pub struct Config;
        impl Bls12Config for Config {
            const X: &'static [u64] = &[0xd201000000010000];
            const X_IS_NEGATIVE: bool = true;
            const TWIST_TYPE: TwistType = TwistType::M;
            type Fp = Fq;
            type Fp2Config = Fq2Config;
            type Fp6Config = Fq6Config;
            type Fp12Config = Fq12Config;
            type G1Config = self::g1::Config;
            type G2Config = self::g2::Config;
        }
        pub type G1Prepared = ark_ec::bls12::G1Prepared<Config>;
        pub type G2Prepared = ark_ec::bls12::G2Prepared<Config>;
    }
}
pub mod fp128 {
    //! Prime field `Fp` where `p = 2^127 - 1`.
    use ark_ff::fields::{Fp128, MontBackend};
    #[modulus = "170141183460469231731687303715884105727"]
    #[generator = "43"]
    pub struct FqConfig;
    fn fqconfig___() {
        use ark_ff::{
            fields::Fp, BigInt, BigInteger, biginteger::arithmetic as fa, fields::*,
        };
        type B = BigInt<2usize>;
        type F = Fp<MontBackend<FqConfig, 2usize>, 2usize>;
        #[automatically_derived]
        impl MontConfig<2usize> for FqConfig {
            const MODULUS: B = BigInt([18446744073709551615u64, 9223372036854775807u64]);
            const GENERATOR: F = {
                let (is_positive, limbs) = (true, [43u64]);
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            const TWO_ADIC_ROOT_OF_UNITY: F = {
                let (is_positive, limbs) = (
                    true,
                    [18446744073709551614u64, 9223372036854775807u64],
                );
                ::ark_ff::Fp::from_sign_and_limbs(is_positive, &limbs)
            };
            #[inline(always)]
            fn add_assign(a: &mut F, b: &F) {
                __add_with_carry(&mut a.0, &b.0);
                __subtract_modulus(a);
            }
            #[inline(always)]
            fn sub_assign(a: &mut F, b: &F) {
                if b.0 > a.0 {
                    __add_with_carry(
                        &mut a.0,
                        &BigInt([18446744073709551615u64, 9223372036854775807u64]),
                    );
                }
                __sub_with_borrow(&mut a.0, &b.0);
            }
            #[inline(always)]
            fn double_in_place(a: &mut F) {
                a.0.mul2();
                __subtract_modulus(a);
            }
            /// Sets `a = -a`.
            #[inline(always)]
            fn neg_in_place(a: &mut F) {
                if *a != F::ZERO {
                    let mut tmp = BigInt([
                        18446744073709551615u64,
                        9223372036854775807u64,
                    ]);
                    __sub_with_borrow(&mut tmp, &a.0);
                    a.0 = tmp;
                }
            }
            #[inline(always)]
            fn mul_assign(a: &mut F, b: &F) {
                let mut scratch = [0u64; 4usize];
                let mut carry = 0u64;
                scratch[0usize] = fa::mac_with_carry(
                    scratch[0usize],
                    (a.0).0[0usize],
                    (b.0).0[0usize],
                    &mut carry,
                );
                scratch[1usize] = fa::mac_with_carry(
                    scratch[1usize],
                    (a.0).0[0usize],
                    (b.0).0[1usize],
                    &mut carry,
                );
                scratch[0usize + 2usize] = carry;
                let mut carry = 0u64;
                scratch[1usize] = fa::mac_with_carry(
                    scratch[1usize],
                    (a.0).0[1usize],
                    (b.0).0[0usize],
                    &mut carry,
                );
                scratch[2usize] = fa::mac_with_carry(
                    scratch[2usize],
                    (a.0).0[1usize],
                    (b.0).0[1usize],
                    &mut carry,
                );
                scratch[1usize + 2usize] = carry;
                let mut carry2 = 0u64;
                let tmp = scratch[0usize].wrapping_mul(Self::INV);
                let mut carry = 0u64;
                fa::mac(scratch[0usize], tmp, 18446744073709551615u64, &mut carry);
                scratch[1usize] = fa::mac_with_carry(
                    scratch[1usize],
                    tmp,
                    9223372036854775807u64,
                    &mut carry,
                );
                carry2 = fa::adc(&mut scratch[0usize + 2usize], carry, carry2);
                let tmp = scratch[1usize].wrapping_mul(Self::INV);
                let mut carry = 0u64;
                fa::mac(scratch[1usize], tmp, 18446744073709551615u64, &mut carry);
                scratch[2usize] = fa::mac_with_carry(
                    scratch[2usize],
                    tmp,
                    9223372036854775807u64,
                    &mut carry,
                );
                carry2 = fa::adc(&mut scratch[1usize + 2usize], carry, carry2);
                (a.0).0 = scratch[2usize..].try_into().unwrap();
                __subtract_modulus(a);
            }
            #[inline(always)]
            fn square_in_place(a: &mut F) {
                let mut r = [0u64; 4usize];
                let mut carry = 0;
                r[1usize] = fa::mac_with_carry(
                    r[1usize],
                    (a.0).0[0usize],
                    (a.0).0[1usize],
                    &mut carry,
                );
                r[2usize + 0usize] = carry;
                carry = 0;
                r[4usize - 1] = r[4usize - 2] >> 63;
                r[2usize] = (r[2usize] << 1) | (r[2usize - 1] >> 63);
                r[1] <<= 1;
                r[0usize] = fa::mac_with_carry(
                    r[0usize],
                    (a.0).0[0usize],
                    (a.0).0[0usize],
                    &mut carry,
                );
                carry = fa::adc(&mut r[0usize + 1], 0, carry);
                r[2usize] = fa::mac_with_carry(
                    r[2usize],
                    (a.0).0[1usize],
                    (a.0).0[1usize],
                    &mut carry,
                );
                carry = fa::adc(&mut r[2usize + 1], 0, carry);
                let mut carry2 = 0;
                let k = r[0usize].wrapping_mul(Self::INV);
                let mut carry = 0;
                fa::mac_discard(r[0usize], k, 18446744073709551615u64, &mut carry);
                r[1usize] = fa::mac_with_carry(
                    r[1usize],
                    k,
                    9223372036854775807u64,
                    &mut carry,
                );
                carry2 = fa::adc(&mut r[2usize + 0usize], carry, carry2);
                let k = r[1usize].wrapping_mul(Self::INV);
                let mut carry = 0;
                fa::mac_discard(r[1usize], k, 18446744073709551615u64, &mut carry);
                r[2usize] = fa::mac_with_carry(
                    r[2usize],
                    k,
                    9223372036854775807u64,
                    &mut carry,
                );
                carry2 = fa::adc(&mut r[2usize + 1usize], carry, carry2);
                (a.0).0 = r[2usize..].try_into().unwrap();
                __subtract_modulus(a);
            }
            fn sum_of_products<const M: usize>(a: &[F; M], b: &[F; M]) -> F {
                a.iter().zip(b).map(|(a, b)| *a * b).sum()
            }
        }
        #[inline(always)]
        fn __subtract_modulus(a: &mut F) {
            if a.is_geq_modulus() {
                __sub_with_borrow(
                    &mut a.0,
                    &BigInt([18446744073709551615u64, 9223372036854775807u64]),
                );
            }
        }
        #[inline(always)]
        fn __subtract_modulus_with_carry(a: &mut F, carry: bool) {
            if a.is_geq_modulus() || carry {
                __sub_with_borrow(
                    &mut a.0,
                    &BigInt([18446744073709551615u64, 9223372036854775807u64]),
                );
            }
        }
        #[inline(always)]
        fn __add_with_carry(a: &mut B, b: &B) -> bool {
            use ark_ff::biginteger::arithmetic::adc_for_add_with_carry as adc;
            let mut carry = 0;
            carry = adc(&mut a.0[0usize], b.0[0usize], carry);
            carry = adc(&mut a.0[1usize], b.0[1usize], carry);
            carry != 0
        }
        #[inline(always)]
        fn __sub_with_borrow(a: &mut B, b: &B) -> bool {
            use ark_ff::biginteger::arithmetic::sbb_for_sub_with_borrow as sbb;
            let mut borrow = 0;
            borrow = sbb(&mut a.0[0usize], b.0[0usize], borrow);
            borrow = sbb(&mut a.0[1usize], b.0[1usize], borrow);
            borrow != 0
        }
    }
    pub type Fq = Fp128<MontBackend<FqConfig, 2>>;
    #[cfg(test)]
    mod tests {
        use super::*;
        use ark_algebra_test_templates::*;
        mod fq {
            use super::*;
            use ark_ff::{
                fields::{FftField, Field, LegendreSymbol, PrimeField},
                Fp, MontBackend, MontConfig,
            };
            use ark_serialize::{buffer_bit_byte_size, Flags};
            use ark_std::{
                io::Cursor, rand::Rng, vec::Vec, test_rng, vec, Zero, One, UniformRand,
            };
            const ITERATIONS: usize = 1000;
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_frobenius"]
            pub const test_frobenius: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_frobenius"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_frobenius())),
            };
            pub fn test_frobenius() {
                use ark_ff::Field;
                use ark_std::UniformRand;
                let mut rng = ark_std::test_rng();
                let characteristic = <Fq>::characteristic();
                let max_power = (<Fq>::extension_degree() + 1) as usize;
                for _ in 0..ITERATIONS {
                    let a = <Fq>::rand(&mut rng);
                    let mut a_0 = a;
                    a_0.frobenius_map_in_place(0);
                    match (&a, &a_0) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a, &a.frobenius_map(0)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let mut a_q = a.pow(&characteristic);
                    for power in 1..max_power {
                        match (&a_q, &a.frobenius_map(power)) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut a_qi = a;
                        a_qi.frobenius_map_in_place(power);
                        match (&a_qi, &a_q) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::Some(
                                            ::core::fmt::Arguments::new_v1(
                                                &["failed on power "],
                                                &[::core::fmt::ArgumentV1::new_display(&power)],
                                            ),
                                        ),
                                    );
                                }
                            }
                        };
                        a_q = a_q.pow(&characteristic);
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_serialization"]
            pub const test_serialization: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_serialization"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_serialization(),
                )),
            };
            fn test_serialization() {
                use ark_serialize::*;
                use ark_std::UniformRand;
                for compress in [Compress::Yes, Compress::No] {
                    for validate in [Validate::Yes, Validate::No] {
                        let buf_size = <Fq>::zero().serialized_size(compress);
                        let buffer_size = buffer_bit_byte_size(
                                <Fq as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize,
                            )
                            .1 * (<Fq>::extension_degree() as usize);
                        match (&buffer_size, &buf_size) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                        let mut rng = ark_std::test_rng();
                        for _ in 0..ITERATIONS {
                            let a = <Fq>::rand(&mut rng);
                            {
                                let mut serialized = ::alloc::vec::from_elem(0u8, buf_size);
                                let mut cursor = Cursor::new(&mut serialized[..]);
                                a.serialize_with_mode(&mut cursor, compress).unwrap();
                                let mut cursor = Cursor::new(&serialized[..]);
                                let b = <Fq>::deserialize_with_mode(
                                        &mut cursor,
                                        compress,
                                        validate,
                                    )
                                    .unwrap();
                                match (&a, &b) {
                                    (left_val, right_val) => {
                                        if !(*left_val == *right_val) {
                                            let kind = ::core::panicking::AssertKind::Eq;
                                            ::core::panicking::assert_failed(
                                                kind,
                                                &*left_val,
                                                &*right_val,
                                                ::core::option::Option::None,
                                            );
                                        }
                                    }
                                };
                            }
                            {
                                let mut serialized = ::alloc::vec::from_elem(0, buf_size);
                                let result = match a
                                    .serialize_with_flags(
                                        &mut &mut serialized[..],
                                        ::ark_algebra_test_templates::fields::DummyFlags,
                                    )
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                let result = match <Fq>::deserialize_with_flags::<
                                    _,
                                    ::ark_algebra_test_templates::fields::DummyFlags,
                                >(&mut &serialized[..])
                                    .unwrap_err()
                                {
                                    SerializationError::NotEnoughSpace => true,
                                    _ => false,
                                };
                                if !result {
                                    ::core::panicking::panic("assertion failed: result")
                                }
                                {
                                    let mut serialized = ::alloc::vec::from_elem(
                                        0,
                                        buf_size - 1,
                                    );
                                    let mut cursor = Cursor::new(&mut serialized[..]);
                                    a.serialize_with_mode(&mut cursor, compress).unwrap_err();
                                    let mut cursor = Cursor::new(&serialized[..]);
                                    <Fq>::deserialize_with_mode(&mut cursor, compress, validate)
                                        .unwrap_err();
                                }
                            }
                        }
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_add_properties"]
            pub const test_add_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_add_properties"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_add_properties(),
                )),
            };
            fn test_add_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                match (&-zero, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if !zero.is_zero() {
                    ::core::panicking::panic("assertion failed: zero.is_zero()")
                }
                if !<Fq>::ZERO.is_zero() {
                    ::core::panicking::panic("assertion failed: <Fq>::ZERO.is_zero()")
                }
                match (&<Fq>::ZERO, &zero) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    let c = <Fq>::rand(&mut rng);
                    match (&((a + b) + c), &(a + (b + c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a + b), &(b + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero + c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-a + a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-b + b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(-c + c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&-zero, &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let t0 = (a + &b) + &c;
                    let t1 = (a + &c) + &b;
                    let t2 = (b + &c) + &a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&a.double(), &(a + a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&b.double(), &(b + b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&c.double(), &(c + c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_sub_properties"]
            pub const test_sub_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_sub_properties"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sub_properties(),
                )),
            };
            fn test_sub_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                for _ in 0..(ITERATIONS * ITERATIONS) {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    if !((a - b) + (b - a)).is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: ((a - b) + (b - a)).is_zero()",
                        )
                    }
                    match (&(zero - a), &-a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(zero - b), &-b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(a - zero), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    match (&(b - zero), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_mul_properties"]
            pub const test_mul_properties: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_mul_properties"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_mul_properties(),
                )),
            };
            fn test_mul_properties() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                let zero = <Fq>::zero();
                let one = <Fq>::one();
                match (&one.inverse().unwrap(), &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(&["One inverse failed"], &[]),
                                ),
                            );
                        }
                    }
                };
                if !one.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One is not one"], &[]),
                    )
                }
                if !<Fq>::ONE.is_one() {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(&["One constant is not one"], &[]),
                    )
                }
                match (&<Fq>::ONE, &one) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::Some(
                                    ::core::fmt::Arguments::new_v1(
                                        &["One constant is incorrect"],
                                        &[],
                                    ),
                                ),
                            );
                        }
                    }
                };
                for _ in 0..ITERATIONS {
                    let a = <Fq>::rand(&mut rng);
                    let b = <Fq>::rand(&mut rng);
                    let c = <Fq>::rand(&mut rng);
                    match (&((a * b) * c), &(a * (b * c))) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * b), &(b * a)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * a), &a) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * b), &b) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(one * c), &c) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Identity mul failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * a), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * b), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(zero * c), &zero) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Mul by zero failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c.inverse().unwrap()), &one) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Mul by inverse failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    let t0 = (a * b) * c;
                    let t1 = (a * c) * b;
                    let t2 = (b * c) * a;
                    match (&t0, &t1) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&t1, &t2) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Associativity + commutativity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * a), &a.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * b), &b.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * c), &c.square()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(&["Squaring failed"], &[]),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(a * (b + c)), &(a * b + a * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(b * (a + c)), &(b * a + b * c)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (&(c * (a + b)), &(c * a + c * b)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(a + b).square(),
                        &(a.square() + b.square() + a * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(b + c).square(),
                        &(c.square() + b.square() + c * b.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                    match (
                        &(c + a).square(),
                        &(a.square() + c.square() + a * c.double()),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::Some(
                                        ::core::fmt::Arguments::new_v1(
                                            &["Distributivity for square failed"],
                                            &[],
                                        ),
                                    ),
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_pow"]
            pub const test_pow: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_pow"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_pow())),
            };
            fn test_pow() {
                use ark_std::UniformRand;
                let mut rng = test_rng();
                for _ in 0..(ITERATIONS / 10) {
                    for i in 0..20 {
                        let a = <Fq>::rand(&mut rng);
                        let target = a.pow(&[i]);
                        let mut c = <Fq>::one();
                        for _ in 0..i {
                            c *= a;
                        }
                        match (&c, &target) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                    let a = <Fq>::rand(&mut rng);
                    let mut result = a;
                    for i in 0..<Fq>::extension_degree() {
                        result = result.pow(<Fq>::characteristic());
                    }
                    match (&a, &result) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e1: [u64; 10] = rng.gen();
                    let e2: [u64; 10] = rng.gen();
                    match (&a.pow(&e1).pow(&e2), &a.pow(&e2).pow(&e1)) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    let e3: [u64; 10] = rng.gen();
                    let a_to_e1 = a.pow(e1);
                    let a_to_e2 = a.pow(e2);
                    let a_to_e1_plus_e2 = a.pow(e1) * a.pow(e2);
                    match (
                        &a_to_e1_plus_e2.pow(&e3),
                        &(a_to_e1.pow(&e3) * a_to_e2.pow(&e3)),
                    ) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_sum_of_products_tests"]
            pub const test_sum_of_products_tests: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "fp128::tests::fq::test_sum_of_products_tests",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_tests(),
                )),
            };
            fn test_sum_of_products_tests() {
                use ark_std::{UniformRand, rand::Rng};
                let rng = &mut test_rng();
                for _ in 0..ITERATIONS {
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        1,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        2,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        3,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        4,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        5,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        6,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        7,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        8,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        9,
                    >(rng);
                    ::ark_algebra_test_templates::fields::sum_of_products_test_helper::<
                        Fq,
                        10,
                    >(rng);
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_sqrt"]
            pub const test_sqrt: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_sqrt"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_sqrt())),
            };
            fn test_sqrt() {
                if <Fq>::SQRT_PRECOMP.is_some() {
                    use ark_std::UniformRand;
                    let rng = &mut test_rng();
                    if !<Fq>::zero().sqrt().unwrap().is_zero() {
                        ::core::panicking::panic(
                            "assertion failed: <Fq>::zero().sqrt().unwrap().is_zero()",
                        )
                    }
                    for _ in 0..ITERATIONS {
                        let a = <Fq>::rand(rng);
                        let b = a.square();
                        let sqrt = b.sqrt().unwrap();
                        if !(a == sqrt || -a == sqrt) {
                            ::core::panicking::panic(
                                "assertion failed: a == sqrt || -a == sqrt",
                            )
                        }
                        if let Some(mut b) = a.sqrt() {
                            b.square_in_place();
                            match (&a, &b) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                        let a = <Fq>::rand(rng);
                        let b = a.square();
                        match (&b.legendre(), &LegendreSymbol::QuadraticResidue) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_fft"]
            pub const test_fft: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_fft"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_fft())),
            };
            fn test_fft() {
                use ark_ff::FftField;
                match (
                    &<Fq>::TWO_ADIC_ROOT_OF_UNITY.pow([1 << <Fq>::TWO_ADICITY]),
                    &<Fq>::one(),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(small_subgroup_base) = <Fq>::SMALL_SUBGROUP_BASE {
                    let small_subgroup_base_adicity = <Fq>::SMALL_SUBGROUP_BASE_ADICITY
                        .unwrap();
                    let large_subgroup_root_of_unity = <Fq>::LARGE_SUBGROUP_ROOT_OF_UNITY
                        .unwrap();
                    let pow = (1 << <Fq>::TWO_ADICITY)
                        * (small_subgroup_base as u64).pow(small_subgroup_base_adicity);
                    match (&large_subgroup_root_of_unity.pow([pow]), &<Fq>::one()) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    for i in 0..=<Fq>::TWO_ADICITY {
                        for j in 0..=small_subgroup_base_adicity {
                            let size = (1u64 << i) * (small_subgroup_base as u64).pow(j);
                            let root = <Fq>::get_root_of_unity(size as u64).unwrap();
                            match (&root.pow([size as u64]), &<Fq>::one()) {
                                (left_val, right_val) => {
                                    if !(*left_val == *right_val) {
                                        let kind = ::core::panicking::AssertKind::Eq;
                                        ::core::panicking::assert_failed(
                                            kind,
                                            &*left_val,
                                            &*right_val,
                                            ::core::option::Option::None,
                                        );
                                    }
                                }
                            };
                        }
                    }
                } else {
                    for i in 0..=<Fq>::TWO_ADICITY {
                        let size = 1 << i;
                        let root = <Fq>::get_root_of_unity(size).unwrap();
                        match (&root.pow([size as u64]), &<Fq>::one()) {
                            (left_val, right_val) => {
                                if !(*left_val == *right_val) {
                                    let kind = ::core::panicking::AssertKind::Eq;
                                    ::core::panicking::assert_failed(
                                        kind,
                                        &*left_val,
                                        &*right_val,
                                        ::core::option::Option::None,
                                    );
                                }
                            }
                        };
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_sum_of_products_edge_case"]
            pub const test_sum_of_products_edge_case: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "fp128::tests::fq::test_sum_of_products_edge_case",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_sum_of_products_edge_case(),
                )),
            };
            fn test_sum_of_products_edge_case() {
                use ark_ff::BigInteger;
                let mut a_max = <Fq>::ZERO.into_bigint();
                for (i, limb) in a_max.as_mut().iter_mut().enumerate() {
                    if i == <Fq as PrimeField>::BigInt::NUM_LIMBS - 1 {
                        let mod_num_bits_mod_64 = 64
                            * <Fq as PrimeField>::BigInt::NUM_LIMBS
                            - (<Fq as PrimeField>::MODULUS_BIT_SIZE as usize);
                        if mod_num_bits_mod_64 == 63 {
                            *limb = 0u64;
                        } else {
                            *limb = u64::MAX >> (mod_num_bits_mod_64 + 1);
                        }
                    } else {
                        *limb = u64::MAX;
                    }
                }
                let a_max = <Fq>::from_bigint(a_max).unwrap();
                let b_max = -<Fq>::one();
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    1,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    2,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    3,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    4,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    5,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    6,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    7,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    8,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    9,
                >(a_max, b_max);
                ::ark_algebra_test_templates::fields::prime_field_sum_of_products_test_helper::<
                    _,
                    10,
                >(a_max, b_max);
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_constants"]
            pub const test_constants: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName("fp128::tests::fq::test_constants"),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(test_constants())),
            };
            fn test_constants() {
                use ark_ff::{FpConfig, BigInteger, SqrtPrecomputation};
                use ::ark_algebra_test_templates::num_bigint::BigUint;
                use ::ark_algebra_test_templates::num_integer::Integer;
                let modulus: BigUint = <Fq>::MODULUS.into();
                let modulus_minus_one = &modulus - 1u8;
                match (
                    &BigUint::from(<Fq>::MODULUS_MINUS_ONE_DIV_TWO),
                    &(&modulus_minus_one / 2u32),
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&(<Fq>::MODULUS_BIT_SIZE as u64), &modulus.bits()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                if let Some(SqrtPrecomputation::Case3Mod4 { modulus_plus_one_div_four })
                    = <Fq>::SQRT_PRECOMP {
                    let check = ((&modulus + 1u8) / 4u8).to_u64_digits();
                    let len = check.len();
                    match (&&modulus_plus_one_div_four[..len], &&check) {
                        (left_val, right_val) => {
                            if !(*left_val == *right_val) {
                                let kind = ::core::panicking::AssertKind::Eq;
                                ::core::panicking::assert_failed(
                                    kind,
                                    &*left_val,
                                    &*right_val,
                                    ::core::option::Option::None,
                                );
                            }
                        }
                    };
                    if !modulus_plus_one_div_four[len..].iter().all(|l| *l == 0) {
                        ::core::panicking::panic(
                            "assertion failed: modulus_plus_one_div_four[len..].iter().all(|l| *l == 0)",
                        )
                    }
                }
                let mut two_adicity = 0;
                let mut trace = modulus_minus_one;
                while trace.is_even() {
                    trace /= 2u8;
                    two_adicity += 1;
                }
                match (&two_adicity, &<Fq>::TWO_ADICITY) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&BigUint::from(<Fq>::TRACE), &trace) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let trace_minus_one_div_two = (&trace - 1u8) / 2u8;
                match (
                    &BigUint::from(<Fq>::TRACE_MINUS_ONE_DIV_TWO),
                    &trace_minus_one_div_two,
                ) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                let two_adic_root_of_unity: BigUint = <Fq>::TWO_ADIC_ROOT_OF_UNITY
                    .into();
                let generator: BigUint = <Fq>::GENERATOR.into_bigint().into();
                match (&two_adic_root_of_unity, &generator.modpow(&trace, &modulus)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (<Fq>::SMALL_SUBGROUP_BASE, <Fq>::SMALL_SUBGROUP_BASE_ADICITY) {
                    (Some(base), Some(adicity)) => {
                        let mut e = generator;
                        for _i in 0..adicity {
                            e = e.modpow(&base.into(), &modulus);
                        }
                    }
                    (None, None) => {}
                    (_, _) => {
                        ::core::panicking::panic_fmt(
                            ::core::fmt::Arguments::new_v1(
                                &[
                                    "Should specify both `SMALL_SUBGROUP_BASE` and `SMALL_SUBGROUP_BASE_ADICITY`",
                                ],
                                &[],
                            ),
                        )
                    }
                }
            }
            extern crate test;
            #[cfg(test)]
            #[rustc_test_marker = "fp128::tests::fq::test_montgomery_config"]
            pub const test_montgomery_config: test::TestDescAndFn = test::TestDescAndFn {
                desc: test::TestDesc {
                    name: test::StaticTestName(
                        "fp128::tests::fq::test_montgomery_config",
                    ),
                    ignore: false,
                    ignore_message: ::core::option::Option::None,
                    compile_fail: false,
                    no_run: false,
                    should_panic: test::ShouldPanic::No,
                    test_type: test::TestType::UnitTest,
                },
                testfn: test::StaticTestFn(|| test::assert_test_result(
                    test_montgomery_config(),
                )),
            };
            pub fn test_montgomery_config() {
                use ark_ff::{FpConfig, BigInteger};
                use ::ark_algebra_test_templates::num_bigint::{BigUint, BigInt};
                use ::ark_algebra_test_templates::num_integer::Integer;
                use ::ark_algebra_test_templates::num_traits::{
                    Signed, cast::ToPrimitive,
                };
                let limbs = <Fq as PrimeField>::BigInt::NUM_LIMBS;
                let modulus: BigUint = <Fq>::MODULUS.into();
                let r = BigUint::from(2u8)
                    .modpow(&((limbs * 64) as u64).into(), &modulus);
                let r2 = (&r * &r) % &modulus;
                let inv = {
                    let mut inv = 1u128;
                    let two_to_64 = 1u128 << 64;
                    for _ in 0..63 {
                        inv = inv.checked_mul(inv).unwrap() % two_to_64;
                        inv = inv.checked_mul(<Fq>::MODULUS.0[0] as u128).unwrap()
                            % &two_to_64;
                    }
                    let mut inv = inv as i128;
                    let two_to_64 = two_to_64 as i128;
                    inv = (-inv) % two_to_64;
                    inv as u64
                };
                let group_order = 0b111111111111111111111111111111111111111111111111111111111111111u64;
                let group_order_lower = ((group_order << 32) >> 32) as u32;
                let group_order_upper = ((group_order) >> 32) as u32;
                let modulus_lower_limb = <Fq>::MODULUS.0[0];
                let modulus_lower_limb_to2_32 = modulus_lower_limb
                    .wrapping_pow(u32::MAX)
                    .wrapping_mul(modulus_lower_limb);
                let inv2 = modulus_lower_limb
                    .wrapping_pow(group_order_lower)
                    .wrapping_mul(
                        modulus_lower_limb_to2_32.wrapping_pow(group_order_upper),
                    )
                    .wrapping_neg();
                match (&r, &<Fq>::R.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&r2, &<Fq>::R2.into()) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv, &u64::from(<Fq>::INV)) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&inv2, &<Fq>::INV) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
            }
        }
    }
}
#[rustc_main]
pub fn main() -> () {
    extern crate test;
    test::test_main_static(
        &[
            &test_constants,
            &test_inv,
            &test_modulus,
            &batch_normalization,
            &test_gen,
            &test_gen,
            &test_add_properties,
            &test_frobenius,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_tests,
            &test_add_properties,
            &test_frobenius,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_tests,
            &test_add_properties,
            &test_frobenius,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_tests,
            &test_add_properties,
            &test_constants,
            &test_fft,
            &test_frobenius,
            &test_montgomery_config,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_edge_case,
            &test_sum_of_products_tests,
            &test_add_properties,
            &test_constants,
            &test_fft,
            &test_frobenius,
            &test_montgomery_config,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_edge_case,
            &test_sum_of_products_tests,
            &test_add_properties,
            &test_affine_conversion,
            &test_chunked_pippenger,
            &test_cofactor_ops,
            &test_hashmap_pippenger,
            &test_mixed_addition,
            &test_mul_properties,
            &test_serialization,
            &test_sub_properties,
            &test_sw_properties,
            &test_var_base_msm,
            &test_h2c,
            &test_add_properties,
            &test_affine_conversion,
            &test_chunked_pippenger,
            &test_cofactor_ops,
            &test_hashmap_pippenger,
            &test_mixed_addition,
            &test_mul_properties,
            &test_serialization,
            &test_sub_properties,
            &test_sw_properties,
            &test_var_base_msm,
            &test_h2c,
            &test_bilinearity,
            &test_multi_pairing,
            &test_chunked_pippenger,
            &test_hashmap_pippenger,
            &test_var_base_msm,
            &test_add_properties,
            &test_constants,
            &test_fft,
            &test_frobenius,
            &test_montgomery_config,
            &test_mul_properties,
            &test_pow,
            &test_serialization,
            &test_sqrt,
            &test_sub_properties,
            &test_sum_of_products_edge_case,
            &test_sum_of_products_tests,
        ],
    )
}

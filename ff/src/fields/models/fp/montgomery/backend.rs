use super::*;
/// Construct a [`Fp<MontBackend<T, N>, N>`] element from a literal string. This
/// should be used primarily for constructing constant field elements; in a
/// non-const context, [`Fp::from_str`](`ark_std::str::FromStr::from_str`) is
/// preferable.
///
/// # Panics
///
/// If the integer represented by the string cannot fit in the number
/// of limbs of the `Fp`, this macro results in a
/// * compile-time error if used in a const context
/// * run-time error otherwise.
///
/// # Usage
///
/// ```rust
/// # use ark_test_curves::MontFp;
/// # use ark_test_curves::bls12_381 as ark_bls12_381;
/// # use ark_std::{One, str::FromStr};
/// use ark_bls12_381::Fq;
/// const ONE: Fq = MontFp!("1");
/// const NEG_ONE: Fq = MontFp!("-1");
///
/// fn check_correctness() {
///     assert_eq!(ONE, Fq::one());
///     assert_eq!(Fq::from_str("1").unwrap(), ONE);
///     assert_eq!(NEG_ONE, -Fq::one());
/// }
/// ```
#[macro_export]
macro_rules! MontFp {
    ($c0:expr) => {{
        let (is_positive, limbs) = $crate::ark_ff_macros::to_sign_and_limbs!($c0);
        $crate::Fp::from_sign_and_limbs(is_positive, &limbs)
    }};
}

pub use ark_ff_macros::MontConfig;

pub use MontFp;

pub struct MontBackend<T: MontConfig<N>, const N: usize>(PhantomData<T>);

impl<T: MontConfig<N>, const N: usize> FpConfig<N> for MontBackend<T, N> {
    /// The modulus of the field.
    const MODULUS: crate::BigInt<N> = T::MODULUS;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<Self, N> = T::GENERATOR;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp<Self, N> = Fp::new_unchecked(BigInt([0u64; N]));

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp<Self, N> = Fp::new_unchecked(T::R);

    const TWO_ADICITY: u32 = T::TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Fp<Self, N> = T::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = T::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = T::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<Self, N>> = T::LARGE_SUBGROUP_ROOT_OF_UNITY;
    const SQRT_PRECOMP: Option<crate::SqrtPrecomputation<Fp<Self, N>>> = T::SQRT_PRECOMP;

    fn add_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::add_assign(a, b)
    }

    fn sub_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::sub_assign(a, b)
    }

    fn double_in_place(a: &mut Fp<Self, N>) {
        T::double_in_place(a)
    }

    fn neg_in_place(a: &mut Fp<Self, N>) {
        T::neg_in_place(a)
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@zkteam/modular_multiplication) if
    /// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    fn mul_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::mul_assign(a, b)
    }

    fn sum_of_products<const M: usize>(a: &[Fp<Self, N>; M], b: &[Fp<Self, N>; M]) -> Fp<Self, N> {
        T::sum_of_products(a, b)
    }

    #[inline]
    #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
    fn square_in_place(a: &mut Fp<Self, N>) {
        T::square_in_place(a)
    }

    fn inverse(a: &Fp<Self, N>) -> Option<Fp<Self, N>> {
        T::inverse(a)
    }

    fn from_bigint(r: BigInt<N>) -> Option<Fp<Self, N>> {
        T::from_bigint(r)
    }

    #[inline]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<Self, N>) -> BigInt<N> {
        T::into_bigint(a)
    }
}

impl<T: MontConfig<N>, const N: usize> Fp<MontBackend<T, N>, N> {
    #[doc(hidden)]
    pub const R: BigInt<N> = T::R;
    #[doc(hidden)]
    pub const R2: BigInt<N> = T::R2;
    #[doc(hidden)]
    pub const INV: u64 = T::INV;

    /// Construct a new field element from its underlying
    /// [`struct@BigInt`] data type.
    #[inline]
    pub const fn new(element: BigInt<N>) -> Self {
        let mut r = Self(element, PhantomData);
        if r.const_is_zero() {
            r
        } else {
            r = r.mul(&Fp(T::R2, PhantomData));
            r
        }
    }

    /// Construct a new field element from its underlying
    /// [`struct@BigInt`] data type.
    ///
    /// Unlike [`Self::new`], this method does not perform Montgomery reduction.
    /// Thus, this method should be used only when constructing
    /// an element from an integer that has already been put in
    /// Montgomery form.
    #[inline]
    pub const fn new_unchecked(element: BigInt<N>) -> Self {
        Self(element, PhantomData)
    }

    const fn const_is_zero(&self) -> bool {
        self.0.const_is_zero()
    }

    #[doc(hidden)]
    const fn const_neg(self) -> Self {
        if !self.const_is_zero() {
            Self::new_unchecked(Self::sub_with_borrow(&T::MODULUS, &self.0))
        } else {
            self
        }
    }

    /// Interpret a set of limbs (along with a sign) as a field element.
    /// For *internal* use only; please use the `ark_ff::MontFp` macro instead
    /// of this method
    #[doc(hidden)]
    pub const fn from_sign_and_limbs(is_positive: bool, limbs: &[u64]) -> Self {
        let mut repr = BigInt::<N>([0; N]);
        assert!(limbs.len() <= N);
        crate::const_for!((i in 0..(limbs.len())) {
            repr.0[i] = limbs[i];
        });
        let res = Self::new(repr);
        if is_positive {
            res
        } else {
            res.const_neg()
        }
    }

    pub(super) const fn mul_without_cond_subtract(mut self, other: &Self) -> (bool, Self) {
        let (mut lo, mut hi) = ([0u64; N], [0u64; N]);
        crate::const_for!((i in 0..N) {
            let mut carry = 0;
            crate::const_for!((j in 0..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], (self.0).0[i], (other.0).0[j], &mut carry);
                } else {
                    lo[k] = mac_with_carry!(lo[k], (self.0).0[i], (other.0).0[j], &mut carry);
                }
            });
            hi[i] = carry;
        });
        // Montgomery reduction
        let mut carry2 = 0;
        crate::const_for!((i in 0..N) {
            let tmp = lo[i].wrapping_mul(T::INV);
            let mut carry;
            mac!(lo[i], tmp, T::MODULUS.0[0], &mut carry);
            crate::const_for!((j in 1..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], tmp, T::MODULUS.0[j], &mut carry);
                }  else {
                    lo[k] = mac_with_carry!(lo[k], tmp, T::MODULUS.0[j], &mut carry);
                }
            });
            hi[i] = adc!(hi[i], carry, &mut carry2);
        });

        crate::const_for!((i in 0..N) {
            (self.0).0[i] = hi[i];
        });
        (carry2 != 0, self)
    }

    const fn mul(self, other: &Self) -> Self {
        let (carry, res) = self.mul_without_cond_subtract(other);
        if T::MODULUS_HAS_SPARE_BIT {
            res.const_subtract_modulus()
        } else {
            res.const_subtract_modulus_with_carry(carry)
        }
    }

    const fn const_is_valid(&self) -> bool {
        crate::const_for!((i in 0..N) {
            if (self.0).0[N - i - 1] < T::MODULUS.0[N - i - 1] {
                return true
            } else if (self.0).0[N - i - 1] > T::MODULUS.0[N - i - 1] {
                return false
            }
        });
        false
    }

    #[inline]
    const fn const_subtract_modulus(mut self) -> Self {
        if !self.const_is_valid() {
            self.0 = Self::sub_with_borrow(&self.0, &T::MODULUS);
        }
        self
    }

    #[inline]
    const fn const_subtract_modulus_with_carry(mut self, carry: bool) -> Self {
        if carry || !self.const_is_valid() {
            self.0 = Self::sub_with_borrow(&self.0, &T::MODULUS);
        }
        self
    }

    const fn sub_with_borrow(a: &BigInt<N>, b: &BigInt<N>) -> BigInt<N> {
        a.const_sub_with_borrow(b).0
    }

    pub const fn sqrt_precomputation() -> Option<SqrtPrecomputation<Self>> {
        match T::MODULUS.mod_4() {
            3 => match T::MODULUS_PLUS_ONE_DIV_FOUR.as_ref() {
                Some(m) => Some(SqrtPrecomputation::Case3Mod4 {
                    modulus_plus_one_div_four: &m.0,
                }),
                None => None,
            },
            _ => Some(SqrtPrecomputation::TonelliShanks {
                two_adicity: <MontBackend<T, N>>::TWO_ADICITY,
                quadratic_nonresidue_to_trace: T::TWO_ADIC_ROOT_OF_UNITY,
                trace_of_modulus_minus_one_div_two:
                    &<Fp<MontBackend<T, N>, N>>::TRACE_MINUS_ONE_DIV_TWO.0,
            }),
        }
    }
}

#[cfg(test)]
mod test {
    use ark_std::{str::FromStr, vec::*};
    use ark_test_curves::secp256k1::Fr;
    use num_bigint::{BigInt, BigUint, Sign};

    #[test]
    fn test_mont_macro_correctness() {
        let (is_positive, limbs) = str_to_limbs_u64(
            "111192936301596926984056301862066282284536849596023571352007112326586892541694",
        );
        let t = Fr::from_sign_and_limbs(is_positive, &limbs);

        let result: BigUint = t.into();
        let expected = BigUint::from_str(
            "111192936301596926984056301862066282284536849596023571352007112326586892541694",
        )
        .unwrap();

        assert_eq!(result, expected);
    }

    fn str_to_limbs_u64(num: &str) -> (bool, Vec<u64>) {
        let (sign, digits) = BigInt::from_str(num)
            .expect("could not parse to bigint")
            .to_radix_le(16);
        let limbs = digits
            .chunks(16)
            .map(|chunk| {
                let mut this = 0u64;
                for (i, hexit) in chunk.iter().enumerate() {
                    this += (*hexit as u64) << (4 * i);
                }
                this
            })
            .collect::<Vec<_>>();

        let sign_is_positive = sign != Sign::Minus;
        (sign_is_positive, limbs)
    }
}

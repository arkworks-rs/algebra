/// Indication of the field element's quadratic residuosity
///
/// # Examples
/// ```
/// # use ark_std::test_rng;
/// # use ark_std::UniformRand;
/// # use ark_test_curves::{LegendreSymbol, Field, bls12_381::Fq as Fp};
/// let a: Fp = Fp::rand(&mut test_rng());
/// let b = a.square();
/// assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum LegendreSymbol {
    Zero = 0,
    QuadraticResidue = 1,
    QuadraticNonResidue = -1,
}

impl LegendreSymbol {
    /// Returns true if `self.is_zero()`.
    ///
    /// # Examples
    /// ```
    /// # use ark_std::test_rng;
    /// # use ark_std::UniformRand;
    /// # use ark_test_curves::{LegendreSymbol, Field, bls12_381::Fq as Fp};
    /// let a: Fp = Fp::rand(&mut test_rng());
    /// let b: Fp = a.square();
    /// assert!(!b.legendre().is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        *self == LegendreSymbol::Zero
    }

    /// Returns true if `self` is a quadratic non-residue.
    ///
    /// # Examples
    /// ```
    /// # use ark_test_curves::{Fp2Config, Field, LegendreSymbol, bls12_381::{Fq, Fq2Config}};
    /// let a: Fq = Fq2Config::NONRESIDUE;
    /// assert!(a.legendre().is_qnr());
    /// ```
    pub fn is_qnr(&self) -> bool {
        *self == LegendreSymbol::QuadraticNonResidue
    }

    /// Returns true if `self` is a quadratic residue.
    /// # Examples
    /// ```
    /// # use ark_std::test_rng;
    /// # use ark_test_curves::bls12_381::Fq as Fp;
    /// # use ark_std::UniformRand;
    /// # use ark_ff::{LegendreSymbol, Field};
    /// let a: Fp = Fp::rand(&mut test_rng());
    /// let b: Fp = a.square();
    /// assert!(b.legendre().is_qr());
    /// ```
    pub fn is_qr(&self) -> bool {
        *self == LegendreSymbol::QuadraticResidue
    }
}

/// Precomputation that makes computing square roots faster
/// A particular variant should only be instantiated if the modulus satisfies
/// the corresponding condition.
#[non_exhaustive]
pub enum SqrtPrecomputation<F: crate::Field> {
    // Tonelli-Shanks algorithm works for all elements, no matter what the modulus is.
    TonelliShanks {
        two_adicity: u32,
        quadratic_nonresidue_to_trace: F,
        trace_of_modulus_minus_one_div_two: &'static [u64],
    },
    /// To be used when the modulus is 3 mod 4.
    Case3Mod4 {
        modulus_plus_one_div_four: &'static [u64],
    },
    /// To be used when the modulus is 5 mod 8.
    Case5Mod8 {
        modulus_plus_three_div_eight: &'static [u64],
        modulus_minus_one_div_four: &'static [u64],
    },
}

impl<F: crate::Field> SqrtPrecomputation<F> {
    pub fn sqrt(&self, elem: &F) -> Option<F> {
        match self {
            Self::TonelliShanks {
                two_adicity,
                quadratic_nonresidue_to_trace,
                trace_of_modulus_minus_one_div_two,
            } => {
                // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
                // Actually this is just normal Tonelli-Shanks; since `P::Generator`
                // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
                // is also a quadratic non-residue (since `t` is odd).
                if elem.is_zero() {
                    return Some(F::zero());
                }
                // Try computing the square root (x at the end of the algorithm)
                // Check at the end of the algorithm if x was a square root
                // Begin Tonelli-Shanks
                let mut z = *quadratic_nonresidue_to_trace;
                let mut w = elem.pow(trace_of_modulus_minus_one_div_two);
                let mut x = w * elem;
                let mut b = x * &w;

                let mut v = *two_adicity as usize;

                while !b.is_one() {
                    let mut k = 0usize;

                    let mut b2k = b;
                    while !b2k.is_one() {
                        // invariant: b2k = b^(2^k) after entering this loop
                        b2k.square_in_place();
                        k += 1;
                    }

                    if k == (*two_adicity as usize) {
                        // We are in the case where self^(T * 2^k) = x^(P::MODULUS - 1) = 1,
                        // which means that no square root exists.
                        return None;
                    }
                    let j = v - k;
                    w = z;
                    for _ in 1..j {
                        w.square_in_place();
                    }

                    z = w.square();
                    b *= &z;
                    x *= &w;
                    v = k;
                }
                // Is x the square root? If so, return it.
                if x.square() == *elem {
                    Some(x)
                } else {
                    // Consistency check that if no square root is found,
                    // it is because none exists.
                    debug_assert!(!matches!(elem.legendre(), LegendreSymbol::QuadraticResidue));
                    None
                }
            },
            // Let `x ^ 2 = a mod p` is our quadratic equation where we need
            // to find `x` if one exists. Note that solutions modullo p
            // exists if `a` is quadratic residue modullo `p`. Recall that `a` in
            // `F_p` is quadratic residue if `a ^ ((p - 1) / 2) = 1 (mod p)`
            // by Euler criterion (https://en.wikipedia.org/wiki/Euler%27s_criterion)
            // or equivalently Legendre symbol `(a/p) = 1` so that solutions
            // to the equation `x ^ 2 = a (mod p)` exist.
            Self::Case3Mod4 {
                modulus_plus_one_div_four,
            } => {
                // if `p = 4k + 3` then `a ^ (2k + 1) = 1 (mod p)`. After multiplying by
                // `a` both sides of conjugation we obtain `a ^ (2k + 2) = a (mod p)` so
                // that `a ^ (2k + 2) = x ^ 2 (mod p)`. Now we can easily take square root
                // of both sides as every exponent is even: `x = +- a ^ (k + 1) (mod p)`.
                let result = elem.pow(modulus_plus_one_div_four.as_ref());
                (result.square() == *elem).then_some(result)
            },
            Self::Case5Mod8 {
                modulus_plus_three_div_eight,
                modulus_minus_one_div_four,
            } => {
                // When `p = 8k + 5`, we have `a ^ (4k + 2) = 1 (mod p)`.
                // Multiplying each side by `a` will not help since the exponent
                // will be odd. But instead, since `a ^ (4k + 2) = 1 ^ 2 = 1 (mod p)`
                // taking square root of `1` gives us either `a ^ (2k + 1) = 1 (mod p)`
                // or `a ^ (2k + 1) = -1 (mod p)`.

                if elem.is_zero() {
                    return Some(F::zero());
                }

                let result;

                // We have different solutions, if `a ^ (2k + 1)` is `1` or `-1`.
                let check_value = elem.pow(modulus_minus_one_div_four.as_ref());
                if check_value.is_one() {
                    // In this case, we can use the same technique as in `p = 4k + 3` case.
                    // After multiplying both sides by `a` we get
                    // `a ^ (2k + 2) = a = x ^ 2 (mod p)`
                    // so that `x = +- a ^ (k + 1) (mod p)`.
                    result = elem.pow(modulus_plus_three_div_eight.as_ref());
                } else if check_value.neg().is_one() {
                    // In this case we can not use the same technique, but recalling
                    // Tonneli-Shanks trick of multiplying each side by some non-residue
                    // we could obtain the square root. Firstly, `2` in `F_p` is always
                    // quadratic non-residue modullo `p` as by Legendre symbol properties
                    // (https://en.wikipedia.org/wiki/Legendre_symbol):
                    //      `(2/p) = (-1) ^ ((p ^ 2 - 1) / 8 )
                    //             = (-1) ^ (8k ^ 2 + 10 k + 3)
                    //             = -1`.
                    // By Euler criterion:
                    //      `2 ^ ((p - 1) / 2) = 2 ^ (4k + 2)
                    //                         = -1 (mod p)`.
                    // After multiplying both sides of `a ^ (2k + 1) = -1 (mod p)` by
                    // `2 ^ (4k + 2)` we get the following conjugation:
                    //      `a ^ (2k + 1) 2 ^ (4k + 2) = 1 (mod p)`.
                    // Multiplying both sides by `a` we get
                    //      `a ^ (2k + 2) 2 ^ (4k + 2) = a = x ^ 2 (mod p)`
                    // so that `x = +- a ^ (k+1) 2 ^ (2k + 1) (mod p)`.
                    let two: F = 2.into();
                    result = elem
                        .pow(modulus_plus_three_div_eight.as_ref())
                        .mul(two.pow(modulus_minus_one_div_four.as_ref()))
                } else {
                    return None;
                }

                (result.square() == *elem).then_some(result)
            },
        }
    }
}

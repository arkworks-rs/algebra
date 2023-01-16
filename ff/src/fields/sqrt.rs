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
    /// https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5).
    /// Tonelli-Shanks algorithm works for all elements, no matter what the modulus is.
    /// With _q_ as field order, _p_ as characteristic, and _m_ as extension degree:
    /// * First factor _q - 1 = 2^s t_ where _t_ is odd.
    /// * `two_adicity` - _s_.
    /// * `quadratic_nonresidue_to_trace` - _c^t_, with random _c_ such that _c^2^(s - 1) = 1_.
    /// * `trace_of_modulus_minus_one_div_two` - _(t - 1)/2 + 1_.
    TonelliShanks {
        two_adicity: u32,
        quadratic_nonresidue_to_trace: F,
        trace_of_modulus_minus_one_div_two: &'static [u64],
    },
    /// https://eprint.iacr.org/2012/685.pdf (page 9, algorithm 2).
    /// With _q_ as field order, _p_ as characteristic, and _m_ as extension degree:
    /// * `char_minus_three_div_four` - _(p - 3)/4_.
    /// * `deg_minus_three_div_two_plus_one` - _(m - 3)/2 + 1_.
    ShanksCase3Mod4 {
        char_minus_three_div_four: &'static [u64],
        deg_minus_three_div_two_plus_one: usize,
    },
    /// https://eprint.iacr.org/2012/685.pdf (page 10, algorithm 3).
    /// With _q_ as field order, _p_ as characteristic, and _m_ as extension degree:
    /// * `trace` - _2^(q - 5)/8_.
    /// * `char_minus_five_div_eight` - _(p - 5)/8_.
    /// * `deg_minus_three_div_two_plus_one` - _(m - 3)/2 + 1_.
    AtkinCase5Mod8 {
        trace: F,
        char_minus_five_div_eight: &'static [u64],
        deg_minus_three_div_two_plus_one: usize,
    },
    /// https://eprint.iacr.org/2012/685.pdf (page 11, algorithm 4).
    /// With _q_ as field order, _p_ as characteristic, and _m_ as extension degree:
    /// * `trace` - _2^(q - 9)/16_.
    /// * `c` - nonzero value such that _chi_q(c) != 1_.
    /// * `d` - _c^(q - 9)/8_.
    /// * `c_squared` - _c^2_.
    /// * `char_minus_nine_div_sixteen` - _(p - 9)/16_.
    /// * `deg_minus_three_div_two_plus_one` - _(m - 3)/2 + 1_.
    KongCase9Mod16 {
        trace: F,
        c: F,
        d: F,
        c_squared: F,
        char_minus_nine_div_sixteen: &'static [u64],
        deg_minus_three_div_two_plus_one: usize,
    },
    /// In the case of 3 mod 4, we can find the square root via an exponentiation,
    /// sqrt(a) = a^(p+1)/4. This can be proved using Euler's criterion, a^(p-1)/2 = 1 mod p.
    PowerCase3Mod4 {
        modulus_plus_one_div_four: &'static [u64],
    },
}

impl<F: crate::Field> SqrtPrecomputation<F> {
    pub fn sqrt(&self, elem: &F) -> Option<F> {
        match self {
            Self::TonelliShanks {
                two_adicity,
                quadratic_nonresidue_to_trace,
                trace_of_modulus_minus_one_div_two,
            } => tonelli_shanks(
                elem,
                two_adicity,
                quadratic_nonresidue_to_trace,
                trace_of_modulus_minus_one_div_two,
            ),
            SqrtPrecomputation::ShanksCase3Mod4 {
                char_minus_three_div_four,
                deg_minus_three_div_two_plus_one,
            } => shanks(
                elem,
                char_minus_three_div_four,
                *deg_minus_three_div_two_plus_one,
            ),
            SqrtPrecomputation::AtkinCase5Mod8 {
                trace,
                char_minus_five_div_eight,
                deg_minus_three_div_two_plus_one,
            } => atkin(
                elem,
                trace,
                char_minus_five_div_eight,
                *deg_minus_three_div_two_plus_one,
            ),
            SqrtPrecomputation::KongCase9Mod16 {
                trace,
                c,
                d,
                c_squared,
                char_minus_nine_div_sixteen,
                deg_minus_three_div_two_plus_one,
            } => kong(
                elem,
                trace,
                c,
                d,
                c_squared,
                char_minus_nine_div_sixteen,
                *deg_minus_three_div_two_plus_one,
            ),
            Self::PowerCase3Mod4 {
                modulus_plus_one_div_four,
            } => power_case_three_mod_four(elem, modulus_plus_one_div_four),
        }
    }
}

fn tonelli_shanks<F: crate::Field>(
    elem: &F,
    two_adicity: &u32,
    quadratic_nonresidue_to_trace: &F,
    trace_of_modulus_minus_one_div_two: &[u64],
) -> Option<F> {
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
}

fn shanks<F: crate::Field>(
    elem: &F,
    char_minus_three_div_four: &[u64],
    deg_minus_three_div_two_plus_one: usize,
) -> Option<F> {
    // Computing a1 = Using decomposition of (q-3)/4 = a + p[pa + (3a+2)] * sum_i=1^(m-3)/2 p^2i
    // where a = (p - 3) / 4.
    // factor1 = elem^a
    let factor1 = elem.pow(char_minus_three_div_four);
    // elem_to_p = elem^p
    let elem_to_p = elem.frobenius_map(1);
    // factor2_base = elem^(p^2)a * elem^3pa * elem^2p
    let factor2_base = elem_to_p.frobenius_map(1).pow(char_minus_three_div_four)
        * elem_to_p.pow(&[3u64]).pow(char_minus_three_div_four)
        * elem_to_p.square();
    // factor2 = prod_i=1^(m-3)/2 factor2_base^(p^2i)
    let mut factor2 = F::one();
    for i in 1..deg_minus_three_div_two_plus_one {
        factor2 *= factor2_base.frobenius_map(i * 2 as usize);
    }
    let a1 = factor1 * factor2;

    let a1_elem = a1 * elem;
    let a0 = a1 * a1_elem;
    if a0 == -F::one() {
        return None;
    }

    Some(a1_elem)
}

fn atkin<F: crate::Field>(
    elem: &F,
    trace: &F,
    char_minus_five_div_eight: &[u64],
    deg_minus_three_div_two_plus_one: usize,
) -> Option<F> {
    // Computing a1 = elem^(q-5)/8 using decomposition of
    // (q-5)/8 = a + p[pa + (5a+3)] * sum_i=1^(m-3)/2 p^2i
    // where a = (p - 5) / 8.
    // factor1 = elem^a
    let factor1 = elem.pow(char_minus_five_div_eight);
    // elem_to_p = elem^p
    let elem_to_p = elem.frobenius_map(1);
    // factor2_base = elem^(p^2)a * elem^5pa * elem^3p
    let factor2_base = elem_to_p.frobenius_map(1).pow(char_minus_five_div_eight)
        * elem_to_p.pow(&[5u64]).pow(char_minus_five_div_eight)
        * elem_to_p.pow(&[3u64]);
    // factor2 = prod_i=1^(m-3)/2 factor2_base^(p^2i)
    let mut factor2 = F::one();
    for i in 1..deg_minus_three_div_two_plus_one {
        factor2 *= factor2_base.frobenius_map(2 * i);
    }
    let a1 = factor1 * factor2;

    let a0 = (a1.square() * elem).square();
    if a0 == -F::one() {
        return None;
    }

    let b = a1 * trace;
    let elem_b = b * elem;
    let i = elem_b.double() * b;
    let x = elem_b * (i - F::one());

    Some(x)
}

fn kong<F: crate::Field>(
    elem: &F,
    trace: &F,
    c: &F,
    d: &F,
    c_squared: &F,
    char_minus_nine_div_sixteen: &[u64],
    deg_minus_three_div_two_plus_one: usize,
) -> Option<F> {
    // Using decomposition of (q-9)/16 = a + p[pa + (9a+5)] * sum_i=1^(m-3)/2 p^2i
    // a = (p - 9) / 16
    // factor1 = elem^a
    let factor1 = elem.pow(char_minus_nine_div_sixteen);
    // elem_to_p = elem^p
    let elem_to_p = elem.frobenius_map(1);
    // factor2_base = elem^(p^2)a * elem^9pa * elem^5p
    let factor2_base = elem_to_p.frobenius_map(1).pow(char_minus_nine_div_sixteen)
        * elem_to_p.pow(&[9u64]).pow(char_minus_nine_div_sixteen)
        * elem_to_p.pow(&[5u64]);
    // factor2 = prod_i=1^(m-3)/2 factor2_base^(p^2i)
    let mut factor2 = F::one();
    for i in 1..deg_minus_three_div_two_plus_one {
        factor2 *= factor2_base.frobenius_map(2 * i);
    }
    let a1 = factor1 * factor2;

    let a0 = (a1.square() * elem).pow(&[4u64]);
    if a0 == -F::one() {
        return None;
    }

    let b = a1 * trace;
    let elem_b = b * elem;
    let mut i = elem_b.double() * b;
    let r = i.square();
    if r == -F::one() {
        let x = elem_b * (i - F::one());
        return Some(x);
    }

    let u = b * d;
    i = u.square().double() * c_squared * elem;
    let x = u * c * elem * (i - F::one());
    Some(x)
}

fn power_case_three_mod_four<F: crate::Field>(
    elem: &F,
    modulus_plus_one_div_four: &[u64],
) -> Option<F> {
    let result = elem.pow(modulus_plus_one_div_four.as_ref());
    (result.square() == *elem).then_some(result)
}

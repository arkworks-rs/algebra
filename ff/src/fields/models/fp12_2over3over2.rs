use super::quadratic_extension::{QuadExtConfig, QuadExtField};
use crate::{
    fields::{
        fp6_3over2::{Fp6, Fp6Config},
        Field, Fp2, Fp2Config as Fp2ConfigTrait,
    },
    AdditiveGroup, CyclotomicMultSubgroup, Zero,
};
use core::{marker::PhantomData, ops::Not};

type Fp2Config<P> = <<P as Fp12Config>::Fp6Config as Fp6Config>::Fp2Config;

pub trait Fp12Config: 'static + Send + Sync + Copy {
    type Fp6Config: Fp6Config;

    /// This *must* equal (0, 1, 0);
    /// see [[DESD06, Section 6.1]](https://eprint.iacr.org/2006/471.pdf).
    const NONRESIDUE: Fp6<Self::Fp6Config>;

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP12_C1: &[Fp2<Fp2Config<Self>>];

    /// Multiply by quadratic nonresidue v.
    #[inline(always)]
    fn mul_fp6_by_nonresidue_in_place(fe: &mut Fp6<Self::Fp6Config>) -> &mut Fp6<Self::Fp6Config> {
        // see [[DESD06, Section 6.1]](https://eprint.iacr.org/2006/471.pdf).
        let old_c1 = fe.c1;
        fe.c1 = fe.c0;
        fe.c0 = fe.c2;
        Self::Fp6Config::mul_fp2_by_nonresidue_in_place(&mut fe.c0);
        fe.c2 = old_c1;
        fe
    }
}

pub struct Fp12ConfigWrapper<P: Fp12Config>(PhantomData<P>);

impl<P: Fp12Config> QuadExtConfig for Fp12ConfigWrapper<P> {
    type BasePrimeField = <Fp2Config<P> as Fp2ConfigTrait>::Fp;
    type BaseField = Fp6<P::Fp6Config>;
    type FrobCoeff = Fp2<Fp2Config<P>>;

    const DEGREE_OVER_BASE_PRIME_FIELD: usize = 12;

    const NONRESIDUE: Self::BaseField = P::NONRESIDUE;

    const FROBENIUS_COEFF_C1: &[Self::FrobCoeff] = P::FROBENIUS_COEFF_FP12_C1;

    #[inline(always)]
    fn mul_base_field_by_nonresidue_in_place(fe: &mut Self::BaseField) -> &mut Self::BaseField {
        P::mul_fp6_by_nonresidue_in_place(fe)
    }

    fn mul_base_field_by_frob_coeff(fe: &mut Self::BaseField, power: usize) {
        fe.mul_assign_by_fp2(Self::FROBENIUS_COEFF_C1[power % Self::DEGREE_OVER_BASE_PRIME_FIELD]);
    }
}

pub type Fp12<P> = QuadExtField<Fp12ConfigWrapper<P>>;

impl<P: Fp12Config> Fp12<P> {
    pub fn mul_by_fp(&mut self, element: &<Self as Field>::BasePrimeField) {
        self.c0.mul_by_fp(element);
        self.c1.mul_by_fp(element);
    }

    pub fn mul_by_034(
        &mut self,
        c0: &Fp2<Fp2Config<P>>,
        c3: &Fp2<Fp2Config<P>>,
        c4: &Fp2<Fp2Config<P>>,
    ) {
        let a0 = self.c0.c0 * c0;
        let a1 = self.c0.c1 * c0;
        let a2 = self.c0.c2 * c0;
        let a = Fp6::new(a0, a1, a2);
        let mut b = self.c1;
        b.mul_by_01(c3, c4);

        let c0 = *c0 + c3;
        let c1 = c4;
        let mut e = self.c0 + &self.c1;
        e.mul_by_01(&c0, c1);
        self.c1 = e - &(a + &b);
        self.c0 = b;
        P::mul_fp6_by_nonresidue_in_place(&mut self.c0);
        self.c0 += &a;
    }

    pub fn mul_by_014(
        &mut self,
        c0: &Fp2<Fp2Config<P>>,
        c1: &Fp2<Fp2Config<P>>,
        c4: &Fp2<Fp2Config<P>>,
    ) {
        let mut aa = self.c0;
        aa.mul_by_01(c0, c1);
        let mut bb = self.c1;
        bb.mul_by_1(c4);
        let mut o = *c1;
        o += c4;
        self.c1 += &self.c0;
        self.c1.mul_by_01(c0, &o);
        self.c1 -= &aa;
        self.c1 -= &bb;
        self.c0 = bb;
        P::mul_fp6_by_nonresidue_in_place(&mut self.c0);
        self.c0 += &aa;
    }

    #[inline(always)]
    fn fp4_square(
        a: &Fp2<Fp2Config<P>>,
        b: &Fp2<Fp2Config<P>>,
    ) -> (Fp2<Fp2Config<P>>, Fp2<Fp2Config<P>>) {
        let fp2_nr = <P::Fp6Config as Fp6Config>::mul_fp2_by_nonresidue;
        let tmp = *a * b;
        let c0 = (*a + b) * &(fp2_nr(*b) + a) - &tmp - &fp2_nr(tmp);
        let c1 = tmp.double();
        (c0, c1)
    }

    fn cyclotomic_exp_granger_scott_naf(&mut self, naf: &[i8]) {
        let Some(top) = naf.iter().rposition(|&d| d != 0) else {
            *self = Self::ONE;
            return;
        };
        let mut self_inv = *self;
        self_inv.conjugate_in_place();

        let mut res = if naf[top] > 0 { *self } else { self_inv };
        for &digit in naf[..top].iter().rev() {
            res.cyclotomic_square_in_place();
            if digit > 0 {
                res *= &*self;
            } else if digit < 0 {
                res *= &self_inv;
            }
        }
        *self = res;
    }

    fn cyclotomic_exp_uncompressed_in_place(&mut self, limbs: &[u64]) {
        let Some(top_idx) = limbs.iter().rposition(|&w| w != 0) else {
            *self = Self::ONE;
            return;
        };
        let total_bits = top_idx * 64 + (64 - limbs[top_idx].leading_zeros() as usize);
        if total_bits <= STACK_NAF_MAX_BITS {
            let mut naf_buf = [0i8; STACK_NAF_MAX_BITS + 1];
            let (naf_len, _) = compute_naf_stack(limbs, total_bits, &mut naf_buf);
            self.cyclotomic_exp_granger_scott_naf(&naf_buf[..naf_len]);
            return;
        }

        let mut res_opt: Option<Self> = None;
        let mut cur = *self;
        let mut carry = 0u8;
        let mut k = 0usize;
        while k < total_bits || carry != 0 {
            if k > 0 {
                cur.cyclotomic_square_in_place();
            }
            let z_k = next_naf_digit(limbs, k, &mut carry);
            if z_k != 0 {
                let mut factor = cur;
                if z_k < 0 {
                    factor.conjugate_in_place();
                }
                match &mut res_opt {
                    Some(res) => *res *= &factor,
                    None => res_opt = Some(factor),
                }
            }
            k += 1;
        }
        *self = res_opt.unwrap_or(Self::ONE);
    }

    fn cyclotomic_exp_karabina_in_place(&mut self, limbs: &[u64], total_bits: usize) {
        let mut carry = 0u8;
        let z0 = next_naf_digit(limbs, 0, &mut carry);
        let mut res_opt = if z0 > 0 {
            Some(*self)
        } else if z0 < 0 {
            let mut inv0 = *self;
            inv0.conjugate_in_place();
            Some(inv0)
        } else {
            None
        };

        let mut comp = KarabinaCompressed::<P> {
            z2: self.c1.c0,
            z3: self.c0.c2,
            z4: self.c0.c1,
            z5: self.c1.c2,
        };
        let mut buf_comp = [KarabinaCompressed::<P>::default(); KARABINA_BATCH_SIZE];
        let mut buf_neg = [false; KARABINA_BATCH_SIZE];
        let mut buf_len = 0usize;

        let mut k = 1usize;
        while k < total_bits || carry != 0 {
            comp = comp.square();
            let z_k = next_naf_digit(limbs, k, &mut carry);

            if z_k != 0 {
                if comp.z2.is_zero() && comp.z3.is_zero() {
                    if comp.z4.is_zero() && comp.z5.is_zero() {
                        if res_opt.is_none() {
                            res_opt = Some(Self::ONE);
                        }
                    } else {
                        self.cyclotomic_exp_uncompressed_in_place(limbs);
                        return;
                    }
                } else {
                    buf_comp[buf_len] = comp;
                    buf_neg[buf_len] = z_k < 0;
                    buf_len += 1;
                    if buf_len == KARABINA_BATCH_SIZE {
                        if !Self::flush_karabina_batch(
                            &buf_comp[..KARABINA_BATCH_SIZE],
                            &buf_neg[..KARABINA_BATCH_SIZE],
                            &mut res_opt,
                        ) {
                            self.cyclotomic_exp_uncompressed_in_place(limbs);
                            return;
                        }
                        buf_len = 0;
                    }
                }
            }
            k += 1;
        }

        if buf_len > 0
            && !Self::flush_karabina_batch(&buf_comp[..buf_len], &buf_neg[..buf_len], &mut res_opt)
        {
            self.cyclotomic_exp_uncompressed_in_place(limbs);
            return;
        }

        *self = res_opt.unwrap_or(Self::ONE);
    }

    fn flush_karabina_batch(
        comps: &[KarabinaCompressed<P>],
        neg_flags: &[bool],
        res_opt: &mut Option<Self>,
    ) -> bool {
        let n = comps.len();
        if n == 0 {
            return true;
        }
        debug_assert!(n <= KARABINA_BATCH_SIZE);

        let mut denoms = [Fp2::<Fp2Config<P>>::ZERO; KARABINA_BATCH_SIZE];
        let mut prods = [Fp2::<Fp2Config<P>>::ZERO; KARABINA_BATCH_SIZE];
        let mut is_case1 = [false; KARABINA_BATCH_SIZE];
        let mut acc = Fp2::<Fp2Config<P>>::ONE;

        for i in 0..n {
            let c = &comps[i];
            if c.z2.is_zero() {
                denoms[i] = c.z3;
                is_case1[i] = false;
            } else {
                denoms[i] = c.z2.double().double();
                is_case1[i] = true;
            }
            if i == 0 {
                acc = denoms[0];
            } else {
                acc *= &denoms[i];
            }
            prods[i] = acc;
        }

        let Some(mut inv_acc) = acc.inverse() else {
            return false;
        };

        let mut d_invs = [Fp2::<Fp2Config<P>>::ZERO; KARABINA_BATCH_SIZE];
        for i in (1..n).rev() {
            d_invs[i] = inv_acc * &prods[i - 1];
            inv_acc *= &denoms[i];
        }
        d_invs[0] = inv_acc;

        let fp2_nr = <P::Fp6Config as Fp6Config>::mul_fp2_by_nonresidue;
        for i in 0..n {
            let c = &comps[i];
            let z1 = if is_case1[i] {
                let z4s = c.z4.square();
                let uz5s = fp2_nr(c.z5.square());
                let num = uz5s + &z4s.double() + &z4s - &c.z3.double();
                num * &d_invs[i]
            } else {
                (c.z4 * &c.z5).double() * &d_invs[i]
            };
            let z34 = c.z3 * &c.z4;
            let mut inner = z1.square().double() - &(z34.double() + &z34);
            if is_case1[i] {
                inner += &(c.z2 * &c.z5);
            }
            let z0 = fp2_nr(inner) + &Fp2::<Fp2Config<P>>::ONE;
            let mut elem = Self::new(Fp6::new(z0, c.z4, c.z3), Fp6::new(c.z2, z1, c.z5));
            if neg_flags[i] {
                elem.conjugate_in_place();
            }
            match res_opt {
                Some(res) => *res *= &elem,
                None => *res_opt = Some(elem),
            }
        }
        true
    }
}

const KARABINA_BATCH_SIZE: usize = 16;
const STACK_NAF_MAX_BITS: usize = 512;

#[inline(always)]
const fn get_bit_le(limbs: &[u64], bit_idx: usize) -> u8 {
    let word_idx = bit_idx >> 6;
    if word_idx < limbs.len() {
        ((limbs[word_idx] >> (bit_idx & 63)) & 1) as u8
    } else {
        0
    }
}

#[inline(always)]
const fn next_naf_digit(limbs: &[u64], k: usize, carry: &mut u8) -> i8 {
    let sum = get_bit_le(limbs, k) + *carry;
    if sum == 0 {
        *carry = 0;
        0
    } else if sum == 2 {
        *carry = 1;
        0
    } else if get_bit_le(limbs, k + 1) != 0 {
        *carry = 1;
        -1
    } else {
        *carry = 0;
        1
    }
}

#[inline]
const fn compute_naf_stack(
    limbs: &[u64],
    total_bits: usize,
    out_naf: &mut [i8; STACK_NAF_MAX_BITS + 1],
) -> (usize, usize) {
    let mut carry = 0u8;
    let mut k = 0usize;
    let mut internal_weight = 0usize;
    while k < total_bits || carry != 0 {
        let d = next_naf_digit(limbs, k, &mut carry);
        out_naf[k] = d;
        if k > 0 && d != 0 {
            internal_weight += 1;
        }
        k += 1;
    }
    (k, internal_weight)
}

#[inline]
const fn count_internal_naf_weight(limbs: &[u64], total_bits: usize) -> usize {
    let mut carry = 0u8;
    let mut k = 0usize;
    let mut internal_weight = 0usize;
    while k < total_bits || carry != 0 {
        let d = next_naf_digit(limbs, k, &mut carry);
        if k > 0 && d != 0 {
            internal_weight += 1;
        }
        k += 1;
    }
    internal_weight
}

#[derive(educe::Educe)]
#[educe(Copy, Clone, Default)]
struct KarabinaCompressed<P: Fp12Config> {
    z2: Fp2<Fp2Config<P>>,
    z3: Fp2<Fp2Config<P>>,
    z4: Fp2<Fp2Config<P>>,
    z5: Fp2<Fp2Config<P>>,
}

impl<P: Fp12Config> KarabinaCompressed<P> {
    #[inline(always)]
    fn square(self) -> Self {
        let (t2, t3) = Fp12::<P>::fp4_square(&self.z2, &self.z3);
        let (t4, t5) = Fp12::<P>::fp4_square(&self.z4, &self.z5);
        let nr_t5 = <P::Fp6Config as Fp6Config>::mul_fp2_by_nonresidue(t5);
        Self {
            z2: (nr_t5 + &self.z2).double() + &nr_t5,
            z3: (t4 - &self.z3).double() + &t4,
            z4: (t2 - &self.z4).double() + &t2,
            z5: (t3 + &self.z5).double() + &t3,
        }
    }
}

pub const fn characteristic_square_mod_6_is_one(characteristic: &[u64]) -> bool {
    // char mod 6 = (a_0 + 2**64 * a_1 + ...) mod 6
    //            = a_0 mod 6 + (2**64 * a_1 mod 6) + (...) mod 6
    //            = a_0 mod 6 + (4 * a_1 mod 6) + (4 * ...) mod 6
    let mut char_mod_6 = 0u64;
    crate::const_for!((i in 0..(characteristic.len())) {
        char_mod_6 += if i == 0 {
            characteristic[i] % 6
        } else {
            (4 * (characteristic[i] % 6)) % 6
        };
    });
    (char_mod_6 * char_mod_6) % 6 == 1
}

impl<P: Fp12Config> CyclotomicMultSubgroup for Fp12<P> {
    const INVERSE_IS_FAST: bool = true;

    fn cyclotomic_inverse_in_place(&mut self) -> Option<&mut Self> {
        self.is_zero().not().then(|| self.conjugate_in_place())
    }

    fn cyclotomic_square_in_place(&mut self) -> &mut Self {
        // Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions
        // - Robert Granger and Michael Scott
        //
        if characteristic_square_mod_6_is_one(Self::characteristic()) {
            let fp2_nr = <P::Fp6Config as Fp6Config>::mul_fp2_by_nonresidue;

            let (t0, t1) = Self::fp4_square(&self.c0.c0, &self.c1.c1);
            let (t2, t3) = Self::fp4_square(&self.c1.c0, &self.c0.c2);
            let (t4, t5) = Self::fp4_square(&self.c0.c1, &self.c1.c2);

            let z0 = &mut self.c0.c0;
            let z4 = &mut self.c0.c1;
            let z3 = &mut self.c0.c2;
            let z2 = &mut self.c1.c0;
            let z1 = &mut self.c1.c1;
            let z5 = &mut self.c1.c2;

            // for A: z0 = 3 * t0 - 2 * z0, z1 = 3 * t1 + 2 * z1
            *z0 = t0 - &*z0;
            z0.double_in_place();
            *z0 += &t0;

            *z1 = t1 + &*z1;
            z1.double_in_place();
            *z1 += &t1;

            // for B: z2 = 3 * (xi * t5) + 2 * z2, z3 = 3 * t4 - 2 * z3
            let tmp = fp2_nr(t5);
            *z2 += tmp;
            z2.double_in_place();
            *z2 += &tmp;

            *z3 = t4 - &*z3;
            z3.double_in_place();
            *z3 += &t4;

            // for C: z4 = 3 * t2 - 2 * z4, z5 = 3 * t3 + 2 * z5
            *z4 = t2 - &*z4;
            z4.double_in_place();
            *z4 += &t2;

            *z5 += t3;
            z5.double_in_place();
            *z5 += &t3;
            self
        } else {
            self.square_in_place()
        }
    }

    fn cyclotomic_exp_in_place(&mut self, e: impl AsRef<[u64]>) {
        if self.is_zero() {
            return;
        }

        let limbs = e.as_ref();
        let Some(top_idx) = limbs.iter().rposition(|&w| w != 0) else {
            *self = Self::ONE;
            return;
        };
        let limbs = &limbs[..=top_idx];

        if !characteristic_square_mod_6_is_one(Self::characteristic())
            || (self.c1.c0.is_zero() && self.c0.c2.is_zero())
        {
            self.cyclotomic_exp_uncompressed_in_place(limbs);
            return;
        }

        let total_bits = top_idx * 64 + (64 - limbs[top_idx].leading_zeros() as usize);
        if total_bits == 1 {
            return;
        }

        // Karabina compressed squaring saves 2 Fp2 muls per bit while batch decompression costs
        // ~8.5 Fp2 muls per nonzero NAF digit (crossover density W / L <= 1/4).
        // For sparse exponents (`BLS12-377`, `BLS12-381`, `2^k - 1`, etc.), run Karabina +
        // 16-slot stack-batched Montgomery decompression; for dense scalars, run zero-allocation
        // stack-buffered Granger-Scott NAF.
        if total_bits <= STACK_NAF_MAX_BITS {
            let mut naf_buf = [0i8; STACK_NAF_MAX_BITS + 1];
            let (naf_len, internal_weight) = compute_naf_stack(limbs, total_bits, &mut naf_buf);
            if 4 * internal_weight <= total_bits {
                self.cyclotomic_exp_karabina_in_place(limbs, total_bits);
            } else {
                self.cyclotomic_exp_granger_scott_naf(&naf_buf[..naf_len]);
            }
        } else if 4 * count_internal_naf_weight(limbs, total_bits) <= total_bits {
            self.cyclotomic_exp_karabina_in_place(limbs, total_bits);
        } else {
            self.cyclotomic_exp_uncompressed_in_place(limbs);
        }
    }
}

#[cfg(test)]
mod test {
    use super::characteristic_square_mod_6_is_one;
    use ark_std::test_rng;
    use ark_test_curves::{
        ark_ff::{
            AdditiveGroup, CyclotomicMultSubgroup, Field, Fp6Config, One, PrimeField, UniformRand,
            Zero,
        },
        bls12_381::{Fq, Fq12, Fq2, Fq6, Fq6Config as Bls381Fq6Config},
    };
    use num_bigint::BigUint;

    fn sample_cyclotomic_bls12_381(rng: &mut impl ark_std::rand::Rng) -> Fq12 {
        loop {
            let x = Fq12::rand(rng);
            if let Some(inv_x) = x.inverse() {
                let mut conj_x = x;
                conj_x.conjugate_in_place();
                // r = x^(q^6 - 1)
                let r = conj_x * &inv_x;
                // g = r^(q^2 + 1) in G_{Phi_6(q^2)}
                let mut r_q2 = r;
                r_q2.frobenius_map_in_place(2);
                let g = r_q2 * &r;
                if !g.is_one() {
                    return g;
                }
            }
        }
    }

    #[test]
    fn test_characteristic_square_mod_6_is_one() {
        assert!(!characteristic_square_mod_6_is_one(&[36]));
        assert!(characteristic_square_mod_6_is_one(&[37]));
        assert!(!characteristic_square_mod_6_is_one(&[38]));
        assert!(!characteristic_square_mod_6_is_one(&[39]));
        assert!(!characteristic_square_mod_6_is_one(&[40]));
        assert!(characteristic_square_mod_6_is_one(&[41]));

        assert!(!characteristic_square_mod_6_is_one(&[36, 36]));
        assert!(!characteristic_square_mod_6_is_one(&[36, 37]));
        assert!(!characteristic_square_mod_6_is_one(&[36, 38]));
        assert!(!characteristic_square_mod_6_is_one(&[36, 39]));
        assert!(!characteristic_square_mod_6_is_one(&[36, 40]));
        assert!(!characteristic_square_mod_6_is_one(&[36, 41]));

        assert!(!characteristic_square_mod_6_is_one(&[36, 41]));
        assert!(!characteristic_square_mod_6_is_one(&[37, 41]));
        assert!(!characteristic_square_mod_6_is_one(&[38, 41]));
        assert!(characteristic_square_mod_6_is_one(&[39, 41]));
        assert!(!characteristic_square_mod_6_is_one(&[40, 41]));
        assert!(characteristic_square_mod_6_is_one(&[41, 41]));
        assert!(characteristic_square_mod_6_is_one(&[1, u64::MAX]));
    }

    #[test]
    fn test_karabina_cyclotomic_exp_edge_and_high_weight_exponents() {
        let mut rng = test_rng();
        let g = sample_cyclotomic_bls12_381(&mut rng);

        // Edge cases including 0, 1, 17-set-bit clear-bit-0 regression `[0x0002_aaaa_aaaa_0000]`,
        // all-ones NAF carry across limb boundaries, curve seeds, and multi-chunk 256-bit scalars.
        let fixed_exponents: &[&[u64]] = &[
            &[],
            &[0],
            &[1],
            &[2],
            &[3],
            &[6],
            &[0x0002_aaaa_aaaa_0000],
            &[0x0003_aaaa_aaaa_0000],
            &[0x0002_aaaa_aaaa_0001],
            &[0x5555_5555_5555_5555],
            &[0xaaaa_aaaa_aaaa_aaaa],
            &[u64::MAX],
            &[u64::MAX, u64::MAX],
            &[0, 1],
            &[1, 0, 0, 1],
            &[0xd201_0000_0001_0000],
            &[0x8508_c000_0000_0001],
            &[0x44e9_92b4_4a69_09f1],
            &[0x0002_aaaa_aaaa_0000, 0, 0, 0, 1], // 18 internal NAF digits across 257 bits -> 2 Karabina batch flushes (16 + 2)
            &[1, 0, 0, 0, 0, 0, 0, 0, 1],         // > 512-bit exponent
            &[
                0x5555_5555_5555_5555,
                0xaaaa_aaaa_aaaa_aaaa,
                0x5555_5555_5555_5555,
                0xaaaa_aaaa_aaaa_aaaa,
            ],
        ];

        assert_eq!(Fq12::ZERO.cyclotomic_exp([5u64]), Fq12::ZERO);
        assert_eq!(
            Fq12::ONE.cyclotomic_exp([0x0002_aaaa_aaaa_0000u64]),
            Fq12::ONE
        );

        for &exp in fixed_exponents {
            assert_eq!(
                g.cyclotomic_exp(exp),
                g.pow(exp),
                "Karabina cyclotomic_exp mismatch for exp={exp:x?}"
            );
        }

        for _ in 0..32 {
            let h = sample_cyclotomic_bls12_381(&mut rng);
            let exp: [u64; 4] = [
                u64::rand(&mut rng),
                u64::rand(&mut rng),
                u64::rand(&mut rng),
                u64::rand(&mut rng),
            ];
            assert_eq!(h.cyclotomic_exp(exp), h.pow(exp));
        }
    }

    #[test]
    fn test_karabina_nontrivial_z2_zero_z3_nonzero_branch() {
        // Deterministic genus-0 rational point on G_{Phi_6(q^2)} \cap {z2 = 0, z3 != 0}:
        //   xi * z3^3 - 6 * z4 * z3 + 8 * z4^3 = 0  ==>  z3 = 6m / (xi + 8m^3), z4 = m * z3.
        let xi = Bls381Fq6Config::NONRESIDUE;
        let xi_inv = xi.inverse().unwrap();
        let mut g_opt = None;
        for m_c0 in 1u64..64 {
            let m = Fq2::new(Fq::from(m_c0), Fq::ONE);
            let m3 = m.square() * &m;
            let Some(den_inv) = (xi + &(Fq2::from(8u8) * &m3)).inverse() else {
                continue;
            };
            let z3 = (Fq2::from(6u8) * &m) * &den_inv;
            if z3.is_zero() {
                continue;
            }
            let z4 = m * &z3;
            let z4_sq = z4.square();
            let rhs = (z3.double() - &(z4_sq.double() + &z4_sq)) * &xi_inv;
            if let Some(z5) = rhs.sqrt() {
                let z1 = (m * &z5).double();
                let z34 = z3 * &z4;
                let inner = z1.square().double() - &(z34.double() + &z34);
                let z0 = Bls381Fq6Config::mul_fp2_by_nonresidue(inner) + &Fq2::ONE;
                g_opt = Some(Fq12::new(Fq6::new(z0, z4, z3), Fq6::new(Fq2::ZERO, z1, z5)));
                break;
            }
        }
        let g = g_opt.expect("must find deterministic z2 == 0, z3 != 0 witness in G_{Phi_6(q^2)}");
        assert!(g.c1.c0.is_zero() && !g.c0.c2.is_zero());

        // Verify g lies in G_{Phi_6(q^2)} of odd order q^4 - q^2 + 1 and compute its square root h:
        // h^2 == g has h.z2 != 0 while its first Karabina squaring lands directly on z2 == 0, z3 != 0!
        let q: BigUint = Fq::MODULUS.into();
        let q2 = &q * &q;
        let phi6 = &q2 * &q2 - &q2 + 1u32;
        assert!(g.pow(phi6.to_u64_digits()).is_one());

        let half_exp = ((&phi6 + 1u32) >> 1usize).to_u64_digits();
        let h = g.pow(&half_exp);
        let h2 = h.pow(&half_exp);
        assert!(!h.c1.c0.is_zero());
        assert_eq!(h.square(), g);
        assert_eq!(h2.square(), h);

        // Exponents hitting z_k = +1 and z_k = -1 at k = 1 (comp == g) and k = 2 (comp == g)
        // on BOTH dense Granger-Scott NAF and sparse Karabina batch decompression (`4 * W <= L`):
        for exp in [
            &[2u64][..],
            &[3u64][..],
            &[4u64][..],
            &[6u64][..],
            &[0x102u64][..], // 2^8 + 2 (L=9, W=2 => Karabina path, z_1 = +1 at comp == g!)
            &[0x1feu64][..], // 2^9 - 2 (L=9, W=2 => Karabina path, z_1 = -1 at comp == g!)
            &[0x204u64][..], // 2^9 + 4 (L=10, W=2 => Karabina path, z_2 = +1 at comp == g for h2!)
            &[0x1fcu64][..], // 2^9 - 4 (L=9, W=2 => Karabina path, z_2 = -1 at comp == g for h2!)
            &[0x0002_aaaa_aaaa_0002u64, 0, 0, 0, 1][..],
            &[u64::MAX][..],
        ] {
            assert_eq!(g.cyclotomic_exp(exp), g.pow(exp));
            assert_eq!(h.cyclotomic_exp(exp), h.pow(exp));
            assert_eq!(h2.cyclotomic_exp(exp), h2.pow(exp));
        }
    }
}

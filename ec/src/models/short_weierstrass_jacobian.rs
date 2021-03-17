use ark_serialize::{
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, SWFlags, SerializationError,
};
use ark_std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign},
    vec::Vec,
};

use ark_ff::{
    biginteger::BigInteger,
    bytes::{FromBytes, ToBytes},
    fields::{BitIteratorBE, Field, PrimeField, SquareRootField},
    ToConstraintField, UniformRand,
};

use crate::{
    batch_arith::{decode_endo_from_u32, BatchGroupArithmetic, ENDO_CODING_BITS},
    AffineCurve, ModelParameters, ProjectiveCurve,
};

use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub trait SWModelParameters: ModelParameters + Sized {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;
    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    #[inline(always)]
    fn glv_window_size() -> usize {
        4
    }

    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy += &Self::COEFF_B;
        copy
    }

    #[inline(always)]
    fn has_glv() -> bool {
        false
    }

    #[inline(always)]
    fn glv_endomorphism_in_place(_elem: &mut Self::BaseField) {
        unimplemented!()
    }

    #[inline(always)]
    fn glv_scalar_decomposition(
        _k: <Self::ScalarField as PrimeField>::BigInt,
    ) -> (
        (bool, <Self::ScalarField as PrimeField>::BigInt),
        (bool, <Self::ScalarField as PrimeField>::BigInt),
    ) {
        unimplemented!()
    }
}

/// Implements GLV mul for a single element with a wNAF tables
#[macro_export]
macro_rules! impl_glv_mul {
    ($Projective: ty, $P: ident, $w: ident, $self_proj: ident, $res: ident, $by: ident) => {
        // In the future, make this a GLV parameter entry
        let wnaf_recoding =
            |s: &mut <Self::ScalarField as PrimeField>::BigInt, is_neg: bool| -> Vec<i16> {
                let window_size: i16 = 1 << ($w + 1);
                let half_window_size: i16 = 1 << $w;

                let mut recoding = Vec::<i16>::with_capacity(s.num_bits() as usize / ($w + 1));

                while !s.is_zero() {
                    let op = if s.is_odd() {
                        let mut z: i16 = (s.as_ref()[0] % (1 << ($w + 1))) as i16;

                        if z < half_window_size {
                            s.sub_noborrow(&(z as u64).into());
                        } else {
                            z = z - window_size;
                            s.add_nocarry(&((-z) as u64).into());
                        }
                        if is_neg {
                            -z
                        } else {
                            z
                        }
                    } else {
                        0
                    };
                    recoding.push(op);
                    s.div2();
                }
                recoding
            };

        let ((k1_neg, mut k1), (k2_neg, mut k2)) = $P::glv_scalar_decomposition($by.into());
        let mut wnaf_table_k1 = Vec::<$Projective>::with_capacity(1 << $w);
        let double = $self_proj.double();
        wnaf_table_k1.push($self_proj);
        for _ in 1..(1 << ($w - 1)) {
            wnaf_table_k1.push(*wnaf_table_k1.last().unwrap() + &double);
        }
        let mut wnaf_table_k2 = wnaf_table_k1.clone();
        wnaf_table_k2
            .iter_mut()
            .for_each(|p| $P::glv_endomorphism_in_place(&mut p.x));

        let k1_ops = wnaf_recoding(&mut k1, k1_neg);
        let k2_ops = wnaf_recoding(&mut k2, k2_neg);

        if k1_ops.len() > k2_ops.len() {
            for &op in k1_ops[k2_ops.len()..].iter().rev() {
                $res.double_in_place();
                if op > 0 {
                    $res += &wnaf_table_k1[(op as usize) / 2];
                } else if op < 0 {
                    $res += &wnaf_table_k1[(-op as usize) / 2].neg();
                }
            }
        } else {
            for &op in k2_ops[k1_ops.len()..].iter().rev() {
                $res.double_in_place();
                if op > 0 {
                    $res += &wnaf_table_k2[(op as usize) / 2];
                } else if op < 0 {
                    $res += &wnaf_table_k2[(-op as usize) / 2].neg();
                }
            }
        }
        for (&op1, &op2) in k1_ops.iter().zip(k2_ops.iter()).rev() {
            $res.double_in_place();
            if op1 > 0 {
                $res += &wnaf_table_k1[(op1 as usize) / 2];
            } else if op1 < 0 {
                $res += &wnaf_table_k1[(-op1 as usize) / 2].neg();
            }
            if op2 > 0 {
                $res += &wnaf_table_k2[(op2 as usize) / 2];
            } else if op2 < 0 {
                $res += &wnaf_table_k2[(-op2 as usize) / 2].neg();
            }
        }
    };
}

use SWModelParameters as Parameters;

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    PartialEq(bound = "P: Parameters"),
    Eq(bound = "P: Parameters"),
    Debug(bound = "P: Parameters"),
    Hash(bound = "P: Parameters")
)]
#[must_use]
pub struct GroupAffine<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub infinity: bool,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P: Parameters> PartialEq<GroupProjective<P>> for GroupAffine<P> {
    fn eq(&self, other: &GroupProjective<P>) -> bool {
        self.into_projective() == *other
    }
}

impl<P: Parameters> PartialEq<GroupAffine<P>> for GroupProjective<P> {
    fn eq(&self, other: &GroupAffine<P>) -> bool {
        *self == other.into_projective()
    }
}

impl<P: Parameters> Display for GroupAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.infinity {
            write!(f, "GroupAffine(Infinity)")
        } else {
            write!(f, "GroupAffine(x={}, y={})", self.x, self.y)
        }
    }
}

impl<P: Parameters> GroupAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, infinity: bool) -> Self {
        Self {
            x,
            y,
            infinity,
            _params: PhantomData,
        }
    }

    pub fn scale_by_cofactor(&self) -> GroupProjective<P> {
        let cofactor = BitIteratorBE::new(P::COFACTOR);
        self.mul_bits(cofactor)
    }

    /// Multiplies `self` by the scalar represented by `bits`. `bits` must be a big-endian
    /// bit-wise decomposition of the scalar.
    pub(crate) fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> GroupProjective<P> {
        let mut res = GroupProjective::zero();
        // Skip leading zeros.
        for i in bits.skip_while(|b| !b) {
            res.double_in_place();
            if i {
                res.add_assign_mixed(&self)
            }
        }
        res
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    #[allow(dead_code)]
    pub fn get_point_from_x(x: P::BaseField, greatest: bool) -> Option<Self> {
        // Compute x^3 + ax + b
        let x3b = P::add_b(&((x.square() * &x) + &P::mul_by_a(&x)));

        x3b.sqrt().map(|y| {
            let negy = -y;

            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new(x, y, false)
        })
    }

    pub fn is_on_curve(&self) -> bool {
        if self.is_zero() {
            true
        } else {
            // Check that the point is on the curve
            let y2 = self.y.square();
            let x3b = P::add_b(&((self.x.square() * &self.x) + &P::mul_by_a(&self.x)));
            y2 == x3b
        }
    }

    pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.mul_bits(BitIteratorBE::new(P::ScalarField::characteristic()))
            .is_zero()
    }
}

impl<P: Parameters> Zeroize for GroupAffine<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.infinity.zeroize();
    }
}

impl<P: Parameters> Zero for GroupAffine<P> {
    #[inline]
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one(), true)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl<P: Parameters> Add<Self> for GroupAffine<P> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut copy = self;
        copy += &other;
        copy
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for GroupAffine<P> {
    fn add_assign(&mut self, other: &'a Self) {
        let mut s_proj = GroupProjective::from(*self);
        s_proj.add_assign_mixed(other);
        *self = s_proj.into();
    }
}

impl<P: Parameters> AffineCurve for GroupAffine<P> {
    const COFACTOR: &'static [u64] = P::COFACTOR;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Projective = GroupProjective<P>;

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Self::new(
            P::AFFINE_GENERATOR_COEFFS.0,
            P::AFFINE_GENERATOR_COEFFS.1,
            false,
        )
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<SWFlags>(bytes).and_then(|(x, flags)| {
            // if x is valid and is zero and only the infinity flag is set, then parse this
            // point as infinity. For all other choices, get the original point.
            if x.is_zero() && flags.is_infinity() {
                Some(Self::zero())
            } else if let Some(y_is_positive) = flags.is_positive() {
                Self::get_point_from_x(x, y_is_positive) // Unwrap is safe because it's not zero.
            } else {
                None
            }
        })
    }

    #[inline]
    fn mul<S: Into<<Self::ScalarField as PrimeField>::BigInt>>(&self, by: S) -> Self::Projective {
        if P::has_glv() {
            let w = P::glv_window_size();
            let mut res = Self::Projective::zero();
            let self_proj = self.into_projective();
            impl_glv_mul!(Self::Projective, P, w, self_proj, res, by);
            res
        } else {
            let bits = BitIteratorBE::new(by.into());
            self.mul_bits(bits)
        }
    }

    #[inline]
    fn mul_by_cofactor_to_projective(&self) -> Self::Projective {
        self.scale_by_cofactor()
    }

    fn mul_by_cofactor_inv(&self) -> Self {
        self.mul(P::COFACTOR_INV).into()
    }
}

impl<P: Parameters> Neg for GroupAffine<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if !self.is_zero() {
            Self::new(self.x, -self.y, false)
        } else {
            self
        }
    }
}

impl<P: Parameters> ToBytes for GroupAffine<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)?;
        self.infinity.write(&mut writer)
    }
}

impl<P: Parameters> FromBytes for GroupAffine<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let infinity = bool::read(reader)?;
        Ok(Self::new(x, y, infinity))
    }
}

impl<P: Parameters> Default for GroupAffine<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

#[cfg(feature = "prefetch")]
macro_rules! prefetch_slice {
    ($slice_1: ident, $slice_2: ident, $prefetch_iter: ident) => {
        if let Some((idp_1, idp_2)) = $prefetch_iter.next() {
            prefetch::<Self>(&mut $slice_1[*idp_1 as usize]);
            prefetch::<Self>(&mut $slice_2[*idp_2 as usize]);
        }
    };

    ($slice_1: ident, $prefetch_iter: ident) => {
        if let Some((idp_1, _)) = $prefetch_iter.next() {
            prefetch::<Self>(&mut $slice_1[*idp_1 as usize]);
        }
    };
}

#[cfg(feature = "prefetch")]
macro_rules! prefetch_slice_endo {
    ($slice_1: ident, $slice_2: ident, $prefetch_iter: ident) => {
        if let Some((idp_1, idp_2)) = $prefetch_iter.next() {
            let (idp_2, _) = decode_endo_from_u32(*idp_2);
            prefetch::<Self>(&mut $slice_1[*idp_1 as usize]);
            prefetch::<Self>(&$slice_2[idp_2]);
        }
    };
}

#[cfg(feature = "prefetch")]
macro_rules! prefetch_slice_write {
    ($slice_1: ident, $slice_2: ident, $prefetch_iter: ident) => {
        if let Some((idp_1, idp_2)) = $prefetch_iter.next() {
            prefetch::<Self>(&$slice_1[*idp_1 as usize]);
            if *idp_2 != !0u32 {
                prefetch::<Self>(&$slice_2[*idp_2 as usize]);
            }
        }
    };
}

macro_rules! batch_add_loop_1 {
    ($a: ident, $b: ident, $half: ident, $inversion_tmp: ident) => {
        if $a.is_zero() || $b.is_zero() {
            ();
        } else if $a.x == $b.x {
            $half = match $half {
                None => P::BaseField::one().double().inverse(),
                _ => $half,
            };
            let h = $half.unwrap();

            // Double
            // In our model, we consider self additions rare.
            // So we consider it inconsequential to make them more expensive
            // This costs 1 modular mul more than a standard squaring,
            // and one amortised inversion
            if $a.y == $b.y {
                let x_sq = $b.x.square();
                $b.x -= &$b.y; // x - y
                $a.x = $b.y.double(); // denominator = 2y
                $a.y = x_sq.double() + &x_sq + &P::COEFF_A; // numerator = 3x^2 + a
                $b.y -= &(h * &$a.y); // y - (3x^2 + $a./2
                $a.y *= &$inversion_tmp; // (3x^2 + a) * tmp
                $inversion_tmp *= &$a.x; // update tmp
            } else {
                // No inversions take place if either operand is zero
                $a.infinity = true;
                $b.infinity = true;
            }
        } else {
            // We can recover x1 + x2 from this. Note this is never 0.
            $a.x -= &$b.x; // denominator = x1 - x2
            $a.y -= &$b.y; // numerator = y1 - y2
            $a.y *= &$inversion_tmp; // (y1 - y2)*tmp
            $inversion_tmp *= &$a.x // update tmp
        }
    };
}

macro_rules! batch_add_loop_2 {
    ($a: ident, $b: ident, $inversion_tmp: ident) => {
        if $a.is_zero() {
            *$a = $b;
        } else if !$b.is_zero() {
            let lambda = $a.y * &$inversion_tmp;
            $inversion_tmp *= &$a.x; // Remove the top layer of the denominator

            // x3 = l^2 - x1 - x2 or for squaring: 2y + l^2 + 2x - 2y = l^2 - 2x
            $a.x += &$b.x.double();
            $a.x = lambda.square() - &$a.x;
            // y3 = l*(x2 - x3) - y2 or
            // for squaring: (3x^2 + a)/2y(x - y - x3) - (y - (3x^2 + a)/2) = l*(x - x3) - y
            $a.y = lambda * &($b.x - &$a.x) - &$b.y;
        }
    };
}

impl<P: Parameters> BatchGroupArithmetic for GroupAffine<P> {
    type BaseFieldForBatch = P::BaseField;
    /// This implementation of batch group ops takes particular
    /// care to make most use of points fetched from memory to prevent
    /// reallocations

    /// It is inspired by Aztec's approach:
    /// https://github.com/AztecProtocol/barretenberg/blob/
    /// c358fee3259a949da830f9867df49dc18768fa26/barretenberg/
    /// src/aztec/ecc/curves/bn254/scalar_multiplication/scalar_multiplication.
    /// cpp

    // We require extra scratch space, and since we want to prevent allocation/deallocation
    // overhead we pass it externally for when this function is called many times
    #[inline]
    fn batch_double_in_place(
        bases: &mut [Self],
        index: &[u32],
        scratch_space: Option<&mut Vec<Self::BaseFieldForBatch>>,
    ) {
        let mut inversion_tmp = P::BaseField::one();

        let mut _scratch_space_inner = if scratch_space.is_none() {
            Vec::with_capacity(index.len())
        } else {
            vec![]
        };
        let scratch_space = match scratch_space {
            Some(vec) => vec,
            None => &mut _scratch_space_inner,
        };

        debug_assert!(scratch_space.len() == 0);

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        for idx in index.iter() {
            // Prefetch next group into cache
            #[cfg(feature = "prefetch")]
            if let Some(idp) = prefetch_iter.next() {
                prefetch::<Self>(&mut bases[*idp as usize]);
            }
            let mut a = &mut bases[*idx as usize];
            if !a.is_zero() {
                if a.y.is_zero() {
                    a.infinity = true;
                } else {
                    let x_sq = a.x.square();
                    let x_sq_3 = x_sq.double() + &x_sq + &P::COEFF_A; // numerator = 3x^2 + a
                    scratch_space.push(x_sq_3 * &inversion_tmp); // (3x^2 + a) * tmp
                    inversion_tmp *= &a.y.double(); // update tmp
                }
            }
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter().rev();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        for idx in index.iter().rev() {
            #[cfg(feature = "prefetch")]
            if let Some(idp) = prefetch_iter.next() {
                prefetch::<Self>(&mut bases[*idp as usize]);
            }
            let mut a = &mut bases[*idx as usize];
            if !a.is_zero() {
                let z = scratch_space.pop().unwrap();
                #[cfg(feature = "prefetch")]
                if let Some(e) = scratch_space.last() {
                    prefetch::<P::BaseField>(e);
                }
                let lambda = z * &inversion_tmp;
                inversion_tmp *= &a.y.double(); // Remove the top layer of the denominator

                // x3 = l^2 + 2x
                let x3 = &(lambda.square() - &a.x.double());
                // y3 = l*(x - x3) - y
                a.y = lambda * &(a.x - x3) - &a.y;
                a.x = *x3;
            }
        }

        debug_assert!(scratch_space.len() == 0);

        // We reset the vector
        // Clearing is really unnecessary, but we can do it anyway
        scratch_space.clear();
    }

    #[inline]
    fn batch_add_in_place(bases: &mut [Self], other: &mut [Self], index: &[(u32, u32)]) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            #[cfg(feature = "prefetch")]
            prefetch_slice!(bases, other, prefetch_iter);

            let (mut a, mut b) = (&mut bases[*idx as usize], &mut other[*idy as usize]);
            batch_add_loop_1!(a, b, half, inversion_tmp);
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter().rev();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        for (idx, idy) in index.iter().rev() {
            #[cfg(feature = "prefetch")]
            prefetch_slice!(bases, other, prefetch_iter);
            let (mut a, b) = (&mut bases[*idx as usize], other[*idy as usize]);
            batch_add_loop_2!(a, b, inversion_tmp)
        }
    }

    #[inline]
    fn batch_add_in_place_same_slice(bases: &mut [Self], index: &[(u32, u32)]) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        {
            prefetch_iter.next();
        }

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            #[cfg(feature = "prefetch")]
            prefetch_slice!(bases, bases, prefetch_iter);
            let (mut a, mut b) = if idx < idy {
                let (x, y) = bases.split_at_mut(*idy as usize);
                (&mut x[*idx as usize], &mut y[0])
            } else {
                let (x, y) = bases.split_at_mut(*idx as usize);
                (&mut y[0], &mut x[*idy as usize])
            };
            batch_add_loop_1!(a, b, half, inversion_tmp);
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter().rev();
        #[cfg(feature = "prefetch")]
        {
            prefetch_iter.next();
        }

        for (idx, idy) in index.iter().rev() {
            #[cfg(feature = "prefetch")]
            prefetch_slice!(bases, bases, prefetch_iter);
            let (mut a, b) = if idx < idy {
                let (x, y) = bases.split_at_mut(*idy as usize);
                (&mut x[*idx as usize], y[0])
            } else {
                let (x, y) = bases.split_at_mut(*idx as usize);
                (&mut y[0], x[*idy as usize])
            };
            batch_add_loop_2!(a, b, inversion_tmp);
        }
    }

    #[inline]
    fn batch_add_in_place_read_only(
        bases: &mut [Self],
        other: &[Self],
        index: &[(u32, u32)],
        scratch_space: &mut Vec<Self>,
    ) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            let (idy, endomorphism) = decode_endo_from_u32(*idy);
            #[cfg(feature = "prefetch")]
            prefetch_slice_endo!(bases, other, prefetch_iter);

            let mut a = &mut bases[*idx as usize];

            // Apply endomorphisms according to encoding
            let mut b = if endomorphism % 2 == 1 {
                other[idy].neg()
            } else {
                other[idy]
            };

            if P::has_glv() {
                if endomorphism >> 1 == 1 {
                    P::glv_endomorphism_in_place(&mut b.x);
                }
            }
            batch_add_loop_1!(a, b, half, inversion_tmp);
            scratch_space.push(b);
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter().rev();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        for (idx, _) in index.iter().rev() {
            #[cfg(feature = "prefetch")]
            {
                prefetch_slice!(bases, prefetch_iter);
                let len = scratch_space.len();
                if len > 0 {
                    prefetch::<Self>(&mut scratch_space[len - 1]);
                }
            }
            let (mut a, b) = (&mut bases[*idx as usize], scratch_space.pop().unwrap());
            batch_add_loop_2!(a, b, inversion_tmp);
        }
    }

    fn batch_add_write(
        lookup: &[Self],
        index: &[(u32, u32)],
        new_elems: &mut Vec<Self>,
        scratch_space: &mut Vec<Option<Self>>,
    ) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        {
            prefetch_iter.next();
        }

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            #[cfg(feature = "prefetch")]
            prefetch_slice_write!(lookup, lookup, prefetch_iter);

            if *idy == !0u32 {
                new_elems.push(lookup[*idx as usize]);
                scratch_space.push(None);
            } else {
                let (mut a, mut b) = (lookup[*idx as usize], lookup[*idy as usize]);
                batch_add_loop_1!(a, b, half, inversion_tmp);
                new_elems.push(a);
                scratch_space.push(Some(b));
            }
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        for (a, op_b) in new_elems.iter_mut().rev().zip(scratch_space.iter().rev()) {
            match op_b {
                Some(b) => {
                    let b_ = *b;
                    batch_add_loop_2!(a, b_, inversion_tmp);
                }
                None => (),
            };
        }
        scratch_space.clear();
    }

    fn batch_add_write_read_self(
        lookup: &[Self],
        index: &[(u32, u32)],
        new_elems: &mut Vec<Self>,
        scratch_space: &mut Vec<Option<Self>>,
    ) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        #[cfg(feature = "prefetch")]
        let mut prefetch_iter = index.iter();
        #[cfg(feature = "prefetch")]
        prefetch_iter.next();

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            #[cfg(feature = "prefetch")]
            prefetch_slice_write!(new_elems, lookup, prefetch_iter);

            if *idy == !0u32 {
                new_elems.push(lookup[*idx as usize]);
                scratch_space.push(None);
            } else {
                let (mut a, mut b) = (new_elems[*idx as usize], lookup[*idy as usize]);
                batch_add_loop_1!(a, b, half, inversion_tmp);
                new_elems.push(a);
                scratch_space.push(Some(b));
            }
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        for (a, op_b) in new_elems.iter_mut().rev().zip(scratch_space.iter().rev()) {
            match op_b {
                Some(b) => {
                    let b_ = *b;
                    batch_add_loop_2!(a, b_, inversion_tmp);
                }
                None => (),
            };
        }
        scratch_space.clear();
    }

    fn batch_scalar_mul_in_place<BigInt: BigInteger>(
        mut bases: &mut [Self],
        scalars: &mut [BigInt],
        w: usize,
    ) {
        debug_assert!(bases.len() == scalars.len());
        if bases.len() == 0 {
            return;
        }
        let batch_size = bases.len();
        if P::has_glv() {
            use itertools::{EitherOrBoth::*, Itertools};
            let mut scratch_space = Vec::<Self::BaseFieldForBatch>::with_capacity(bases.len());
            let mut scratch_space_group = Vec::<Self>::with_capacity(bases.len() / w);

            let k_vec: Vec<_> = scalars
                .iter()
                .map(|k| {
                    P::glv_scalar_decomposition(<P::ScalarField as PrimeField>::BigInt::from_slice(
                        k.as_ref(),
                    ))
                })
                .collect();

            let mut k1_scalars: Vec<_> = k_vec.iter().map(|x| (x.0).1).collect();
            let k1_negates: Vec<_> = k_vec.iter().map(|x| (x.0).0).collect();
            let mut k2_scalars: Vec<_> = k_vec.iter().map(|x| (x.1).1).collect();
            let k2_negates: Vec<_> = k_vec.iter().map(|x| (x.1).0).collect();

            let opcode_vectorised_k1 = Self::batch_wnaf_opcode_recoding(
                &mut k1_scalars[..],
                w,
                Some(k1_negates.as_slice()),
            );
            let opcode_vectorised_k2 = Self::batch_wnaf_opcode_recoding(
                &mut k2_scalars[..],
                w,
                Some(k2_negates.as_slice()),
            );

            let tables = Self::batch_wnaf_tables(bases, w);
            let tables_k2: Vec<_> = tables
                .iter()
                .map(|&p| {
                    let mut p = p;
                    P::glv_endomorphism_in_place(&mut p.x);
                    p
                })
                .collect();
            // Set all points to 0;
            let zero = Self::zero();
            for p in bases.iter_mut() {
                *p = zero;
            }

            let noop_vec = vec![None; batch_size];
            for (opcode_row_k1, opcode_row_k2) in opcode_vectorised_k1
                .iter()
                .zip_longest(opcode_vectorised_k2.iter())
                .map(|x| match x {
                    Both(a, b) => (a, b),
                    Left(a) => (a, &noop_vec),
                    Right(b) => (&noop_vec, b),
                })
                .rev()
            {
                let index_double: Vec<_> = opcode_row_k1
                    .iter()
                    .zip(opcode_row_k2.iter())
                    .enumerate()
                    .filter(|x| (x.1).0.is_some() || (x.1).1.is_some())
                    .map(|x| x.0 as u32)
                    .collect();

                Self::batch_double_in_place(
                    &mut bases,
                    &index_double[..],
                    Some(&mut scratch_space),
                );
                let index_add_k1: Vec<_> = opcode_row_k1
                    .iter()
                    .enumerate()
                    .filter(|(_, op)| op.is_some() && op.unwrap() != 0)
                    .map(|(i, op)| {
                        let idx = op.unwrap();
                        if idx > 0 {
                            let op2 = ((idx as usize) / 2 * batch_size + i) as u32;
                            (i as u32, op2 << ENDO_CODING_BITS)
                        } else {
                            let op2 = ((-idx as usize) / 2 * batch_size + i) as u32;
                            (i as u32, (op2 << ENDO_CODING_BITS) + 1)
                        }
                    })
                    .collect();

                Self::batch_add_in_place_read_only(
                    &mut bases,
                    &tables[..],
                    &index_add_k1[..],
                    &mut scratch_space_group,
                );
                let index_add_k2: Vec<_> = opcode_row_k2
                    .iter()
                    .enumerate()
                    .filter(|(_, op)| op.is_some() && op.unwrap() != 0)
                    .map(|(i, op)| {
                        let idx = op.unwrap();
                        if idx > 0 {
                            let op2 = ((idx as usize) / 2 * batch_size + i) as u32;
                            (i as u32, op2 << ENDO_CODING_BITS)
                        } else {
                            let op2 = ((-idx as usize) / 2 * batch_size + i) as u32;
                            (i as u32, (op2 << ENDO_CODING_BITS) + 1)
                        }
                    })
                    .collect();

                Self::batch_add_in_place_read_only(
                    &mut bases,
                    &tables_k2[..],
                    &index_add_k2[..],
                    &mut scratch_space_group,
                );
            }
        } else {
            let mut scratch_space = Vec::<Self::BaseFieldForBatch>::with_capacity(bases.len());
            let opcode_vectorised = Self::batch_wnaf_opcode_recoding::<BigInt>(scalars, w, None);
            let tables = Self::batch_wnaf_tables(bases, w);
            // Set all points to 0;
            let zero = Self::zero();
            for p in bases.iter_mut() {
                *p = zero;
            }

            for opcode_row in opcode_vectorised.iter().rev() {
                let index_double: Vec<_> = opcode_row
                    .iter()
                    .enumerate()
                    .filter(|x| x.1.is_some())
                    .map(|x| x.0 as u32)
                    .collect();

                Self::batch_double_in_place(
                    &mut bases,
                    &index_double[..],
                    Some(&mut scratch_space),
                );

                let mut add_ops: Vec<Self> = opcode_row
                    .iter()
                    .enumerate()
                    .filter(|(_, op)| op.is_some() && op.unwrap() != 0)
                    .map(|(i, op)| {
                        let idx = op.unwrap();
                        if idx > 0 {
                            tables[(idx as usize) / 2 * batch_size + i].clone()
                        } else {
                            tables[(-idx as usize) / 2 * batch_size + i].clone().neg()
                        }
                    })
                    .collect();

                let index_add: Vec<_> = opcode_row
                    .iter()
                    .enumerate()
                    .filter(|(_, op)| op.is_some() && op.unwrap() != 0)
                    .map(|x| x.0)
                    .enumerate()
                    .map(|(x, y)| (y as u32, x as u32))
                    .collect();

                Self::batch_add_in_place(&mut bases, &mut add_ops[..], &index_add[..]);
            }
        }
    }
}

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    Debug(bound = "P: Parameters"),
    Hash(bound = "P: Parameters")
)]
#[must_use]
pub struct GroupProjective<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub z: P::BaseField,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P: Parameters> Display for GroupProjective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", GroupAffine::from(*self))
    }
}

impl<P: Parameters> Eq for GroupProjective<P> {}
impl<P: Parameters> PartialEq for GroupProjective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // The points (X, Y, Z) and (X', Y', Z')
        // are equal when (X * Z^2) = (X' * Z'^2)
        // and (Y * Z^3) = (Y' * Z'^3).
        let z1z1 = self.z.square();
        let z2z2 = other.z.square();

        if self.x * &z2z2 != other.x * &z1z1 {
            false
        } else {
            self.y * &(z2z2 * &other.z) == other.y * &(z1z1 * &self.z)
        }
    }
}

impl<P: Parameters> Distribution<GroupProjective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> GroupProjective<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = GroupAffine::get_point_from_x(x, greatest) {
                return p.scale_by_cofactor().into();
            }
        }
    }
}

impl<P: Parameters> ToBytes for GroupProjective<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)?;
        self.z.write(writer)
    }
}

impl<P: Parameters> FromBytes for GroupProjective<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let z = P::BaseField::read(reader)?;
        Ok(Self::new(x, y, z))
    }
}

impl<P: Parameters> Default for GroupProjective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> GroupProjective<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        Self {
            x,
            y,
            z,
            _params: PhantomData,
        }
    }
}

impl<P: Parameters> Zeroize for GroupProjective<P> {
    // The phantom data does not contain element-specific data
    // and thus does not need to be zeroized.
    fn zeroize(&mut self) {
        self.x.zeroize();
        self.y.zeroize();
        self.z.zeroize();
    }
}

impl<P: Parameters> Zero for GroupProjective<P> {
    // The point at infinity is always represented by
    // Z = 0.
    #[inline]
    fn zero() -> Self {
        Self::new(
            P::BaseField::one(),
            P::BaseField::one(),
            P::BaseField::zero(),
        )
    }

    // The point at infinity is always represented by
    // Z = 0.
    #[inline]
    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }
}

impl<P: Parameters> ProjectiveCurve for GroupProjective<P> {
    const COFACTOR: &'static [u64] = P::COFACTOR;
    type BaseField = P::BaseField;
    type ScalarField = P::ScalarField;
    type Affine = GroupAffine<P>;

    #[inline(always)]
    fn get_x(&mut self) -> &mut Self::BaseField {
        &mut self.x
    }

    #[inline]
    fn prime_subgroup_generator() -> Self {
        GroupAffine::prime_subgroup_generator().into()
    }

    #[inline]
    fn is_normalized(&self) -> bool {
        self.is_zero() || self.z.is_one()
    }

    #[inline]
    fn batch_normalization(v: &mut [Self]) {
        // A projective curve element (x, y, z) is normalized
        // to its affine representation, by the conversion
        // (x, y, z) -> (x / z^2, y / z^3, 1)
        // Batch normalizing N short-weierstrass curve elements costs:
        //     1 inversion + 6N field multiplications + N field squarings    (Field ops)
        // (batch inversion requires 3N multiplications + 1 inversion)
        let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
        ark_ff::batch_inversion(&mut z_s);

        // Perform affine transformations
        ark_std::cfg_iter_mut!(v)
            .zip(z_s)
            .filter(|(g, _)| !g.is_normalized())
            .for_each(|(g, z)| {
                let z2 = z.square(); // 1/z
                g.x *= &z2; // x/z^2
                g.y *= &(z2 * &z); // y/z^3
                g.z = P::BaseField::one(); // z = 1
            });
    }

    fn double_in_place(&mut self) -> &mut Self {
        if self.is_zero() {
            return self;
        }

        if P::COEFF_A.is_zero() {
            // A = X1^2
            let mut a = self.x.square();

            // B = Y1^2
            let b = self.y.square();

            // C = B^2
            let mut c = b.square();

            // D = 2*((X1+B)2-A-C)
            let d = ((self.x + &b).square() - &a - &c).double();

            // E = 3*A
            let e = a + &*a.double_in_place();

            // F = E^2
            let f = e.square();

            // Z3 = 2*Y1*Z1
            self.z *= &self.y;
            self.z.double_in_place();

            // X3 = F-2*D
            self.x = f - &d - &d;

            // Y3 = E*(D-X3)-8*C
            self.y = (d - &self.x) * &e - &*c.double_in_place().double_in_place().double_in_place();
            self
        } else {
            // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            // XX = X1^2
            let xx = self.x.square();

            // YY = Y1^2
            let yy = self.y.square();

            // YYYY = YY^2
            let mut yyyy = yy.square();

            // ZZ = Z1^2
            let zz = self.z.square();

            // S = 2*((X1+YY)^2-XX-YYYY)
            let s = ((self.x + &yy).square() - &xx - &yyyy).double();

            // M = 3*XX+a*ZZ^2
            let m = xx + &xx + &xx + &P::mul_by_a(&zz.square());

            // T = M^2-2*S
            let t = m.square() - &s.double();

            // X3 = T
            self.x = t;
            // Y3 = M*(S-T)-8*YYYY
            let old_y = self.y;
            self.y = m * &(s - &t) - &*yyyy.double_in_place().double_in_place().double_in_place();
            // Z3 = (Y1+Z1)^2-YY-ZZ
            self.z = (old_y + &self.z).square() - &yy - &zz;
            self
        }
    }

    fn add_assign_mixed(&mut self, other: &GroupAffine<P>) {
        if other.is_zero() {
            return;
        }

        if self.is_zero() {
            self.x = other.x;
            self.y = other.y;
            self.z = P::BaseField::one();
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square();

        // U2 = X2*Z1Z1
        let u2 = other.x * &z1z1;

        // S2 = Y2*Z1*Z1Z1
        let s2 = (other.y * &self.z) * &z1z1;

        if self.x == u2 && self.y == s2 {
            // The two points are equal, so we double.
            self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-X1
            let h = u2 - &self.x;

            // HH = H^2
            let hh = h.square();

            // I = 4*HH
            let mut i = hh;
            i.double_in_place().double_in_place();

            // J = H*I
            let mut j = h * &i;

            // r = 2*(S2-Y1)
            let r = (s2 - &self.y).double();

            // V = X1*I
            let v = self.x * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square();
            self.x -= &j;
            self.x -= &v;
            self.x -= &v;

            // Y3 = r*(V-X3)-2*Y1*J
            j *= &self.y; // J = 2*Y1*J
            j.double_in_place();
            self.y = v - &self.x;
            self.y *= &r;
            self.y -= &j;

            // Z3 = (Z1+H)^2-Z1Z1-HH
            self.z += &h;
            self.z.square_in_place();
            self.z -= &z1z1;
            self.z -= &hh;
        }
    }

    fn mul<S: AsRef<[u64]>>(mut self, other: S) -> Self {
        if P::has_glv() {
            let w = P::glv_window_size();
            let mut res = Self::zero();
            let exponent_bigint =
                <Self::ScalarField as PrimeField>::BigInt::from_slice(other.as_ref());
            impl_glv_mul!(Self, P, w, self, res, exponent_bigint);
            res
        } else {
            let mut res = Self::zero();
            for b in BitIteratorBE::without_leading_zeros(other.as_ref()) {
                res.double_in_place();
                if b {
                    res += self;
                }
            }
            self = res;
            self
        }
    }
}

impl<P: Parameters> Neg for GroupProjective<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if !self.is_zero() {
            Self::new(self.x, -self.y, self.z)
        } else {
            self
        }
    }
}

ark_ff::impl_additive_ops_from_ref!(GroupProjective, Parameters);

impl<'a, P: Parameters> Add<&'a Self> for GroupProjective<P> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &'a Self) -> Self {
        self += other;
        self
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for GroupProjective<P> {
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square();

        // Z2Z2 = Z2^2
        let z2z2 = other.z.square();

        // U1 = X1*Z2Z2
        let u1 = self.x * &z2z2;

        // U2 = X2*Z1Z1
        let u2 = other.x * &z1z1;

        // S1 = Y1*Z2*Z2Z2
        let s1 = self.y * &other.z * &z2z2;

        // S2 = Y2*Z1*Z1Z1
        let s2 = other.y * &self.z * &z1z1;

        if u1 == u2 && s1 == s2 {
            // The two points are equal, so we double.
            self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-U1
            let h = u2 - &u1;

            // I = (2*H)^2
            let i = (h.double()).square();

            // J = H*I
            let j = h * &i;

            // r = 2*(S2-S1)
            let r = (s2 - &s1).double();

            // V = U1*I
            let v = u1 * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square() - &j - &(v.double());

            // Y3 = r*(V - X3) - 2*S1*J
            self.y = r * &(v - &self.x) - &*(s1 * &j).double_in_place();

            // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
            self.z = ((self.z + &other.z).square() - &z1z1 - &z2z2) * &h;
        }
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for GroupProjective<P> {
    type Output = Self;

    #[inline]
    fn sub(mut self, other: &'a Self) -> Self {
        self -= other;
        self
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for GroupProjective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: Parameters> MulAssign<P::ScalarField> for GroupProjective<P> {
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = self.mul(other.into_repr())
    }
}

// The affine point X, Y is represented in the Jacobian
// coordinates with Z = 1.
impl<P: Parameters> From<GroupAffine<P>> for GroupProjective<P> {
    #[inline]
    fn from(p: GroupAffine<P>) -> GroupProjective<P> {
        if p.is_zero() {
            Self::zero()
        } else {
            Self::new(p.x, p.y, P::BaseField::one())
        }
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: Parameters> From<GroupProjective<P>> for GroupAffine<P> {
    #[inline]
    fn from(p: GroupProjective<P>) -> GroupAffine<P> {
        if p.is_zero() {
            GroupAffine::zero()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            GroupAffine::new(p.x, p.y, false)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let zinv = p.z.inverse().unwrap();
            let zinv_squared = zinv.square();

            // X/Z^2
            let x = p.x * &zinv_squared;

            // Y/Z^3
            let y = p.y * &(zinv_squared * &zinv);

            GroupAffine::new(x, y, false)
        }
    }
}

impl<P: Parameters> CanonicalSerialize for GroupAffine<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
            let flags = SWFlags::infinity();
            // Serialize 0.
            P::BaseField::zero().serialize_with_flags(writer, flags)
        } else {
            let flags = SWFlags::from_y_sign(self.y > -self.y);
            self.x.serialize_with_flags(writer, flags)
        }
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let flags = if self.is_zero() {
            SWFlags::infinity()
        } else {
            SWFlags::default()
        };
        self.x.serialize(&mut writer)?;
        self.y.serialize_with_flags(&mut writer, flags)?;
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.x.serialized_size() + self.y.serialized_size_with_flags::<SWFlags>()
    }
}

impl<P: Parameters> CanonicalSerialize for GroupProjective<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialized_size()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.serialize_uncompressed(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        let aff = GroupAffine::<P>::from(self.clone());
        aff.uncompressed_size()
    }
}

impl<P: Parameters> CanonicalDeserialize for GroupAffine<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;
        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
        if flags.is_infinity() {
            Ok(Self::zero())
        } else {
            let p = GroupAffine::<P>::get_point_from_x(x, flags.is_positive().unwrap())
                .ok_or(SerializationError::InvalidData)?;
            Ok(p)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_uncompressed_unchecked(reader)?;
        if !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let (y, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        let p = GroupAffine::<P>::new(x, y, flags.is_infinity());
        Ok(p)
    }
}

impl<P: Parameters> CanonicalDeserialize for GroupProjective<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_uncompressed(reader)?;
        Ok(aff.into())
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let aff = GroupAffine::<P>::deserialize_unchecked(reader)?;
        Ok(aff.into())
    }
}

impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for GroupAffine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        let infinity_fe = self.infinity.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        x_fe.extend_from_slice(&infinity_fe);
        Some(x_fe)
    }
}

impl<M: Parameters, ConstraintF: Field> ToConstraintField<ConstraintF> for GroupProjective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
        GroupAffine::from(*self).to_field_elements()
    }
}

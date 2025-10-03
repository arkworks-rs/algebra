use crate::{AdditiveGroup, BigInt, FftField, One, PrimeField, SqrtPrecomputation, Zero};
use ark_std::{
    cmp::*,
    fmt::{Display, Formatter, Result as FmtResult},
    hash::Hash,
    marker::PhantomData,
    str::FromStr,
};
use educe::Educe;
use num_traits::Unsigned;

/// A trait that specifies the configuration of a prime field.
/// Also specifies how to perform arithmetic on field elements.
pub trait SmallFpConfig: Send + Sync + 'static + Sized {
    type T: Copy
        + Default
        + PartialEq
        + Eq
        + Hash
        + Sync
        + Send
        + PartialOrd
        + Display
        + Unsigned
        + core::fmt::Debug
        + core::ops::Add<Output = Self::T>
        + core::ops::Sub<Output = Self::T>
        + core::ops::Mul<Output = Self::T>
        + core::ops::Div<Output = Self::T>
        + core::ops::Rem<Output = Self::T>
        + Into<u128>
        + TryFrom<u128>;

    /// The modulus of the field.
    const MODULUS: Self::T;
    const MODULUS_128: u128;

    // ! this is fixed temporarily the value can be 1 or 2
    const NUM_BIG_INT_LIMBS: usize = 2;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: SmallFp<Self>;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: SmallFp<Self>;

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: SmallFp<Self>;

    /// Negation of the multiplicative identity of the field.
    const NEG_ONE: SmallFp<Self>;

    /// Let `N` be the size of the multiplicative group defined by the field.
    /// Then `TWO_ADICITY` is the two-adicity of `N`, i.e. the integer `s`
    /// such that `N = 2^s * t` for some odd integer `t`.
    const TWO_ADICITY: u32;

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: SmallFp<Self>;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)) Used for mixed-radix
    /// FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<SmallFp<Self>> = None;

    /// Precomputed material for use when computing square roots.
    /// Currently uses the generic Tonelli-Shanks,
    /// which works for every modulus.
    const SQRT_PRECOMP: Option<SqrtPrecomputation<SmallFp<Self>>>;

    /// Set a += b.
    fn add_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>);

    /// Set a -= b.
    fn sub_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>);

    /// Set a = a + a.
    fn double_in_place(a: &mut SmallFp<Self>);

    /// Set a = -a;
    fn neg_in_place(a: &mut SmallFp<Self>);

    /// Set a *= b.
    fn mul_assign(a: &mut SmallFp<Self>, b: &SmallFp<Self>);

    /// Compute the inner product `<a, b>`.
    fn sum_of_products<const T: usize>(
        a: &[SmallFp<Self>; T],
        b: &[SmallFp<Self>; T],
    ) -> SmallFp<Self>;

    /// Set a *= a.
    fn square_in_place(a: &mut SmallFp<Self>);

    /// Compute a^{-1} if `a` is not zero.
    fn inverse(a: &SmallFp<Self>) -> Option<SmallFp<Self>>;

    /// Construct a field element from an integer in the range
    /// `0..(Self::MODULUS - 1)`. Returns `None` if the integer is outside
    /// this range.
    fn from_bigint(other: BigInt<2>) -> Option<SmallFp<Self>>;

    /// Convert a field element to an integer in the range `0..(Self::MODULUS -
    /// 1)`.
    fn into_bigint(other: SmallFp<Self>) -> BigInt<2>;
}

/// Represents an element of the prime field F_p, where `p == P::MODULUS`.
/// This type can represent elements in any field of size at most N * 64 bits.
#[derive(Educe)]
#[educe(Default, Hash, Clone, Copy, PartialEq, Eq)]
pub struct SmallFp<P: SmallFpConfig> {
    pub value: P::T,
    _phantom: PhantomData<P>,
}

impl<P: SmallFpConfig> SmallFp<P> {
    #[doc(hidden)]
    #[inline]
    pub fn is_geq_modulus(&self) -> bool {
        self.value >= P::MODULUS
    }

    pub const fn new(value: P::T) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    pub fn num_bits_to_shave() -> usize {
        primitive_type_bit_size(P::MODULUS_128) - (Self::MODULUS_BIT_SIZE as usize)
    }
}

impl<P: SmallFpConfig> ark_std::fmt::Debug for SmallFp<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> ark_std::fmt::Result {
        ark_std::fmt::Debug::fmt(&self.into_bigint(), f)
    }
}

impl<P: SmallFpConfig> Zero for SmallFp<P> {
    #[inline]
    fn zero() -> Self {
        P::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        *self == P::ZERO
    }
}

impl<P: SmallFpConfig> One for SmallFp<P> {
    #[inline]
    fn one() -> Self {
        P::ONE
    }

    #[inline]
    fn is_one(&self) -> bool {
        *self == P::ONE
    }
}

impl<P: SmallFpConfig> AdditiveGroup for SmallFp<P> {
    type Scalar = Self;
    const ZERO: Self = P::ZERO;

    #[inline]
    fn double(&self) -> Self {
        let mut temp = *self;
        AdditiveGroup::double_in_place(&mut temp);
        temp
    }

    #[inline]
    fn double_in_place(&mut self) -> &mut Self {
        P::double_in_place(self);
        self
    }

    #[inline]
    fn neg_in_place(&mut self) -> &mut Self {
        P::neg_in_place(self);
        self
    }
}

const fn const_to_bigint(value: u128) -> BigInt<2> {
    let low = (value & 0xFFFFFFFFFFFFFFFF) as u64;
    let high = (value >> 64) as u64;
    BigInt::<2>::new([low, high])
}

const fn const_num_bits_u128(value: u128) -> u32 {
    if value == 0 {
        0
    } else {
        128 - value.leading_zeros()
    }
}

const fn primitive_type_bit_size(modulus_128: u128) -> usize {
    match modulus_128 {
        x if x <= u8::MAX as u128 => 8,
        x if x <= u16::MAX as u128 => 16,
        x if x <= u32::MAX as u128 => 32,
        x if x <= u64::MAX as u128 => 64,
        _ => 128,
    }
}

impl<P: SmallFpConfig> PrimeField for SmallFp<P> {
    type BigInt = BigInt<2>;

    const MODULUS: Self::BigInt = const_to_bigint(P::MODULUS_128);
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = Self::MODULUS.divide_by_2_round_down();
    const MODULUS_BIT_SIZE: u32 = const_num_bits_u128(P::MODULUS_128);
    const TRACE: Self::BigInt = Self::MODULUS.two_adic_coefficient();
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = Self::TRACE.divide_by_2_round_down();

    #[inline]
    fn from_bigint(r: BigInt<2>) -> Option<Self> {
        P::from_bigint(r)
    }

    fn into_bigint(self) -> BigInt<2> {
        P::into_bigint(self)
    }
}

impl<P: SmallFpConfig> FftField for SmallFp<P> {
    const GENERATOR: Self = P::GENERATOR;
    const TWO_ADICITY: u32 = P::TWO_ADICITY;
    const TWO_ADIC_ROOT_OF_UNITY: Self = P::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = P::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = P::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = P::LARGE_SUBGROUP_ROOT_OF_UNITY;
}

/// Note that this implementation of `Ord` compares field elements viewing
/// them as integers in the range 0, 1, ..., P::MODULUS - 1. However, other
/// implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `Ord` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: SmallFpConfig> Ord for SmallFp<P> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }
}

/// Note that this implementation of `PartialOrd` compares field elements
/// viewing them as integers in the range 0, 1, ..., `P::MODULUS` - 1. However,
/// other implementations of `PrimeField` might choose a different ordering, and
/// as such, users should use this `PartialOrd` for applications where
/// any ordering suffices (like in a BTreeMap), and not in applications
/// where a particular ordering is required.
impl<P: SmallFpConfig> PartialOrd for SmallFp<P> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: SmallFpConfig> ark_std::rand::distributions::Distribution<SmallFp<P>>
    for ark_std::rand::distributions::Standard
{
    #[inline]
    // samples non-zero element, loop avoids modulo bias
    fn sample<R: ark_std::rand::Rng + ?Sized>(&self, rng: &mut R) -> SmallFp<P> {
        macro_rules! sample_loop {
            ($ty:ty) => {
                loop {
                    let random_val: $ty = rng.sample(ark_std::rand::distributions::Standard);
                    let val_u128 = random_val as u128;
                    if val_u128 > 0 && val_u128 < P::MODULUS_128 {
                        return SmallFp::from(random_val);
                    }
                }
            };
        }

        match P::MODULUS_128 {
            modulus if modulus <= u8::MAX as u128 => sample_loop!(u8),
            modulus if modulus <= u16::MAX as u128 => sample_loop!(u16),
            modulus if modulus <= u32::MAX as u128 => sample_loop!(u32),
            modulus if modulus <= u64::MAX as u128 => sample_loop!(u64),
            _ => sample_loop!(u128),
        }
    }
}

pub enum ParseSmallFpError {
    Empty,
    InvalidFormat,
    InvalidLeadingZero,
}

impl<P: SmallFpConfig> FromStr for SmallFp<P> {
    type Err = ParseSmallFpError;

    /// Interpret a string of numbers as a (congruent) prime field element.
    /// Does not accept unnecessary leading zeroes or a blank string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err(ParseSmallFpError::Empty);
        }
        if s.starts_with('0') && s.len() > 1 {
            return Err(ParseSmallFpError::InvalidLeadingZero);
        }

        match s.parse::<u128>() {
            Ok(val) => Ok(SmallFp::from(val)),
            Err(_) => Err(ParseSmallFpError::InvalidFormat),
        }
    }
}

/// Outputs a string containing the value of `self`,
/// represented as a decimal without leading zeroes.
impl<P: SmallFpConfig> Display for SmallFp<P> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // Always use BigInt conversion to display the true mathematical value
        let bigint = P::into_bigint(*self);
        write!(f, "{}", bigint)
    }
}

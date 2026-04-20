//! Layout contract for reinterpreting field-element slices as flat `u64` slices.
//!
//! SIMD kernels (e.g. the Goldilocks AVX-512 / NEON backends used by
//! downstream sumcheck provers) need to hand their inner loops a
//! `&[u64]` carrying Montgomery-form limbs. Without a layout guarantee
//! from the field type, the only way to get that slice is `unsafe`
//! pointer casts.
//!
//! [`RawU64Repr`] advertises that guarantee. A type `T: RawU64Repr`
//! promises that it is laid out identically to `[u64; T::N_U64]`, which
//! lets [`RawU64Repr::as_u64_slice`] return a safe flat slice whose
//! length is `slice.len() * T::N_U64`.

use crate::fields::models::{
    cubic_extension::{CubicExtConfig, CubicExtField},
    fp::{Fp, FpConfig},
    quadratic_extension::{QuadExtConfig, QuadExtField},
    small_fp::{SmallFp, SmallFpConfig},
};

/// Field types whose memory layout is `[u64; N_U64]`.
///
/// # Safety
///
/// Implementors must guarantee:
/// - `size_of::<Self>() == Self::N_U64 * size_of::<u64>()`
/// - `align_of::<Self>() == align_of::<u64>()`
/// - Every well-formed `Self` is a valid bit-pattern of `[u64; N_U64]`
///   and vice versa (no niches, no padding).
///
/// The default-provided [`as_u64_slice`](Self::as_u64_slice) and
/// [`as_u64_slice_mut`](Self::as_u64_slice_mut) rely on these invariants.
/// Violating them is undefined behaviour.
pub trait RawU64Repr: Sized + Copy {
    /// Number of `u64` limbs per element.
    const N_U64: usize;

    /// Reinterpret a slice of field elements as a flat slice of Montgomery-form
    /// `u64` limbs. The returned slice has length `slice.len() * Self::N_U64`.
    #[inline]
    #[allow(unsafe_code)]
    fn as_u64_slice(slice: &[Self]) -> &[u64] {
        // SAFETY: trait contract guarantees `Self` has the layout of
        // `[u64; Self::N_U64]`, so `slice.len()` field elements form a
        // contiguous `slice.len() * Self::N_U64` run of `u64`s.
        unsafe {
            core::slice::from_raw_parts(slice.as_ptr().cast::<u64>(), slice.len() * Self::N_U64)
        }
    }

    /// Mutable counterpart to [`as_u64_slice`](Self::as_u64_slice).
    ///
    /// Writing through the returned slice bypasses every invariant of
    /// the field element (canonical range, Montgomery form). The caller
    /// must restore those invariants before the borrow ends.
    #[inline]
    #[allow(unsafe_code)]
    fn as_u64_slice_mut(slice: &mut [Self]) -> &mut [u64] {
        // SAFETY: same layout argument as `as_u64_slice`; exclusive access
        // comes from holding `&mut [Self]`.
        unsafe {
            core::slice::from_raw_parts_mut(
                slice.as_mut_ptr().cast::<u64>(),
                slice.len() * Self::N_U64,
            )
        }
    }
}

// `Fp<P, N>` is `#[repr(transparent)]` around `BigInt<N>(pub [u64; N])`.
impl<P: FpConfig<N>, const N: usize> RawU64Repr for Fp<P, N> {
    const N_U64: usize = N;
}

// `SmallFp<P>` is `#[repr(transparent)]` around `P::T`. Only the
// `T = u64` case has a `[u64; 1]` layout; narrower backings are exposed
// via [`SmallFp::as_raw_slice`].
impl<P: SmallFpConfig<T = u64>> RawU64Repr for SmallFp<P> {
    const N_U64: usize = 1;
}

// `QuadExtField` / `CubicExtField` are `#[repr(C)]` over same-typed
// base-field coefficients — no padding between them because the fields
// share alignment. The layout composes as long as the base does.
impl<P: QuadExtConfig> RawU64Repr for QuadExtField<P>
where
    P::BaseField: RawU64Repr,
{
    const N_U64: usize = 2 * <P::BaseField as RawU64Repr>::N_U64;
}

impl<P: CubicExtConfig> RawU64Repr for CubicExtField<P>
where
    P::BaseField: RawU64Repr,
{
    const N_U64: usize = 3 * <P::BaseField as RawU64Repr>::N_U64;
}

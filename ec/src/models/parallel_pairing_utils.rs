use ark_std::cfg_chunks_mut;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Executes the function `func` over `data` in parallel if the data length exceeds a threshold,
/// otherwise processes the entire data slice sequentially.
///
/// This is an internal helper function for use in multi-pairing and multi-miller-loop computations.
/// 
///
/// # Parameters
/// - `data`: A mutable slice of elements to be processed.
/// - `func`: A function that takes mutable chunk of `data` and returns a value of type `R`.
///
/// # Parallelism
/// Uses parallel processing via Rayon if the `parallel` feature is enabled and the data length is greater than 1000.
///
/// # Type Parameters
/// - `T`: The element type of the data slice. Must be `Send`.
/// - `F`: The function type. Must be `Fn(&mut [T]) -> R + Send + Sync`.
/// - `R`: The result type. Must implement `std::iter::Product` and `Send`. In internal usage, is the target field type of the pairing.
pub(super) fn threshold_chunked_loop<T, F, R>(data: &mut [T], func: F) -> R
where
    F: Fn(&mut [T]) -> R + Send + Sync,
    R: std::iter::Product + Send,
    T: Send,
{
    if data.len() > 1000 {
        cfg_chunks_mut!(data, 32).map(func).product::<R>()
    } else {
        func(data)
    }
}

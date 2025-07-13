#[cfg(feature = "parallel")]
use crate::scalar_mul::variable_base::VariableBaseMSM;

pub(super) fn preamble<A, B>(bases: &mut &[A], scalars: &mut &[B]) -> Option<usize> {
    let size = bases.len().min(scalars.len());
    if size == 0 {
        return None;
    }
    #[cfg(feature = "parallel")]
    let chunk_size = {
        let num_threads = rayon::current_num_threads();
        let num_chunks = if size < num_threads {
            1
        } else {
            num_threads
        };
        size.div_ceil(num_chunks)
    };
    #[cfg(not(feature = "parallel"))]
    let chunk_size = size;

    *bases = &bases[..size];
    *scalars = &scalars[..size];
    Some(chunk_size)
}

#[cfg(feature = "parallel")]
pub(super) fn parallelization_helper<T: Sync + Send, V: VariableBaseMSM>(
    scalars: &[T],
    bases: &[V::MulBase],
    chunk_size: usize,
    msm_fn: impl Fn(&[V::MulBase], &[T]) -> V + Sync + Send + Copy,
) -> V {
    let num_chunks = scalars.chunks(chunk_size).len().max(1);
    let (sender, receiver) = ark_std::sync::mpsc::sync_channel::<V>(num_chunks);
    let mut sum = V::zero();

    ark_std::thread::scope(|s| {
        let bases = bases.chunks(chunk_size);
        let scalars = scalars.chunks(chunk_size);
        let sender = &sender;
        for (i, (bases, scalars)) in bases.zip(scalars).enumerate() {
            if i == num_chunks - 1 {
                sender.send(msm_fn(bases, scalars)).unwrap();
            } else {
                s.spawn(move || sender.send(msm_fn(bases, scalars)).unwrap());
            }
        }
    });
    for _ in 0..num_chunks {
        sum += receiver.recv().unwrap();
    }

    sum
}

use ark_ff::{FftField, FftParameters};

pub struct io_dimension {
    length: usize,
    input_stride: usize,
    output_stride: usize,
}

pub struct io_tensor {
    dimensions: Vec<io_dimension>,
}

impl io_tensor {
    pub fn rank(&self) -> usize {
        dimensions.len()
    }
}

pub fn dft<F: FftField>(N: io_tensor, V: io_tensor, I: &[F], O: &[F]) {

}
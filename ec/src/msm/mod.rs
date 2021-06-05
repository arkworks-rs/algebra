mod fixed_base;
mod variable_base;
pub use fixed_base::*;
pub use variable_base::*;

/// The result of this function is only approximately `ln(a)`. See [here](https://github.com/arkworks-rs/snark/79#issue-556220473) for details.
fn ln_without_floats(a: usize) -> usize {
    // log2(a) * ln(2)
    (ark_std::log2(a) * 69 / 100) as usize
}

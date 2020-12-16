#[deprecated(
    since = "0.2.0",
    note = "please use `ark_std::{UniformRand, test_rng}` instead of ark_ff::{UniformRand, test_rng}"
)]
/// Should be used only for tests, not for any real world usage.
pub fn test_rng() -> rand::rngs::StdRng {
    use rand::SeedableRng;

    // arbitrary seed
    let seed = [
        1, 0, 0, 0, 23, 0, 0, 0, 200, 1, 0, 0, 210, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0,
    ];
    rand::rngs::StdRng::from_seed(seed)
}

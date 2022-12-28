/// Utility function for getting a vector of degrees to benchmark on.
/// returns `vec![2^{min}, 2^{min + interval}, ..., 2^{max}]`, where:
/// * `interval = log_interval`
/// * `min      = ceil(log_2(min_degree))`
/// * `max      = ceil(log_2(max_degree))`
pub fn size_range(
    log_interval: usize,
    min_degree: usize,
    max_degree: usize,
) -> ark_std::vec::Vec<usize> {
    let mut to_ret = vec![min_degree.next_power_of_two()];
    let interval = 1 << log_interval;
    while *to_ret.last().unwrap() < max_degree {
        let next_elem = usize::min(max_degree, interval * to_ret.last().unwrap());
        to_ret.push(next_elem);
    }
    to_ret
}

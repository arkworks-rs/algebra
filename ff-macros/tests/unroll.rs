use ark_ff_macros::unroll_for_loops;

#[unroll_for_loops(2)]
fn closed_range_end() -> usize {
    let mut count = 0;
    for i in 0..=6 & 3 {
        count += 1 + i - i;
    }
    count
}

// `0..=6 & 3` is `0..=(6 & 3)`, i.e. `0..=2`, which has 3 iterations.
#[test]
fn range_end_is_parenthesised() {
    assert_eq!(closed_range_end(), 3);
}

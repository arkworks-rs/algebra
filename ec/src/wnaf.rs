extern crate alloc;
use crate::ProjectiveCurve;
use alloc::vec::Vec;

// Computes scalar multiplication of a preprocessed group element by a scalar in windowed non-adjacent form (wNAF).
// `scalar_wnaf` is expected in its NAF form which can be obtained by using `find_wnaf` on the underlying BigInt.
// `table` holds pre-computed multiples of the group element; it can be calculated using `wnaf_table`.
pub fn wnaf_mul<G: ProjectiveCurve>(table: &[G], scalar_wnaf: &[i64]) -> G {
    let mut result = G::zero();

    let mut found_one = false;

    for n in scalar_wnaf.iter().rev() {
        if found_one {
            result.double_in_place();
        }

        if *n != 0 {
            found_one = true;

            if *n > 0 {
                result += &table[(n / 2) as usize];
            } else {
                result -= &table[((-n) / 2) as usize];
            }
        }
    }

    result
}

pub fn wnaf_table<G: ProjectiveCurve>(mut base: G, window: usize) -> Vec<G> {
    let mut table = Vec::with_capacity(1 << (window - 1));

    let dbl = base.double();

    for _ in 0..(1 << (window - 1)) {
        table.push(base);
        base.add_assign(&dbl);
    }
    table
}

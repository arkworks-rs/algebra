extern crate alloc;
use alloc::vec::Vec;
use crate::Group;

pub fn wnaf_mul<G: Group>(table: &[G], scalar_wnaf: &[i64]) -> G {
    let mut result = G::zero();

    let mut found_one = false;

    for n in scalar_wnaf.iter().rev() {
        if found_one {
            result = result.double();
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

pub fn wnaf_table<G: Group>(table: &mut Vec<G>, mut base: G, window: usize) {
    table.truncate(0);
    table.reserve(1 << (window - 1));

    let dbl = base.double();

    for _ in 0..(1 << (window - 1)) {
        table.push(base);
        base.add_assign(&dbl);
    }
}

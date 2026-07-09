//! Run with:
//! `cargo test --release --manifest-path curves/pallas/Cargo.toml --test sqrt_bench -- --ignored --nocapture`

use ark_ff::{FftField, PrimeField, SqrtPrecomputation};
use ark_std::test_rng;
use std::time::Instant;

#[test]
#[ignore = "timing comparison; run explicitly with --release --nocapture"]
fn compare() {
    bench::<ark_pallas::Fq>("Pallas Fq (p)");
    bench::<ark_pallas::Fr>("Pallas Fr (q)");
}

fn bench<F: PrimeField + FftField>(name: &str) {
    let rng = &mut test_rng();
    // Squares only, so both algorithms take the "found a root" path.
    let inputs: Vec<F> = (0..1000).map(|_| F::rand(rng).square()).collect();

    // The installed precomputation (Sarkar2020 for these fields).
    let sarkar_owned = F::SQRT_PRECOMP;
    let sarkar = sarkar_owned.as_ref().expect("Sarkar precomp installed");

    // A reference Tonelli-Shanks precomputation for the same field.
    let trace: &'static [u64] = Box::leak(
        F::TRACE_MINUS_ONE_DIV_TWO
            .as_ref()
            .to_vec()
            .into_boxed_slice(),
    );
    let ts: SqrtPrecomputation<F> = SqrtPrecomputation::TonelliShanks {
        two_adicity: F::TWO_ADICITY,
        quadratic_nonresidue_to_trace: F::TWO_ADIC_ROOT_OF_UNITY,
        trace_of_modulus_minus_one_div_two: trace,
    };

    let run = |p: &SqrtPrecomputation<F>| {
        let t = Instant::now();
        let mut acc = vec![];
        for x in &inputs {
            acc.push(p.sqrt(x).unwrap());
        }
        (t.elapsed(), acc)
    };

    let (ts_time, a1) = run(&ts);
    let (sk_time, a2) = run(sarkar);
    assert_eq!(a1, a2);

    println!(
        "{name}: tonelli-shanks {:?}, sarkar {:?}  ({:.2}x)",
        ts_time,
        sk_time,
        ts_time.as_secs_f64() / sk_time.as_secs_f64()
    );
}

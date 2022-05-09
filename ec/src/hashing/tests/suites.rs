use std::fs::{read_dir, File};
use std::io::BufReader;

use super::json::SuiteVector;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use libtest_mimic::{run_tests, Arguments, Outcome, Test};

use ark_ff::PrimeField;
use ark_test_curves::bls12_381::Fq;
use ark_test_curves::bls12_381::Fq2;
use sha2::Sha256;

#[test]
fn suites() {
    let args = Arguments::from_args();
    let mut tests_weierstrass = Vec::<Test<SuiteVector>>::new();

    for filename in read_dir("./src/hashing/tests/testdata").unwrap() {
        let file = File::open(filename.unwrap().path()).unwrap();
        let u: SuiteVector = serde_json::from_reader(BufReader::new(file)).unwrap();
        let test = Test {
            name: u.ciphersuite.clone(),
            data: u,
            kind: String::default(),
            is_ignored: false,
            is_bench: false,
        };
        tests_weierstrass.push(test);
    }
    run_tests(&args, tests_weierstrass, run_test_w).exit_if_failed();
}

fn run_test_w(Test { data, .. }: &Test<SuiteVector>) -> Outcome {
    assert_eq!(data.hash, "sha256");
    let dst = data.dst.as_bytes();
    let hasher;
    let m;
    match data.curve.as_str() {
        "BLS12-381 G1" => {
            m = 1;
            hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<Fq>>::new(dst);
        },
        "BLS12-381 G2" => {
            m = 2;
            hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<Fq2>>::new(dst);
        },
        _ => return Outcome::Ignored,
    }

    for v in data.vectors.iter() {
        let got: Vec<Fq> = hasher.hash_to_field(&v.msg.as_bytes(), 2 * m);
        let want: Vec<Fq> = (&v.u)
            .into_iter()
            .map(|x| {
                x.split(",").map(|f| {
                    Fq::from_be_bytes_mod_order(&hex::decode(f.trim_start_matches("0x")).unwrap())
                })
            })
            .flatten()
            .collect();
        if got != want {
            return Outcome::Failed {
                msg: Some(format!(
                    "Suite: {:?}\ngot:  {:?}\nwant: {:?}",
                    data.ciphersuite,
                    got[0].to_string(),
                    want[0].to_string()
                )),
            };
        }
    }
    Outcome::Passed
}

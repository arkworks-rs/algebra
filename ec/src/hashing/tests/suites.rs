use std::fs::{read_dir, File};
use std::io::BufReader;

use super::json::SuiteVector;
use libtest_mimic::{run_tests, Arguments, Outcome, Test};

use crate::hashing::map_to_curve_hasher::HashToField;
use crate::hashing::tests::IETFHasher;
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

    fn run_test_w(Test { data, .. }: &Test<SuiteVector>) -> Outcome {
        tt(data)
    }

    fn tt(u: &SuiteVector) -> Outcome {
        assert_eq!(u.hash, "sha256");
        let dst = u.dst.as_bytes();
        let hasher;
        match u.curve.as_str() {
            "BLS12-381 G2" => {
                hasher =
                    <IETFHasher<Sha256, 128> as HashToField<Fq>>::new_hash_to_field(dst).unwrap();
            },
            "BLS12-381 G1" => {
                hasher =
                    <IETFHasher<Sha256, 128> as HashToField<Fq2>>::new_hash_to_field(dst).unwrap();
            },
            _ => return Outcome::Ignored,
        }

        for v in u.vectors.iter() {
            let got: Vec<Fq> = hasher.hash_to_field(&v.msg.as_bytes(), 2).unwrap();
            let want: Vec<Fq> = (&v.u)
                .into_iter()
                .map(|x| Fq::from_be_bytes_mod_order(x.as_bytes()))
                .collect();
            if got != want {
                return Outcome::Failed {
                    msg: Some(format!(
                        "Suite: {:?}\ngot:  {:?}\nwant: {:?}",
                        u.ciphersuite, got, want
                    )),
                };
            }
        }
        Outcome::Passed
    }
}

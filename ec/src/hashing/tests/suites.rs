use std::fs::{read_dir, File};
use std::io::BufReader;

use super::json::SuiteVector;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use libtest_mimic::{run_tests, Arguments, Outcome, Test};

use ark_test_curves::{
    hashing::{curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
    short_weierstrass_jacobian::GroupAffine,
};

use ark_ff::{Field, PrimeField};
use ark_test_curves::bls12_381::{
    g1::Parameters as G1Parameters, g2::Parameters as G2Parameters, Fq, Fq2,
};
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
    let g1_mapper = MapToCurveBasedHasher::<
        GroupAffine<G1Parameters>,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<G1Parameters>,
    >::new(dst)
    .unwrap();
    let g2_mapper = MapToCurveBasedHasher::<
        GroupAffine<G2Parameters>,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<G2Parameters>,
    >::new(dst)
    .unwrap();
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
        // first, hash-to-field tests
        let got: Vec<Fq> = hasher.hash_to_field(&v.msg.as_bytes(), 2 * m);
        let want: Vec<Fq> = (&v.u)
            .into_iter()
            .map(|x| read_fq_vec(x))
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

        // then, test curve points
        let x: Vec<Fq> = read_fq_vec(&v.p.x);
        let y: Vec<Fq> = read_fq_vec(&v.p.y);
        let x_q0: Vec<Fq> = read_fq_vec(&v.q0.x);
        let x_q1: Vec<Fq> = read_fq_vec(&v.q1.x);
        let y_q0: Vec<Fq> = read_fq_vec(&v.q0.y);
        let y_q1: Vec<Fq> = read_fq_vec(&v.q1.y);
        match data.curve.as_str() {
            "BLS12-381 G1" => {
                let out = g1_mapper.hash(&v.msg.as_bytes()).unwrap();
                let got = out.0;
                let want = GroupAffine::<G1Parameters>::new(
                    Fq::from_base_prime_field_elems(&x[..]).unwrap(),
                    Fq::from_base_prime_field_elems(&y[..]).unwrap(),
                    false,
                );
                assert!(got.is_on_curve());
                assert!(want.is_on_curve());
                if got != want {
                    return Outcome::Failed {
                        msg: Some(format!(
                            "Suite: {:?}\ngot:  {:?}\nwant: {:?}",
                            data.ciphersuite,
                            got.to_string(),
                            want.to_string()
                        )),
                    };
                }
            },
            "BLS12-381 G2" => {
                let out = g2_mapper.hash(&v.msg.as_bytes()).unwrap();
                let q0 = out.1;
                let q1 = out.2;
                let got = out.0;
                let want_q0 = GroupAffine::<G2Parameters>::new(
                    Fq2::from_base_prime_field_elems(&x_q0[..]).unwrap(),
                    Fq2::from_base_prime_field_elems(&y_q0[..]).unwrap(),
                    false,
                );
                let want_q1 = GroupAffine::<G2Parameters>::new(
                    Fq2::from_base_prime_field_elems(&x_q1[..]).unwrap(),
                    Fq2::from_base_prime_field_elems(&y_q1[..]).unwrap(),
                    false,
                );
                let want = GroupAffine::<G2Parameters>::new(
                    Fq2::from_base_prime_field_elems(&x[..]).unwrap(),
                    Fq2::from_base_prime_field_elems(&y[..]).unwrap(),
                    false,
                );
                assert!(got.is_on_curve());
                assert!(want.is_on_curve());
                if got != want {
                    return Outcome::Failed {
                        msg: Some(format!(
                            "Suite: {:?}\nmsg: {}\n\ngot: {:?}\nwant: {:?}\n\ngot Q0: {}\nwant Q0: {}\n\ngot Q1: {}\nwant Q1: {}",
                            data.ciphersuite,
                            v.msg,
                            got.to_string(),
                            want.to_string(),
                            q0.to_string(),
                            want_q0.to_string(),
                            q1.to_string(),
                            want_q1.to_string(),
                        )),
                    };
                }
            },
            _ => return Outcome::Ignored,
        }
    }
    Outcome::Passed
}

fn read_fq_vec(input: &String) -> Vec<Fq> {
    input
        .split(",")
        .map(|f| Fq::from_be_bytes_mod_order(&hex::decode(f.trim_start_matches("0x")).unwrap()))
        .collect()
}

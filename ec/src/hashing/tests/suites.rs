use std::fs::{read_dir, File};
use std::io::BufReader;

use super::json::SuiteVector;
use libtest_mimic::{run_tests, Arguments, Outcome, Test};

use ark_test_curves::{
    hashing::{
        curve_maps::swu::{parity, SWUMap, SWUParams},
        field_hashers::DefaultFieldHasher,
        map_to_curve_hasher::{HashToField, MapToCurve, MapToCurveBasedHasher},
        HashToCurve,
    },
    short_weierstrass_jacobian::GroupAffine,
    ModelParameters, SWModelParameters,
};

use ark_ff::PrimeField;
use ark_test_curves::bls12_381::Fq2;
use ark_test_curves::bls12_381::{Fq, SwuIsoParameters};
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
    let mapper;
    let hasher;
    let m;
    // TODO: differentiate between G1 and G2 Params!
    mapper = MapToCurveBasedHasher::<
        GroupAffine<SwuIsoParameters>,
        DefaultFieldHasher<Sha256, 128>,
        SWUMap<SwuIsoParameters>,
    >::new(dst)
    .unwrap();
    match data.curve.as_str() {
        "BLS12-381 G1" => {
            m = 1;
            hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<Fq>>::new_hash_to_field(dst)
                .unwrap();
        },
        "BLS12-381 G2" => {
            m = 2;
            hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<Fq2>>::new_hash_to_field(dst)
                .unwrap();
        },
        _ => return Outcome::Ignored,
    }

    for v in data.vectors.iter() {
        // first, test field elements
        let got: Vec<Fq> = hasher.hash_to_field(&v.msg.as_bytes(), 2 * m).unwrap();
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
        // then, test curve points
        let got: GroupAffine<SwuIsoParameters> = mapper.hash(&v.msg.as_bytes()).unwrap();
        assert!(got.is_on_curve());
        let x: Vec<Fq> = (&v.p.x)
            .split(",")
            .map(|f| Fq::from_be_bytes_mod_order(&hex::decode(f.trim_start_matches("0x")).unwrap()))
            .collect();
        let y: Vec<Fq> = (&v.p.y)
            .split(",")
            .map(|f| Fq::from_be_bytes_mod_order(&hex::decode(f.trim_start_matches("0x")).unwrap()))
            .collect();
        let want: GroupAffine<SwuIsoParameters> =
            GroupAffine::<SwuIsoParameters>::new(x[0], y[0], false);
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
    }
    Outcome::Passed
}

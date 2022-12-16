use std::{
    fs::{read_dir, File},
    io::BufReader,
};

use super::json::SuiteVector;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use libtest_mimic::{run, Arguments, Failed, Trial};

use ark_test_curves::{
    hashing::{curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
    short_weierstrass::{Affine, Projective},
};

use ark_ff::{Field, PrimeField};
use ark_test_curves::bls12_381::{
    g1::Parameters as G1Parameters, g2::Parameters as G2Parameters, Fq, Fq2,
};
use sha2::Sha256;

#[test]
fn suites() {
    let args = Arguments::from_args();
    let mut tests_weierstrass = Vec::<Trial>::new();

    for filename in read_dir("./src/hashing/tests/testdata").unwrap() {
        let file = File::open(filename.unwrap().path()).unwrap();
        let u: SuiteVector = serde_json::from_reader(BufReader::new(file)).unwrap();
        let test = Trial::test(u.ciphersuite.clone(), move || run_test_w(&u));
        tests_weierstrass.push(test);
    }
    run(&args, tests_weierstrass).exit_if_failed();
}

fn run_test_w(data: &SuiteVector) -> Result<(), Failed> {
    assert_eq!(data.hash, "sha256");
    let dst = data.dst.as_bytes();
    let hasher;
    let m;
    let g1_mapper = MapToCurveBasedHasher::<
        Projective<G1Parameters>,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<G1Parameters>,
    >::new(dst)
    .unwrap();
    let g2_mapper = MapToCurveBasedHasher::<
        Projective<G2Parameters>,
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
        _ => return Err("unsupported test suite".into()),
    }

    for v in data.vectors.iter() {
        // first, hash-to-field tests
        let got: Vec<Fq> = hasher.hash_to_field(&v.msg.as_bytes(), 2 * m);
        let want: Vec<Fq> = v.u.iter().map(read_fq_vec).flatten().collect();
        if got != want {
            return Err(format!(
                "Suite: {:?}\ngot: {}\nwant: {}",
                data.ciphersuite, got[0], want[0],
            )
            .into());
        }

        // then, test curve points
        let x = read_fq_vec(&v.p.x);
        let y = read_fq_vec(&v.p.y);
        match data.curve.as_str() {
            "BLS12-381 G1" => {
                let got = g1_mapper.hash(&v.msg.as_bytes()).unwrap();
                let want = Affine::<G1Parameters>::new_unchecked(
                    Fq::from_base_prime_field_elems(&x[..]).unwrap(),
                    Fq::from_base_prime_field_elems(&y[..]).unwrap(),
                );
                assert!(got.is_on_curve());
                assert!(want.is_on_curve());
                if got != want {
                    return Err(format!(
                        "Suite: {:?}\ngot: {}\nwant: {}",
                        data.ciphersuite, got, want,
                    )
                    .into());
                }
            },
            "BLS12-381 G2" => {
                let got = g2_mapper.hash(&v.msg.as_bytes()).unwrap();
                let want = Affine::<G2Parameters>::new_unchecked(
                    Fq2::from_base_prime_field_elems(&x[..]).unwrap(),
                    Fq2::from_base_prime_field_elems(&y[..]).unwrap(),
                );
                assert!(got.is_on_curve());
                assert!(want.is_on_curve());
                if got != want {
                    return Err(format!(
                        "Suite: {:?}\nmsg: {}\n\ngot: {}\nwant: {}",
                        data.ciphersuite, v.msg, got, want,
                    )
                    .into());
                }
            },
            _ => return Err("unsupported test suite".into()),
        }
    }
    Ok(())
}

fn read_fq_vec(input: &String) -> Vec<Fq> {
    input
        .split(",")
        .map(|f| Fq::from_be_bytes_mod_order(&hex::decode(f.trim_start_matches("0x")).unwrap()))
        .collect()
}

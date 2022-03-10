use std::fs::{read_dir, File};
use std::io::BufReader;

use super::json::SuiteVector;
use libtest_mimic::{run_tests, Arguments, Outcome, Test};

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
        match u.curve.as_str() {
            "BLS12-381 G1" => {
                assert_eq!(u.hash, "sha256");
                // let h2c = suite.get(u.dst.as_bytes());
                // let curve = h2c.get_curve();
                // let f = curve.get_field();
                for v in u.vectors.iter() {
                    // let got = h2c.hash(v.msg.as_bytes());
                    // let x = f.from(&v.p.x);
                    // let y = f.from(&v.p.y);
                    // let want = curve.new_point(x, y);
                    // if got != want {
                    //     return Outcome::Failed {
                    //         msg: Some(format!(
                    //             "Suite: {}\ngot:  {}\nwant: {}",
                    //             u.ciphersuite, got, want
                    //         )),
                    //     };
                    // }
                }
                Outcome::Passed
            },
            "BLS12-381 G2" => Outcome::Ignored,
            _ => Outcome::Ignored,
        }
    }
}

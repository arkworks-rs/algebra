pub mod json;
extern crate hex;
extern crate serde_json;
extern crate sha2;
pub use hex::decode;
pub use serde_json::from_reader;
pub use sha2::Sha256;

#[macro_export]
macro_rules! test_h2c {
    ($mod_name: ident; $test_path: literal; $test_name: literal; $group: ty; $field: ty; $base_prime_field: ty; $m: literal) => {
        mod $mod_name {
            use ark_ff::PrimeField;

            extern crate std;
            use ark_ec::{
                hashing::{
                    wb::WBMap, HashToCurve,
                },
                short_weierstrass::{Affine, Projective},
                CurveGroup,
            };
            use ark_ff::{
                field_hashers::{xmd_hash_to_field}, // zpad_expander, expand_for_field
                fields::Field,
                One, UniformRand, Zero,
            };
            use ark_std::{format, string::String, vec::Vec};
            use std::{
                fs::{read_dir, File},
                io::BufReader,
            };
            use $crate::{decode, Sha256};

            use $crate::json::SuiteVector;
            #[test]
            fn test_h2c() {
                let filename = format!("{}/{}_XMD-SHA-256_SSWU_RO_.json", $test_path, $test_name);

                let file = File::open(filename).unwrap();
                let data: SuiteVector = $crate::from_reader(BufReader::new(file)).unwrap();

                assert_eq!(data.hash, "sha256");
                let dst = data.dst.as_bytes();

                for v in data.vectors.iter() {

                    // first, hash-to-field tests
                    let got: [$base_prime_field; {  2* $m } ] =
                        xmd_hash_to_field::<Sha256,Projective<TestSWUMapToCurveConfig>,{  2* $m }>(128,dst,&v.msg.as_bytes());
                    let want: Vec<$base_prime_field> =
                        v.u.iter().map(read_fq_vec).flatten().collect();
                    assert_eq!(got[..], *want);

                    // then, test curve points
                    let x = read_fq_vec(&v.p.x);
                    let y = read_fq_vec(&v.p.y);
                    let got = <Projective<$group> as HashToCurve>::hash_to_curve(dst,v.msg.as_bytes()).unwrap().into_affine();
                    let want = Affine::<$group>::new_unchecked(
                        <$field>::from_base_prime_field_elems(x).unwrap(),
                        <$field>::from_base_prime_field_elems(y).unwrap(),
                    );
                    assert!(got.is_on_curve());
                    assert!(want.is_on_curve());
                    assert_eq!(got, want);
                }
            }
            pub fn read_fq_vec(input: &String) -> Vec<$base_prime_field> {
                input
                    .split(",")
                    .map(|f| {
                        <$base_prime_field>::from_be_bytes_mod_order(
                            &decode(f.trim_start_matches("0x")).unwrap(),
                        )
                    })
                    .collect()
            }
        }
    };
}

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
                    curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve,
                },
                short_weierstrass::{Affine, Projective},
            };
            use ark_ff::{
                field_hashers::{DefaultFieldHasher, HashToField},
                fields::Field,
                One, UniformRand, Zero,
            };
            use ark_std::{format, string::String, vec::Vec};
            use std::{
                fs::{read_dir, File},
                io::BufReader,
            };
            use $crate::decode;
            use $crate::Sha256;

            use $crate::json::SuiteVector;
            #[test]
            fn test_h2c() {
                let filename = format!("{}/{}_XMD-SHA-256_SSWU_RO_.json", $test_path, $test_name);

                let file = File::open(filename).unwrap();
                let data: SuiteVector = $crate::from_reader(BufReader::new(file)).unwrap();

                assert_eq!(data.hash, "sha256");
                let dst = data.dst.as_bytes();
                let hasher;
                let g1_mapper = MapToCurveBasedHasher::<
                    Projective<$group>,
                    DefaultFieldHasher<Sha256, 128>,
                    WBMap<$group>,
                >::new(dst)
                .unwrap();
                hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<$field>>::new(dst);

                for v in data.vectors.iter() {
                    // first, hash-to-field tests
                    let got: Vec<$base_prime_field> =
                        hasher.hash_to_field(&v.msg.as_bytes(), 2 * $m);
                    let want: Vec<$base_prime_field> =
                        v.u.iter().map(read_fq_vec).flatten().collect();
                    assert_eq!(got, want);

                    // then, test curve points
                    let x = read_fq_vec(&v.p.x);
                    let y = read_fq_vec(&v.p.y);
                    let got = g1_mapper.hash(&v.msg.as_bytes()).unwrap();
                    let want = Affine::<$group>::new_unchecked(
                        <$field>::from_base_prime_field_elems(&x[..]).unwrap(),
                        <$field>::from_base_prime_field_elems(&y[..]).unwrap(),
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

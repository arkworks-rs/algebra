use libtest_mimic::{run, Arguments, Failed, Trial};

use sha2::{Sha256, Sha384, Sha512};
use sha3::{Shake128, Shake256, digest::{Update,XofReader}};
use std::{
    fs::{read_dir, File},
    io::BufReader,
};

use super::{DST,IrtfH2F};

#[derive(Debug, serde_derive::Serialize, serde_derive::Deserialize)]
pub struct ExpanderVector {
    #[serde(rename = "DST")]
    pub dst: String,
    pub k: usize, // sec_param
    pub hash: String,
    pub name: String,
    #[serde(rename = "tests")]
    pub vectors: Vec<TestExpander>,
}

#[derive(Debug, serde_derive::Serialize, serde_derive::Deserialize)]
pub struct TestExpander {
    #[serde(rename = "DST_prime")]
    pub dst_prime: String,
    pub len_in_bytes: String,
    pub msg: String,
    pub msg_prime: String,
    pub uniform_bytes: String,
}

#[test]
fn expander() {
    let args = Arguments::from_args();
    let mut tests = Vec::<Trial>::new();

    for filename in read_dir("./src/fields/field_hashers/expander/testdata").unwrap() {
        let ff = filename.unwrap();
        let file = File::open(ff.path()).unwrap();
        let u: ExpanderVector = serde_json::from_reader(BufReader::new(file)).unwrap();

        tests.push(Trial::test(
            ff.file_name().to_str().unwrap().to_string(),
            move || do_test(u),
        ));
    }

    run(&args, tests).exit_if_failed();
}

fn do_test(data: ExpanderVector) -> Result<(), Failed> {
    let dst = match data.hash.as_str() {
        "SHA256" => DST::new_xmd::<Sha256>(data.dst.as_bytes()),
        "SHA384" => DST::new_xmd::<Sha384>(data.dst.as_bytes()),
        "SHA512" => DST::new_xmd::<Sha512>(data.dst.as_bytes()),
        "SHAKE128" => DST::new_xof::<Shake128>(data.dst.as_bytes(), Some(data.k)),
        "SHAKE256" => DST::new_xof::<Shake256>(data.dst.as_bytes(), Some(data.k)),
        _ => unimplemented!(),
    };

    for v in data.vectors.iter() {
        let len = usize::from_str_radix(v.len_in_bytes.trim_start_matches("0x"), 16).unwrap();
        let got = match data.hash.as_str() {
            "SHA256"   => IrtfH2F::<Sha256>::new_xmd().chain(v.msg.as_bytes()).expand_xmd(&dst,len).read_boxed(len),
            "SHA384"   => IrtfH2F::<Sha384>::new_xmd().chain(v.msg.as_bytes()).expand_xmd(&dst,len).read_boxed(len),
            "SHA512"   => IrtfH2F::<Sha512>::new_xmd().chain(v.msg.as_bytes()).expand_xmd(&dst,len).read_boxed(len),
            "SHAKE128" => IrtfH2F::<Shake128>::new_xof().chain(v.msg.as_bytes()).expand_xof(&dst,len).read_boxed(len),
            "SHAKE256" => IrtfH2F::<Shake256>::new_xof().chain(v.msg.as_bytes()).expand_xof(&dst,len).read_boxed(len),
            _ => unimplemented!(),
        };
        let want = hex::decode(&v.uniform_bytes).unwrap();
        if &*got != want.as_slice() {
            return Err(format!(
                "Expander: {}\nVector:   {}\ngot:  {:?}\nwant: {:?}",
                data.hash, v.msg, got, want,
            )
            .into());
        }
    }
    Ok(())
}

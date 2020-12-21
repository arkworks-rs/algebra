extern crate rustc_version;
use rustc_version::{version_meta, Channel};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let is_nightly = version_meta().expect("nightly check failed").channel == Channel::Nightly;

    let should_use_asm = cfg!(all(
        feature = "asm",
        target_feature = "bmi2",
        target_feature = "adx",
        target_arch = "x86_64"
    )) && is_nightly;
    if should_use_asm {
        println!("cargo:rustc-cfg=use_asm");
    }

    let should_use_bw6_asm = cfg!(any(
        all(
            feature = "bw6_asm",
            target_feature = "bmi2",
            target_feature = "adx",
            target_arch = "x86_64"
        ),
        feature = "force_bw6_asm"
    ));
    if should_use_bw6_asm {
        cc::Build::new()
            .file("bw6-assembly/modmul768-sos1-adx.S")
            .compile("modmul768");
        cc::Build::new()
            .file("bw6-assembly/modadd768.S")
            .compile("modadd768");
        cc::Build::new()
            .file("bw6-assembly/modsub768.S")
            .compile("modsub768");
        println!("cargo:rustc-cfg=use_bw6_asm");
    }
}

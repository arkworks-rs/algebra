extern crate rustc_version;
use rustc_version::{version, version_meta, Channel, Version};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let is_nightly = version_meta().expect("nightly check failed").channel == Channel::Nightly;

    let asm_enabled = cfg!(feature = "asm");
    let bmi2_enabled  = cfg!(target_feature = "bmi2");
    let adx_enabled  = cfg!(target_feature = "adx");
    let is_x86_64  = cfg!(target_arch = "x86_64");
    // Left in for debugging purposes.
    // assert!(asm_enabled, "failed asm check");
    // assert!(is_x86_64, "failed x86_64 check");
    // assert!(adx_enabled, "failed adx check");
    // assert!(bmi2_enabled, "failed bmi2 check");
    let should_use_asm = asm_enabled && bmi2_enabled && adx_enabled && is_x86_64 && is_nightly;
    if should_use_asm {
        println!("cargo:rustc-cfg=use_asm");
    }

    // TODO: remove this once RFC 2495 ships
    if version().expect("Installed rustc version unparseable!") < Version::parse("1.51.0").unwrap()
    {
        panic!("This code base uses const generics and requires a Rust compiler version greater or equal to 1.51.0");
    }
}

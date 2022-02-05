use rustc_version::Version;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let rust_version = rustc_version::version().unwrap();
    if rust_version >= Version::new(1, 59, 0) {
        println!("cargo:rustc-cfg=inline_asm_stable");
    }
}

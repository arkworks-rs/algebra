use rustc_version::Version;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let target_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();

    let is_x86_64 = target_arch == "x86_64";
    let mut bmi2_enabled = false;
    let mut adx_enabled = false;
    if is_x86_64 {
        bmi2_enabled = is_x86_feature_detected!("bmi2");
        adx_enabled = is_x86_feature_detected!("adx");
    }

    let rust_version = rustc_version::version().unwrap();
    println!("rust_version = {}", rust_version);
    let is_asm_stable = rust_version >= Version::new(1, 59, 0);

    println!("is_asm_stable = {}", is_asm_stable);
    if is_x86_64 {
        println!("bmi2_enabled = {}", bmi2_enabled);
        println!("adx_enabled = {}", adx_enabled);
    }

    let should_use_asm = is_asm_stable && bmi2_enabled && adx_enabled && is_x86_64;
    if should_use_asm {
        println!("cargo:rustc-cfg=use_asm");
    }
}

fn main() {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let link_script = format!("{manifest_dir}/../../../crates/zkvm-guest/link.ld");
    println!("cargo:rustc-link-arg=-T{link_script}");
    println!("cargo:rerun-if-changed={link_script}");
}

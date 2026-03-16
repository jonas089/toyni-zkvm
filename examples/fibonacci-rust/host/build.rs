use std::process::Command;

fn main() {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let guest_dir = format!("{manifest_dir}/../guest");

    println!("cargo:rerun-if-changed={guest_dir}/src/main.rs");
    println!("cargo:rerun-if-changed={guest_dir}/Cargo.toml");

    let status = Command::new("cargo")
        .args([
            "build",
            "--release",
            "--target", "riscv32i-unknown-none-elf",
            "--manifest-path", &format!("{guest_dir}/Cargo.toml"),
        ])
        .status()
        .expect("Failed to run cargo build for guest");

    assert!(status.success(), "Guest build failed");
}

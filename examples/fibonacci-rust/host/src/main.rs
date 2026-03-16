/// Fibonacci ZKVM example using Rust guest program.
///
/// Compiles a Rust guest that computes fib(n), proves execution
/// inside the ZKVM, and verifies the STARK proof.
use zkvm_host::ProverBuilder;

const GUEST_ELF: &[u8] =
    include_bytes!("../../guest/target/riscv32i-unknown-none-elf/release/fibonacci-guest");

fn main() {
    let n = 10u32;
    println!("Computing fib({n}) with Rust guest program + ZKVM proof...");

    let mut builder = ProverBuilder::from_elf(GUEST_ELF);
    builder.add_input(n);

    println!("Executing guest and generating STARK proof...");
    let receipt = builder.prove();

    println!("Output: {:?}", receipt.outputs);
    if !receipt.outputs.is_empty() {
        println!("fib({n}) = {}", receipt.outputs[0]);
    }

    println!("Verifying proof...");
    if receipt.verify() {
        println!("PROOF VERIFIED SUCCESSFULLY!");
    } else {
        println!("PROOF VERIFICATION FAILED!");
        std::process::exit(1);
    }
}

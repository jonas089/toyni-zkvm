/// Heavy ZKVM example: long-running compute loop in the guest, intended as a
/// large-trace workload for prover benchmarking (CPU baseline). For a GPU
/// benchmark, prove the guest ELF directly via `zkvm-cli prove --cuda`.
use zkvm_host::ProverBuilder;

const GUEST_ELF: &[u8] =
    include_bytes!("../../guest/target/riscv32i-unknown-none-elf/release/heavy-guest");

fn main() {
    let seed = 42u32;
    println!("Running heavy guest workload + ZKVM proof (CPU)...");

    let mut builder = ProverBuilder::from_elf(GUEST_ELF);
    builder.add_input(seed);

    let receipt = builder.prove();

    println!("Output: {:?}", receipt.outputs);

    if receipt.verify() {
        println!("PROOF VERIFIED SUCCESSFULLY!");
    } else {
        println!("PROOF VERIFICATION FAILED!");
        std::process::exit(1);
    }
}

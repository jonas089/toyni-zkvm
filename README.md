## Examples

### Fibonacci Example

The project includes a Fibonacci sequence calculator as an example:

```bash
# Build the example
cd examples/fibonacci-rust/guest
cargo build --release

# Run and prove
zkvm-cli prove target/riscv32i-unknown-none-elf/release/fibonacci-guest
```

### Heavy Example (GPU Benchmark)

The `heavy-rust` example runs a long compute loop in the guest (~150k LCG
iterations) so the execution trace pads close to 2^20 rows. Each prover-side
NTT is then large enough that GPU activity is visible on profilers like
`nvtop` / `nvidia-smi`.

```bash
# 1) Build zkvm-cli with CUDA enabled
cargo install --path crates/zkvm-cli --features cuda

# 2) Build the heavy guest
cd examples/heavy-rust/guest
cargo build --release

# 3) Prove with --cuda and watch the GPU
#    In one terminal:
nvidia-smi pmon -d 1
#    In another (from repo root):
zkvm-cli prove examples/heavy-rust/guest/target/riscv32i-unknown-none-elf/release/heavy-guest --cuda
```

`nvtop` averages over ~1s windows and tends to miss short kernel bursts; for
fine-grained verification, use `nsys profile --stats=true` instead.

For a CPU baseline (no GPU), build and run the host wrapper:

```bash
cargo run --release -p heavy-rust-host
```

## Development

### Running Tests

```bash
cargo test
```

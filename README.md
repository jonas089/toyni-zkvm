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
## Development

### Running Tests

```bash
cargo test
```
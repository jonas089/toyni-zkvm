# zkvm

A small zero-knowledge virtual machine with a custom 11-instruction ISA,
built on [Toyni](https://github.com/jonas089/toyni) as its STARK
proving backend.

> [!CAUTION]
> **This is research / hobby code.** It has **not** been audited and is
> not suitable for production use. Do not rely on it for any setting
> where a broken proof would have real-world consequences.

## Status

- **Toyni (proving backend)**: solid. Core STARK toolkit + CUDA NTT path.
- **zkvm (this repo)**: the AIR aims to be a *fully constrained* minimal
  VM — every trace column is fixed by a transition/boundary constraint or
  bound by a permutation/lookup argument, leaving the prover no
  unconstrained freedom. The earlier v1 soundness gaps (un-range-checked
  ordering, unbound init values, free post-halt rows, negative LogUp
  multiplicities) are closed; see "Soundness" below. Substantial portions
  of the constraints were drafted with Claude's assistance and the system
  has **not** been audited.

Getting an instruction-set + AIR + proving pipeline right end-to-end is
genuinely ambitious for a single person. I'm working on it as a side
project, and external contributions, reviews, and bug reports are very
welcome. Open an issue or PR if you want to help close any of the gaps.

## The ISA in one page

Field-native: every register, memory cell, immediate, and PC value is a
BabyBear field element. There is no u32, no carries, no signed/unsigned,
no overflow.

- **8 registers** `r0..r7`. `r0` is hardwired to 0 (writes ignored).
- **Linear memory** addressed by field element (sparse; unwritten cells
  read as 0).
- **Public input/output tapes** consumed by `READ` and produced by `WRITE`.
- **PC advances by 1** per instruction; `JMP`/`JZ` use absolute targets.
- **Halt** via the `HALT` instruction.

| # | Mnemonic | Args | Effect |
|---|----------|------|--------|
| 1 | `ADD`   | `rd, ra, rb` | `rd = ra + rb` |
| 2 | `SUB`   | `rd, ra, rb` | `rd = ra - rb` |
| 3 | `MUL`   | `rd, ra, rb` | `rd = ra * rb` |
| 4 | `IMM`   | `rd, K`      | `rd = K` |
| 5 | `LOAD`  | `rd, ra`     | `rd = mem[ra]` |
| 6 | `STORE` | `ra, rb`     | `mem[ra] = rb` |
| 7 | `JMP`   | `label`      | `pc = label` |
| 8 | `JZ`    | `ra, label`  | if `ra == 0` then `pc = label` |
| 9 | `READ`  | `rd`         | `rd = next public input` |
| 10 | `WRITE`| `ra`         | append `ra` to public outputs |
| 11 | `HALT` |              | terminate |

The assembler also accepts `MOV rd, rs` as a pseudo-instruction
(expands to `ADD rd, rs, r0`).

## Architecture

```mermaid
graph TD
    subgraph Frontend["Frontend (in zkvm-cli)"]
        MINI["fibonacci.mini<br/>(very simple DSL)"]
        ASM["mini → asm<br/>compiler"]
        ASMP["asm → instructions<br/>assembler"]
    end

    subgraph Core["zkvm-core"]
        EXEC["VM execution<br/>(11 instructions)"]
        TRACE["StepRecord per cycle<br/>+ column builder"]
    end

    subgraph AIR["zkvm-air"]
        TRANS["Transition constraints"]
        PERM["Permutation accumulators<br/>reg · mem · prog · pub_in · pub_out"]
    end

    subgraph Prover["zkvm-prover"]
        PIPE["Two-phase commit →<br/>quotient → DEEP → FRI → queries"]
    end

    subgraph Backend["Toyni"]
        BB["BabyBear field"]
        NTT["NTT (CPU + CUDA)"]
        MT["Merkle / Fiat-Shamir"]
    end

    Verifier["zkvm-verifier"]

    MINI --> ASM
    ASM --> ASMP
    ASMP --> EXEC
    EXEC --> TRACE
    TRACE --> Prover
    AIR -.constraints.-> Prover
    Prover --> Backend
    Backend --> Proof([ZkvmProof])
    Proof --> Verifier
    AIR -.same constraints.-> Verifier

    classDef warn fill:#fff4e6,stroke:#f59f00
    class AIR warn
```

## Crates

| Crate | Role |
|-------|------|
| `zkvm-core` | VM execution, step records, column layout, trace builder |
| `zkvm-air`  | Transition + accumulator constraints over the trace columns |
| `zkvm-prover` | Two-phase commit + quotient + DEEP + FRI + query pipeline |
| `zkvm-verifier` | Fiat-Shamir replay, OOD constraint check, FRI query verification, Lagrange-binding of the program ROM and public I/O tables |
| `zkvm-cli` | `prove` command, embedded assembler and `mini` compiler |

## The `mini` DSL

`mini` is a deliberately tiny language that maps 1:1 to asm. No nested
expressions, no functions, no types, no closures. Each statement is one
ALU op, one memory op, one I/O op, or one control-flow op.

```mini
let n = read();
let a = 0;
let b = 1;
let one = 1;
while n != 0 {
    let t = a + b;
    let a = b;
    let b = t;
    n = n - one;
}
write(a);
halt;
```

A maximum of 7 user variables (one per non-`r0` register). The compiler
is ~250 lines.

## Build and run

```bash
# Prove + verify the fibonacci example with input n=10
cargo run --release -p zkvm-cli -- prove examples/fibonacci.mini -i 10

# Or with the CUDA NTT backend (requires nvcc + a CUDA-capable GPU)
cargo run --release -p zkvm-cli --features cuda -- \
    prove examples/fibonacci.mini -i 10 --cuda

# Set ZKVM_DUMP_ASM=1 to print the generated assembly before running.
ZKVM_DUMP_ASM=1 cargo run --release -p zkvm-cli -- prove examples/fibonacci.mini -i 5
```

## Soundness

The AIR enforces:

- **Per-instruction semantics.** Every opcode's selector forces the
  corresponding effect on its slots: ALU/IMM constrain register writes,
  LOAD/STORE pin memory addr+val to register slots, JMP/JZ/HALT control
  PC, READ/WRITE bind public-IO cursors. Selector booleanity + sum-to-1
  + OPCODE-column reconstruction prevent the prover from running two
  opcodes' constraints on the same row or none at all.
- **Register-file consistency.** Three register-access slots per row
  enter a 4-channel grand-product permutation against a sorted table.
  Each slot carries an explicit **activity flag**: an inactive slot is
  forced fully zero, and each opcode is constrained to activate exactly
  the slots it uses. Within the sorted table, read-after-write constraints
  force any read of a register to return the most recent write's value, a
  fresh register read returns 0, and `idx = 0 ⇒ val = 0` (r0) is pinned on
  every sorted entry. Cross-slot transitions (B vs A, C vs B, A[i+1] vs
  C[i]) are all constrained.
- **Memory consistency.** Same shape as the register file with one slot
  per row, gated by a `MEM_USED` flag tied to LOAD/STORE selectors.
- **Strict sorted-table ordering.** Each sorted access carries a unique
  key — registers use access time `t = clk·3 + slot` (so reading a
  register twice in one row stays distinct), memory uses `(addr, clk)`
  with one access per row. Every sorted transition checks
  `diff = 1 + Σ bitₖ·2ᵏ` over 16 boolean bits, i.e. a *strictly* positive,
  range-checked step. Reversed orderings produce diffs of size ~2³¹, far
  outside the bit budget, and the reconstruction constraint catches them.
  The first entry of each sorted table is bound (r0 pin for registers, a
  zero init record for memory), closing the "first entry is never a
  transition target" gap.
- **Post-halt rows replay HALT.** Once the HALT flag is set, every padding
  row is constrained to re-select HALT, so it freezes the PC, touches no
  register/memory/I-O lane, and its ROM lookup matches the real HALT entry.
- **Program ROM binding.** The (PC, opcode, op_a, op_b, op_c) executed
  on each row is matched (4-channel LogUp) against a Lagrange-bound
  ROM table whose hash is committed in the proof's public values. ROM
  rows are constrained contiguous from PC 0 (so PCs are distinct and
  gap-free), and each row's LogUp multiplicity is range-checked
  non-negative, blocking negative-multiplicity cancellation.
- **Public input/output binding.** READ rows feed `(i_in, val)` into a
  4-channel LogUp against a Lagrange-bound public-input table; WRITE
  rows do the symmetric thing on the output side.
- **Boundary.** First-row state is forced (CLK=0, PC=entry_pc, HALT=0,
  cursors=0, all 20 accumulator initial values pinned). Last-row HALT=1.
  HALT monotonicity prevents un-halting.
- **r0 hardwiring.** Per-row inverse-trick on each register-access slot
  forces `idx=0 ⇒ val=0`.
- **Extension-field challenges.** The trace is committed over the base
  field BabyBear (~31 bits), but every random challenge — the lookup /
  permutation γ and α, the out-of-domain point, and the FRI folding βs —
  is drawn from the quartic extension `BabyBear[X]/(X⁴−11)` (~124 bits).
  The accumulators, quotient, DEEP composition and FRI layers are therefore
  extension-valued. This lifts the soundness of every randomized argument
  off the small base field. (Multiple γ/α channels are retained as belt-
  and-suspenders.)
- **Program pinning.** `verify(proof, expected_program_hash, expected_entry_pc)`
  rejects unless the proof's program hash and entry point match what the
  caller supplies, so a passing proof certifies *your* program ran — not
  merely *some* self-consistent program.

### Known limitations

- **16-bit ordering / range budget.** Sorted-table diffs and ROM
  multiplicities are decomposed into 16 boolean bits, so the bound
  `2¹⁶ > 3·trace_len` and `2¹⁶ > max memory address` must hold. For the
  default trace length (a few hundred rows) this is comfortable; very long
  traces or large memory addresses would need a wider decomposition
  (`col::DIFF_BITS`). The booleanity of every bit is itself constrained
  inside the AIR.
- **Last-row exception.** All *main* transition constraints are excepted on
  the final trace row (a padding HALT row); only the cyclic accumulator
  arguments hold there. See the AIR module docs.
- **Not audited.** This is research / hobby code; see the caution at the
  top.

This is meant to be reviewable by hand. The whole AIR is one file
(`crates/zkvm-air/src/lib.rs`), with adversarial unit tests (`cargo test
-p zkvm-air`) that tamper an honest trace to confirm each constraint
fires. If you find a gap, please open an issue or PR.

## Development

```bash
cargo test
cargo run --release -p zkvm-cli -- prove examples/fibonacci.mini -i 7
```

# zkvm ISA spec (v1, draft)

This is the design doc for a small custom instruction set that replaces RV32I
in this project. The goal is an ISA that's small enough to review in one
sitting and to constrain soundly without months of effort.

> Status: design draft, not implemented yet. Sanity-check this document
> before any code is written.

## 1. Scope and non-goals

**In scope:**

- A tiny VM that executes programs over the BabyBear field.
- Enough power to express simple algorithms (loops, branches, arithmetic,
  memory, public I/O).
- Constraint system small enough that one person can review every column
  and every constraint.

**Not in scope:**

- u32 / signed / overflow semantics. Values are field elements.
- Bitwise ops, shifts, comparisons other than equality-with-zero.
- Compiling Rust (or any standard language). Guests are written in
  hand-asm or in the very simple DSL `mini` (§11).
- System calls, interrupts, traps.

## 2. Field

Base field `F = BabyBear`, with `p = 2^31 - 2^27 + 1 = 2_013_265_921`.
Every register, memory cell, immediate, PC value, and instruction operand
is a field element. Arithmetic is field arithmetic; there is no
overflow because there is no integer interpretation.

A program that writes `IMM r1, p` produces zero in `r1`. Program authors
are expected to keep values within `[0, p)` if they want integer-like
intuition. This is documented behaviour, not a bug.

## 3. Machine state

| Component | Size | Notes |
|-----------|------|-------|
| Register file | 8 cells, indexed `r0..r7` | `r0` is hardwired to 0 |
| Data memory | mapping `F -> F` | sparse; unwritten cells read as 0 |
| Program counter `pc` | 1 field element | indexes instructions, increments by 1 |
| Halt flag | 1 bit | once set, stays set |
| Input cursor `i_in` | 1 field element | next position to read |
| Output cursor `i_out` | 1 field element | next position to append |

There is no separate stack, no flags register, no signed mode. The
program counter advances by **1 per instruction**, not 4 (we are not
RISC-V; instructions are not byte-encoded).

## 4. Program ROM

The program ROM is a list of instructions stored at addresses `0..N-1`.
At each address it holds a 4-tuple `(opcode, op_a, op_b, op_c)` where
each field is a field element.

The program ROM is committed once and treated as a public part of the
proof. The fetch-from-ROM constraint (§9) ensures the prover cannot
fabricate instructions.

## 5. Instruction encoding

Every instruction is a fixed 4-tuple of field elements:

```
(opcode, op_a, op_b, op_c)
```

`opcode` is a small integer in `1..=11`. Each operand is either a
register index (`0..=7`) or an immediate field element, depending on the
instruction; unused operands are 0. There is **no bit decomposition of
the instruction word**. Each field is independently a column.

## 6. Instruction set

Eleven instructions. `rd`/`ra`/`rb` denote register indices.

| # | Mnemonic | op_a | op_b | op_c | Effect |
|---|----------|------|------|------|--------|
| 1 | `ADD`   | `rd` | `ra` | `rb` | `r[rd] = r[ra] + r[rb]` |
| 2 | `SUB`   | `rd` | `ra` | `rb` | `r[rd] = r[ra] - r[rb]` |
| 3 | `MUL`   | `rd` | `ra` | `rb` | `r[rd] = r[ra] * r[rb]` |
| 4 | `IMM`   | `rd` | `k`  |  -   | `r[rd] = k` |
| 5 | `LOAD`  | `rd` | `ra` |  -   | `r[rd] = mem[r[ra]]` |
| 6 | `STORE` | `ra` | `rb` |  -   | `mem[r[ra]] = r[rb]` |
| 7 | `JMP`   | `k`  |  -   |  -   | `pc = k` |
| 8 | `JZ`    | `ra` | `k`  |  -   | if `r[ra] == 0` then `pc = k`, else `pc = pc + 1` |
| 9 | `READ`  | `rd` |  -   |  -   | `r[rd] = input[i_in]; i_in += 1` |
| 10 | `WRITE` | `ra` |  -   |  -   | `output[i_out] = r[ra]; i_out += 1` |
| 11 | `HALT` |  -   |  -   |  -   | set halt flag |

Notes:

- All non-jump, non-halt instructions advance `pc` by 1.
- Writes targeting `r0` are silently ignored (so `ADD r0, r1, r2` is a
  legal-but-useless way to discard a result; same convention as RISC-V).
- `LOAD` from an address never written returns 0.
- `JZ` uses zero/non-zero as the only branch condition. To compare two
  values, subtract them and `JZ` on the difference.

## 7. Per-instruction notes

- `ADD/SUB/MUL` are field arithmetic. No carry, no overflow.
- `IMM` lets the program load any field element into a register. Useful
  for constants and addresses.
- `LOAD/STORE` use the value of `r[ra]` as the address. There is no
  immediate-offset addressing mode; build the address with `IMM` + `ADD`
  if needed.
- `JMP` and `JZ` use **absolute** PC targets. Relative jumps would need
  PC arithmetic, which would mean range-checking PC. Absolute targets
  keep the constraint trivial.
- `READ` consumes one element from the public input tape per call;
  reading past the end is a runtime error (caught by the input-binding
  permutation argument failing to balance).
- `HALT` sets the halt flag. After the halt row, the trace is padded
  with rows that have `HALT` semantics so the constraint at the last row
  always sees `halt_flag = 1`.

## 8. Halt protocol

- The trace's first row has `pc = entry_pc` (boundary constraint).
- The trace's last row has `halt_flag = 1` (boundary constraint).
- The `halt_flag` transitions monotonically: once 1, always 1. Only a
  `HALT` instruction can flip it from 0 to 1.
- A program that runs off the end of the program ROM without `HALT`-ing
  cannot produce a valid trace because the fetch lookup would fail.

## 9. Public I/O binding

Public inputs and outputs are bound via permutation arguments tied to
publicly-committed sequences (the same idea as OpenVM's User IO address
space, simplified for our setting):

- **Inputs.** The proof commits to a vector `public_inputs: Vec<F>` of
  length `N_in`. The AIR has columns `(i_in_curr, input_val)`. Every
  `READ` row contributes `(i_in_curr, input_val)` to a "consumed
  inputs" multiset; the verifier supplies the canonical multiset
  `{ (j, public_inputs[j]) | j in 0..N_in }`. The two multisets must
  match. `i_in` increments by 1 on every `READ` row and stays the same
  on others.
- **Outputs.** Symmetric. The proof exposes `public_outputs: Vec<F>` of
  length `N_out`. Every `WRITE` row contributes
  `(i_out_curr, output_val)` to a "produced outputs" multiset; the
  verifier supplies `{ (j, public_outputs[j]) | j in 0..N_out }`.

Both arguments use a single (γ, α) channel for now (~2⁻³⁰ soundness).
We can upgrade to 4 channels later without changing the layout.

## 10. Padding

The trace length is padded to the next power of two with synthetic
`HALT` rows. Padding rows have:

- `pc` equal to the post-halt PC of the real last row,
- all transition constraints satisfied by setting register reads/writes
  to be no-ops,
- `halt_flag = 1`,
- `READ`/`WRITE` selectors zero, so no contribution to the I/O
  permutation arguments.

## 11. Asm syntax (assembler input)

One instruction per line. Comments start with `;`. Labels end with `:`.

```
    IMM r1, 0           ; a = 0
    IMM r2, 1           ; b = 1
    READ r3             ; n = read()
loop:
    JZ r3, done
    ADD r4, r1, r2      ; t = a + b
    ADD r1, r2, r0      ; a = b   (r0 is 0; this is a "MOV")
    ADD r2, r4, r0      ; b = t
    IMM r5, 1
    SUB r3, r3, r5      ; n = n - 1
    JMP loop
done:
    WRITE r1            ; emit a
    HALT
```

`MOV r_d, r_s` is a virtual mnemonic the assembler expands to
`ADD r_d, r_s, r0`. No other pseudo-instructions for now.

## 12. `mini` DSL (very minimal)

`mini` is a flat, assignment-only language that compiles 1:1 to asm. It
exists so guest programs are slightly less painful to write than raw
asm, **without adding any compiler complexity**. Restrictions, on
purpose:

- **No nested expressions.** Each statement is exactly one ALU
  operation, one memory op, one I/O op, or one control-flow op.
- **No types.** Variables are field elements.
- **One variable per register.** The compiler maps variable names to
  registers (max 7 user variables; `r0` is reserved for the constant
  zero). If you run out of registers, you get an error.
- Only these statements:

```
let x = 0;          // constant assignment, compiles to IMM
let x = read();     // compiles to READ
x = y + z;          // ADD; both rhs sides must be variables
x = y - z;          // SUB
x = y * z;          // MUL
x = mem[y];         // LOAD
mem[y] = x;         // STORE
write(x);           // WRITE
if x == 0 { ... }   // JZ + JMP, with optional `else`
while x != 0 { ... }// JZ + JMP loop
halt;               // HALT (also implicit at end of program)
```

That's the whole language. Notably absent: nested expressions
(`x = y + z * w` is **not** legal — the user writes two statements),
function calls, comparisons other than `== 0` and `!= 0`, integer
literals on the rhs of arithmetic (only on `let x = K;` lines).

The compiler is one pass: parse → name-to-register map → emit one asm
instruction per statement (at most a handful for `if`/`while`). Total
expected size: ~200–300 lines of Rust.

Fibonacci in `mini`:

```
let n = read();
let a = 0;
let b = 1;
let one = 1;
while n != 0 {
    let t = a + b;
    a = b + r0;        // pseudo: needs a "copy" form
    b = t + r0;
    n = n - one;
}
write(a);
halt;
```

(The `a = b + r0` lines hint that we may want a `let x = y;` copy form
in `mini` as a 14th rule. Easy to add.)

## 13. Open questions for review

- Does 8 registers feel right, or would 16 be more comfortable (one
  more bit in the register-index range check)? Eight is the minimum for
  fibonacci-style programs.
- Should `JZ` also have a `JNZ` counterpart, or is one direction enough?
  (Currently can do `JNZ ra, k` as `JZ ra, +2; JMP k` if needed.)
- Multiplication: keep it as a primitive (so the AIR has `MUL` as a
  per-row constraint, which is just `r[rd] = r[ra] * r[rb]`)? Or drop
  it and force programs to multiply by repeated addition? Keeping it
  is cheaper; dropping it would shrink the AIR by one constraint and
  one selector but make programs much less expressive. Recommend keep.
- For `mini`, should we add `let x = y;` as a copy form, so users don't
  have to know about `r0`? Recommend yes.

## Constraint-system rough sketch (informational, not normative)

For sanity-checking that this ISA is genuinely small to constrain:

| Component | Approx. columns |
|-----------|-----------------|
| `pc`, `halt_flag` | 2 |
| 11 opcode selectors (one-hot) | 11 |
| 4 instruction fields (`opcode, op_a, op_b, op_c`) | 4 |
| 3 register accesses per row (`rs1`, `rs2`, `rd`) `(idx, val)` | 6 |
| 1 memory access per row `(addr, val, is_write)` | 3 |
| Sorted register table aux | ~6 |
| Sorted memory table aux | ~3 |
| I/O cursors `(i_in, i_out)` | 2 |
| Boundary helpers | ~2 |
| **Total** | **~40 columns** |

vs current zkvm at 226 columns. ~5–6× smaller.

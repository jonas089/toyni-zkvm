# Toyni Auth: a hash-based auth engine

A hash-based authorization engine built on [Toyni](https://github.com/jonas089/toyni).
There is no signature scheme: a user authorizes a message by revealing the
preimage of a hash they committed to earlier, and an aggregator proves a whole
batch of authorizations with a single zero-knowledge STARK.

> [!CAUTION]
> **This is a research project.** It has **not** been audited and is not
> suitable for production use. Do not rely on it for any setting where a
> broken proof would have real-world consequences. The AI-generated review in
> `audit/` is not a substitute for a professional audit.

## Status

- **Toyni (proving backend)**: solid. Core STARK toolkit + CUDA NTT path.
- **Auth engine (this repo)**: one trace row per authorization, Poseidon1 over
  BabyBear as the hash, zero-knowledge proofs. The critical and high findings
  from the AI review in `audit/claude-opus-5.5-max` are fixed.

## Benchmarks

Proving and verifying one batch on an Apple M3 Max (16 cores, CPU only):

| Authorizations | Prove | Verify | Throughput |
|---:|---:|---:|---:|
| 1,024 | 0.09 s | 0.02 s | 11.4k auths/s |
| 8,192 | 0.71 s | 0.05 s | 11.5k auths/s |
| 32,768 | 2.81 s | 0.15 s | 11.6k auths/s |
| 65,536 | 5.80 s | 0.27 s | 11.3k auths/s |

Reproduce with `cargo run --release --bin auth-bench -- <num_auths>`.

## What is proven

For every record `(anchor, m, next, c)` in a batch, the prover knows a secret `x` with `H1(x) == anchor` and
`H2(m, x, next) == c`. The proof is zero-knowledge, so `x` stays hidden from anyone who only sees the proof.

There is no chain yet. `example/` shows how a chain and a sequencer would use these proofs for UTXO payments (with
in-memory placeholders), and its README collects the rules and trust assumptions they need.

`H1(x) = P([x, 0 x 12])[0..4]` and `H2(m, x, next) = P([m, x, next])[0..8]`,
where `P` is Poseidon1 over BabyBear, width 16 (Plonky3's
`default_babybear_poseidon1_16`, checked against its official test vector).

## Layout

`crates/auth-air`:

- `poseidon1.rs`: the permutation. Its round loop is shared by the native
  hash, the witness generator and the constraint evaluator.
- `air.rs`: one trace row per authorization (592 columns, 576 constraints of
  degree <= 3, no transition constraints).
- `prover.rs`, `verifier.rs`: commit trace -> quotient and FRI randomizer ->
  OOD -> DEEP -> FRI -> queries. The verifier binds the public columns to
  records the caller supplies. Witness columns are masked and the FRI input is
  randomized, so proofs are zero-knowledge.
- `bin/auth-bench.rs`: `cargo run --release --bin auth-bench -- <num_auths>`.

`example/`: UTXO payments with an in-memory chain and sequencer, plus their design notes.

`audit/claude-opus-5.5-max`: the AI security review, remediation notes and PoCs.

`cargo test --release` runs the test suite.

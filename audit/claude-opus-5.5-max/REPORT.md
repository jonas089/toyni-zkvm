# Security Audit: toyni-zkvm auth engine (`crates/auth-air`)

| | |
|---|---|
| Auditor | Claude Opus 5.5 (AI model, max reasoning effort) |
| Date | 2026-10-17 |
| Repository | `toyni-zkvm`, HEAD `2d8ac7c` plus the uncommitted working tree (`crates/auth-air` is untracked) |
| Dependency | `toyni` working tree at HEAD `af8683c` plus local changes; audited separately in `toyni/audit/claude-opus-5.5-max/REPORT.md` |
| PoCs | `audit/claude-opus-5.5-max/poc` (standalone crate; `cargo test --release`) |

> This is an AI-generated audit. It is not a substitute for a review by qualified human cryptographers. Every finding marked
> *Confirmed* has an executable proof of concept that passes against the audited code.

## 1. Summary

The engine proves, for a batch of authorization records, that the holder of each `anchor` revealed a preimage `x` and committed to `(m, next)`.
Four issues let an attacker make the verifier accept authorizations nobody made. **Two of them are complete proof forgeries that need no
secret at all.**

| ID | Title | Severity | Status |
|---|---|---|---|
| AUTH-01 | Batches of up to 256 authorizations can be forged without any secret | **Critical** | Confirmed (PoC, 0.1 s) |
| AUTH-02 | Non-canonical OOD values make the constraint check and DEEP disagree: forgery at any batch size | **Critical** | Confirmed (PoC, 3.3 s) |
| AUTH-03 | Records are not range-checked: verified bytes can differ from the authorized message | **High** | Confirmed (PoC) |
| AUTH-04 | Protocol rule lets the aggregator authorize its own message for a user's anchor | **High** | Confirmed (PoC) |
| AUTH-05 | DEEP consistency only on half the domain: soundness margin halved at every size | Medium | Analysis |
| AUTH-06 | Fiat-Shamir does not bind configuration or deployment; prover messages unframed | Low | Analysis |
| AUTH-07 | Verifier can panic on attacker input (debug builds; unbounded `derive_z`) | Low | Confirmed (debug PoC) |
| AUTH-08 | Zero-knowledge is not established | Low | Analysis |
| AUTH-09 | Post-quantum margin of 4-element anchors is ~62 bits | Info | Analysis |
| AUTH-10 | Padding authorization (x = 0) must never be a registered anchor | Info | Analysis |
| AUTH-11 | H1 and H2 are separated only by input layout | Info | Analysis |
| AUTH-12 | Verifier cost is linear in the batch, with one Ext inversion per row per public column | Info | Analysis |

Section 6 lists the properties that were checked and hold.

## 2. Scope

| File | Lines | Role |
|---|---|---|
| `crates/auth-air/src/air.rs` | 165 | Statement, trace layout, constraints |
| `crates/auth-air/src/poseidon1.rs` | 127 | Poseidon1-BabyBear-16 (shared by hashing, witness and constraints) |
| `crates/auth-air/src/constants.rs` | 32 | Round constants and MDS row (Plonky3 `a21e3ed4`) |
| `crates/auth-air/src/prover.rs` | 343 | Prover |
| `crates/auth-air/src/verifier.rs` | 215 | Verifier |
| `crates/auth-air/src/bin/auth-bench.rs` | 45 | Benchmark (not security relevant) |
| `README.md` | — | Protocol description (the chain is not implemented) |

The toyni primitives the engine uses (field, extension, NTT, Merkle, transcript, FRI fold, masking) are covered in the toyni report.
Findings rooted there are cross-referenced (TOYNI-xx).

## 3. Threat model and methodology

**Adversaries.**
- A malicious prover or aggregator that controls every byte of the proof.
- A malicious aggregator that also learns users' secrets `x` (it must, to prove).
- Anyone who can submit records or proofs to the verifying party.

The verifier, the chain state (anchors) and the commitment log are trusted.

**Methodology.**
- **Manual review.** Every line in scope was read, and every verifier check was compared against what a sound DEEP-ALI + FRI verifier must enforce.
- **Malicious provers.** For each suspected break, a malicious prover was written that replays the transcript but chooses its own messages
  (`poc/src/lib.rs`, `Forger`). A finding counts as *Confirmed* only when `auth_air::verifier::verify` returns `true` on a false statement.
- **Vulnerability classes from published audits.**
  - The Least Authority audit of Plonky3 (Nov 2024): verifier trusting proof parameters (Issue A), incomplete Fiat-Shamir (Issues B and C),
    input validity and panics (Issues D–F), and a soundness calculator (Suggestion 4).
  - Weak Fiat-Shamir and "Frozen Heart" (Trail of Bits 2022; Dao, Miller, Wright, Grubbs, IEEE S&P 2023).
  - Under-constrained circuits and non-canonical inputs, the dominant classes in Chaliasos et al., USENIX Security 2024,
    including the 2019 "input aliasing" disclosures for Groth16 verifiers.
  - Zero-knowledge pitfalls in STARKs (Haböck and Al Kindi, ePrint 2024/1037).
  - Soundness accounting per ethSTARK (ePrint 2021/582), DEEP-FRI (ePrint 2019/336) and proximity gaps (ePrint 2020/654).

**Severity.**

| Level | Meaning |
|---|---|
| Critical | The verifier accepts a false statement (forged authorization) with a practical attack |
| High | Forgery or theft under a realistic integration or protocol assumption, or a core security claim is false |
| Medium | Security margin materially below the stated target, or a privacy or availability loss |
| Low | Defense-in-depth gap with no demonstrated exploit |
| Info | Note or recommendation |

## 4. Findings

### AUTH-01: Batches of up to 256 authorizations can be forged without any secret

**Severity: Critical.** Location: `verifier.rs:52-54, 73-98`; `prover.rs:22-32`.

**Description.**
- The verifier samples every query index in `[0, lde/2)` (`verifier.rs:73-74`). It checks the DEEP value against the opened trace and
  quotient only at that index (`verifier.rs:87-94`).
- The paired position `qi + lde/2` is opened from the DEEP layer and used in the first FRI fold (`verifier.rs:96-98`), but is never
  checked against the trace.
- So the DEEP/trace consistency argument only covers the first half `H1` of the LDE domain.
- Every batch of up to 256 authorizations is padded to `trace_len = 256` (`MIN_ROWS`). There, `fri_degree_bound = next_pow2(3(256+268)-256) = 2048 = lde/2 = |H1|`.
- Any function on `H1` has an interpolant of degree below 2048. "The DEEP layer is low-degree and matches the trace on `H1`" therefore
  holds for **any** committed trace. The rate check `lde_size < 2 * d_bound` (`verifier.rs:54`) allows exactly this boundary case.

**Exploit** (`poc/tests/f01_small_batch_forgery.rs`).
1. Commit an all-zero trace and an all-zero quotient.
2. Claim the true interpolants for the 24 public columns at `z`, zero for the witness, and `q(z) = C(z)/Z_H(z)`.
3. The verifier then expects `d(x) = -K/(x - z)` on `H1`. Commit `g(X) = K (V(X)/V(z) - 1)/(X - z)` with `V = Π_{h∈H1}(X - h)`.
   It equals that on `H1`, has degree 2047, and FRI accepts it.

The PoC forges three records with random anchors (no preimage exists in practice) and `verify` returns `true` in 0.08 s.

**Impact.** Anyone can produce a valid batch proof authorizing any message for any anchor, whenever the batch has at most 256 records.

**Recommendation.**
- Check DEEP consistency at both positions of every FRI pair (open the trace and quotient at `qi + lde/2` and recompute `d` there),
  or sample query positions over the whole domain.
- Require `fri_degree_bound <= lde/4`. Alternatively, derive `MIN_ROWS` and `BLOWUP` from a stated target rate instead of from the masking
  budget.
- Add malicious-prover tests, as toyni's `tests/adversarial.rs` does, at the minimum trace size.

### AUTH-02: Non-canonical OOD values make the constraint check and DEEP disagree, forging batches of any size

**Severity: Critical.** Location: `verifier.rs:35-50, 87-94`; root cause TOYNI-02 (`toyni/src/babybear.rs:14-17, 136, 155, 202`).

**Description.**
- `BabyBear` is `pub struct { pub value: u32 }`. The verifier never checks `value < p` on the 593 out-of-domain values it receives.
- `Sub` computes `self.value + PRIME - rhs.value` in u32, which wraps once in release builds when `rhs >= p`.
- Coordinates 1–3 of a trace column's OOD value are subtracted from the opened base-field value, whose coordinates 1–3 are zero
  (`Ext::from(..) - trace_at_z[c]`). If such a coordinate `t` is sent as `t + p`:
  - **DEEP** computes `0 + p - (t + p)`, which wraps to `2^32 - t` and is congruent to `t - Δ` with `Δ = 2^32 mod p = 268435454`.
    DEEP and FRI therefore bind the committed polynomial to `t - Δ`.
  - **The constraint check** computes `(t + p) - b` without wrapping, so it evaluates the constraints at `t`.
- The two checks now disagree by `Δ` on any coordinate the prover chooses.
- Each `a = v^3` S-box cell appears in exactly two constraints, and in no S-box input. Shifting `a` by `δ` changes the combined constraint
  by `w_{2s} δ - w_{2s+1} δ² v_s`, independently of other cells.
- Choosing the shifts is therefore a subset-sum problem in `F_p^4`, with 3 bits per cell over 282 cells against a 124-bit target.

**Exploit** (`poc/tests/f02_noncanonical_ood_forgery.rs`).
1. Commit the true public columns, an all-zero witness and a zero quotient.
2. Compute `D = C(τ) ≠ 0`.
3. Solve `Σ shift-effects = -D` with Wagner's k-tree (32 lists of 2²¹, about 2²⁶ work; `poc/src/ktree.rs`).
4. Send the chosen coordinates as `Δ + p`.

The verifier's constraint check then sees `C = 0 = q(z) Z_H(z)`, while DEEP sees the honest committed polynomials. The PoC forges
**300 random records** at `trace_len = 512`, where AUTH-01 does not apply. It runs in 3.3 s with 3.1 GB of memory.

**Precondition.** The proof must reach `verify` without range checks. That is the case for the current API (pub fields, no decoder) and for
any decoder that maps 4 bytes straight to `value`. A decoder built on `BabyBear::from_bytes` reduces modulo `p` and would block this path.
In debug builds the same proof makes the verifier panic instead (`noncanonical_ood_value_panics_debug_verifier`).

**Recommendation.**
- Reject every field element with `value >= p` at the trust boundary. That covers `trace_at_z`, `q_z`, opened row values, quotient, DEEP
  and FRI openings, and the final layer.
- Provide a canonical decoder that returns an error rather than reducing.
- In toyni (TOYNI-02), make the field private and make the arithmetic total, so out-of-range inputs cannot reach the verifier.

### AUTH-03: Records are not range-checked, so verified bytes can differ from the authorized message

**Severity: High.** Location: `verifier.rs:17-41`; `air.rs:21-37`; `prover.rs:72-81`.

**Description.**
- The verifier accepts `AuthRecord`s whose elements are `>= p`.
- The public-column interpolation reduces them (`*v * w` is a multiplication), so the proof binds the field element the user authorized.
- The transcript, however, absorbs the raw bytes, and the caller keeps the raw record.
- An aggregator can therefore submit `m[0] = v + p` for a user who authorized `m[0] = v`. It builds the proof over the canonical witness
  and a transcript of the non-canonical record. `verify` accepts it, and it rejects the canonical record against the same proof.
- This is the "input aliasing" class from the 2019 Groth16 verifier disclosures.

**Exploit** (`poc/tests/f03_noncanonical_record_aliasing.rs`). The user authorizes `amount = 5`. The verified record says
`2013265926`.

**Impact.** Any consumer that reads `.value` (amounts, addresses, nonces), including the "process verified messages" design, executes a
message the user did not authorize.

**Recommendation.** Reject non-canonical records in `verify` and have it return the canonical records it verified. Consumers must only act on
that returned data.

### AUTH-04: The protocol rule lets the aggregator authorize its own message for a user's anchor

**Severity: High** (protocol design). Location: `README.md`, "prove" step.

**Description.**
- The README requires only that "the chain checks each `c` was logged before the batch".
- To prove, the aggregator must learn `x`. It can then log its own `c' = H2(m', x, next')` and prove `(anchor, m', next', c')`.
- That proof is valid, and `c'` was logged before the batch.
- Commitments are hiding and do not name their anchor. The chain cannot tell `c'` was logged *after* `x` was revealed, which is exactly
  the ordering the Guy Fawkes protocol (Anderson et al., 1998) depends on.

**Exploit** (`poc/tests/f04_aggregator_substitution.rs`). The aggregator authorizes its own message and its own next anchor, so it also
takes over the user's account.

**Recommendation.**
- A commit transaction must name its anchor, i.e. log `(anchor, c)`.
- For each anchor, the chain accepts only the **first** commitment logged while that anchor is current.
- A batch record must reference that commitment.
- Also enforce:
  - at most one record per anchor per batch;
  - anchor uniqueness across users;
  - rejection of the padding anchor (AUTH-10);
  - a chain or contract identifier inside `H2`'s input, so commitments cannot be replayed across deployments.

### AUTH-05: DEEP consistency only on half the domain halves the soundness margin at every size

**Severity: Medium.** Location: `verifier.rs:73-98`; `prover.rs:16-28`.

**Description.**
- For `trace_len >= 512` the FRI rate is 1/4. Because of the restriction in AUTH-01, the DEEP and trace argument effectively runs at
  rate 1/2 on `H1`.
- Rough estimates for 132 queries with no grinding, in bits (Appendix A):

  | | Conjectured | Proven (Johnson) |
  |---|---|---|
  | As implemented | ≈ 132 | ≈ 66 |
  | Fixed (both pair points checked) | capped by the 124-bit field | ≈ 132 |

- There is no soundness calculation in the code. Least Authority made the same recommendation to Plonky3 (Suggestion 4).

**Recommendation.** Fix AUTH-01. Compute and document conjectured and proven security per parameter set, and add grinding or queries if the
target is at least 100 proven bits.

### AUTH-06: Fiat-Shamir does not bind configuration or deployment, and prover messages are unframed

**Severity: Low.** Location: `prover.rs:72-81`; `verifier.rs:28-36`.

**Description.**
- The statement absorbs a label, the counts and the records. It does not absorb `BLOWUP`, `NUM_QUERIES`, `MASK_DEGREE`, field or hash
  identifiers, or a deployment identifier.
- Prover messages are concatenated without length or type framing.
- `trace_commitment`, `quotient_commitment` and `fri_commitments` are not length-checked. toyni's own verifier requires 32 bytes. A wrong
  length currently fails later at Merkle verification, so this is hygiene rather than an exploit.

These are Least Authority's Plonky3 Issue B and Suggestion 5 (domain separators), and Dao et al. (S&P 2023).

**Recommendation.** Absorb a versioned configuration digest and a deployment ID first, frame every absorbed message with its type and length,
and reject commitments that are not 32 bytes.

### AUTH-07: The verifier can panic on attacker input

**Severity: Low.**
- **Debug builds.** The AUTH-02 encoding overflows `u32` and panics (PoC: `noncanonical_ood_value_panics_debug_verifier`).
- **`derive_z`** (`prover.rs:105-112`, also used by the verifier) loops without bound. toyni's verifier caps it at 64 tries.
  Reaching the loop needs a negligible-probability transcript, but the pattern should match.

**Recommendation.** `verify` should never panic. Validate input first, use checked arithmetic, and bound every loop
(Least Authority Plonky3 Issues E and F).

### AUTH-08: Zero-knowledge is not established

**Severity: Low.**
- The witness columns are masked with `MASK_DEGREE = 2·132 + 4` coefficients. The quotient is not masked, and FRI has no randomizer
  polynomial.
- The budget counts trace openings, but the DEEP pair value at `qi + lde/2` and all FRI layer values are further functions of the masked
  columns.
- The linear witness-recovery attack that breaks toyni's example (TOYNI-05) does not carry over directly:
  - the quotient here is cubic in the trace values,
  - each column's 268 masking coefficients exceed its 133 direct openings.
- No zero-knowledge argument exists either (see Haböck and Al Kindi, ePrint 2024/1037). The practical exposure is limited, since the
  aggregator learns `x` anyway. The main risk is leaking `x` for authorizations the chain has not yet processed.

**Recommendation.** If zero-knowledge is a goal, randomize the DEEP/FRI input, budget masking for every revealed functional, and document
the claim.

### AUTH-09: The post-quantum margin of 4-element anchors is about 62 bits

**Severity: Info.**

| Value | Classical | Quantum |
|---|---|---|
| `H1` output (anchor, 4 elements ≈ 123.6 bits) | 123.6-bit preimage resistance | ≈ 62-bit preimage resistance (Grover) |
| `H2` output (`c`, 8 elements ≈ 247 bits) | ≈ 124-bit collision resistance | ≈ 82-bit collision resistance (BHT) |

If post-quantum security is a goal, use 8-element anchors and secrets.

### AUTH-10: The padding authorization (x = 0) must never be a registered anchor

**Severity: Info.** Location: `air.rs:63-70`.

Padding rows prove `H1(0) = anchor_pad`. Anyone can authorize anything for the anchor `H1(0)`, so the chain must refuse to register it.

### AUTH-11: H1 and H2 are separated only by input layout

**Severity: Info.** Location: `air.rs:40-61`.

Both use the same permutation with different input shapes (zero-padded versus full), and no domain tag. No attack was found. Explicit
domain separation (a tag in a capacity lane, or distinct constants) is cheap.

### AUTH-12: Verifier cost is linear in the batch

**Severity: Info.** Location: `verifier.rs:38-41, 131-139`.

The verifier rebuilds 24 public columns and inverts one Ext element per row per column. Use batch inversion, or bind records through a
commitment if verification cost matters.

## 5. Proof-of-concept index

| Finding | Test | Runtime (M3 Max, release) |
|---|---|---|
| AUTH-01 | `tests/f01_small_batch_forgery.rs` | 0.1 s |
| AUTH-02 | `tests/f02_noncanonical_ood_forgery.rs` (release only; about 3 GB RAM) | 3.3 s |
| AUTH-02 / AUTH-07 | `noncanonical_ood_value_panics_debug_verifier` (debug only) | instant |
| AUTH-03 | `tests/f03_noncanonical_record_aliasing.rs` | 0.3 s |
| AUTH-04 | `tests/f04_aggregator_substitution.rs` | 0.1 s |

```
cd audit/claude-opus-5.5-max/poc && cargo test --release
```

## 6. Properties checked that hold

- **Statement completeness.** Every one of the 592 columns is constrained. A single-cell change to an honest row violates a constraint for
  every column (existing test `any_tampered_cell_violates_a_constraint`). The S-box decomposition `a = v^3`, `y = a^2 v` is correct, and
  `x` is shared between `H1` and `H2`.
- **Poseidon1 parameters.** The 336 round constants and the MDS row come by script from Plonky3 `a21e3ed4`. The permutation matches the
  official vector `test_poseidon_width_16` and Plonky3 on 200 random inputs.
- **Transcript order.** Statement, trace root, `alpha`, quotient root, `z` (outside the base field), OOD values, DEEP coefficients, FRI
  roots and betas, then queries. The final FRI layer is bound through its root, so Least Authority's Plonky3 Issue C does not apply.
- **`trace_len` comes from the records,** not from the proof (contrast with TOYNI-01).
- **Merkle openings** are bound to verifier-derived indices, with pinned depth and leaf/node domain separation.
- **Domain arithmetic.** The `2^27`-th root of unity is primitive, the coset shift 7 is outside every `2^k` subgroup (so the coset avoids
  `H`), `X^4 - 11` is irreducible (11 is a non-residue), and `z` outside the base field implies `Z_H(z) ≠ 0`.

## 7. Re-audit after remediation (2026-10-17)

**Scope.** Critical and High only: any way for `verify` to accept a false statement, or to bypass authorization. The code is
the audited code plus the patches in `REMEDIATION.md` (AUTH-01, AUTH-02, AUTH-03, AUTH-05, AUTH-08).

**Result: no new Critical or High findings.**

| ID | Severity | Status |
|---|---|---|
| AUTH-01 | Critical | Fixed (f01 rejected) |
| AUTH-02 | Critical | Fixed (f02 rejected) |
| AUTH-03 | High | Fixed (f03 rejected) |
| AUTH-04 | High | **Open.** The README rule ("the chain checks each `c` was logged before the batch") still allows the substitution. A chain built on it must accept, per anchor, only the first commitment logged by the anchor's owner (Section 4). |
| AUTH-05 | Medium | Fixed (queries sampled over the whole domain) |
| AUTH-08 | Low | Fixed (zero-knowledge: trace masks plus an FRI randomizer) |

**Method.**
- The verifier path was reviewed line by line, then independently a second time:
  - transcript order;
  - Merkle verification;
  - FRI, including the new whole-domain index and fold logic;
  - DEEP terms and AIR completeness;
  - public-input binding;
  - field and extension arithmetic;
  - challenge sampling.
- PoCs f01–f04 were re-run; f01–f03 are rejected.
- Additional tests ran in a scratch copy (not kept in the repo):
  - 2,063 single-field mutations of an honest proof, covering every proof field, were all rejected;
  - a proof over an invalid row, with a lie about `q(z)` that passes the OOD check, was rejected;
  - swapped or reused layer-0 openings were rejected for queries in both halves;
  - the rate-1/2 forgery from AUTH-01 was rejected by whole-domain sampling alone.
- The zero-knowledge change (AUTH-08) was checked on its own:
  - the randomizer is committed before the DEEP coefficients and checked at every query;
  - changing its opening or commitment is rejected;
  - an honest proof built through the PoC forger still verifies, and f01–f03 are still rejected.

## Appendix A: Soundness estimates

These are rough, using `bits ≈ q·log2(1/ρ)` for conjectured and `q·½·log2(1/ρ)` for proven (Johnson regime), ignoring field-size and
list-size terms.

| Configuration | ρ for the DEEP/trace argument | Conjectured | Proven |
|---|---|---|---|
| `trace_len = 256` (batches ≤ 256) | 1 | **0** | **0** |
| `trace_len ≥ 512`, as implemented | 1/2 | ≈ 132 | ≈ 66 |
| `trace_len ≥ 512`, both pair points checked | 1/4 | capped by field (~124) | ≈ 132 |

## References

1. Least Authority, *Plonky3 Security Audit Report* (Polygon), 7 Nov 2024. Issues A–G, Suggestions 1–6.
2. Q. Dao, J. Miller, O. Wright, P. Grubbs, *Weak Fiat-Shamir Attacks on Modern Proof Systems*, IEEE S&P 2023, ePrint 2023/691.
3. Trail of Bits, *Frozen Heart* coordinated disclosures (weak Fiat-Shamir in PlonK, Bulletproofs, Girault), 2022.
4. S. Chaliasos et al., *SoK: What Don't We Know? Understanding Security Vulnerabilities in SNARKs*, USENIX Security 2024, arXiv 2402.15293.
5. U. Haböck, Al Kindi, *A note on adding zero-knowledge to STARKs*, ePrint 2024/1037.
6. StarkWare, *ethSTARK Documentation*, ePrint 2021/582.
7. E. Ben-Sasson, L. Goldberg, S. Kopparty, S. Saraf, *DEEP-FRI*, ePrint 2019/336.
8. E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon Codes*, ePrint 2020/654.
9. R. Anderson, F. Bergadano, B. Crispo, J.-H. Lee, C. Manifavas, R. Needham, *A New Family of Authentication Protocols* (Guy Fawkes), ACM SIGOPS OSR 1998.
10. "Input aliasing" disclosures for snarkjs / ZoKrates / ethsnarks Groth16 verifiers (public inputs not reduced modulo the scalar field), 2019.
11. L. Grassi et al., *Poseidon*, USENIX Security 2021, ePrint 2019/458. C. Bouvier et al., *SoK: Zero-Knowledge Friendly Hash Functions over Prime Fields*, ePrint 2026/1931.

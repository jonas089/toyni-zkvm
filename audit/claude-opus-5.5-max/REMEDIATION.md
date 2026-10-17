# Remediation: auth engine

Date: 2026-10-17. Goal: close the forgery paths (AUTH-01, AUTH-02, AUTH-03) with the smallest change to the pre-audit code.
AUTH-05 was fixed afterwards because its fix is equally small, and AUTH-08 (zero-knowledge) on request. Apart from the two
proof fields AUTH-08 adds, the proof format, the AIR and the `verify` signature are unchanged.

## Patches

### AUTH-01: every batch is padded to at least 512 rows (FRI rate 1/4)

`crates/auth-air/src/prover.rs`
```diff
-/// Below this the masked degree bound leaves no FRI rate.
-pub const MIN_ROWS: usize = 256;
+/// Smallest trace with FRI rate <= 1/4; at 256 the rate is 1/2 and forgeable (AUTH-01).
+pub const MIN_ROWS: usize = 512;
@@ fn prove
-    assert!(lde_size >= 2 * fri_degree_bound(trace_len), "FRI rate must be <= 1/2");
+    assert!(lde_size >= 4 * fri_degree_bound(trace_len), "FRI rate must be <= 1/4");
```

`crates/auth-air/src/verifier.rs`
```diff
-    if lde_size < 2 * d_bound { return false; }
+    if lde_size < 4 * d_bound { return false; }
```

At rate 1/4, an interpolant through the queried half has degree up to `lde/2 - 1 = 2·d_bound - 1`. That exceeds the FRI bound, so
the forgery fails. Batches of up to 256 authorizations now cost a 512-row proof. Larger batches are unchanged.

### AUTH-02 and AUTH-03: `verify` rejects field elements >= p

`crates/auth-air/src/verifier.rs`
```diff
-use toyni::babybear::BabyBear;
+use toyni::babybear::{BabyBear, BABYBEAR_PRIME};
@@ fn verify
     if proof.trace_at_z.len() != NUM_COLS { return false; }
+    if !canonical(proof, records) { return false; }
@@
+/// Every field element must be < p: the u32 arithmetic and `==` are wrong otherwise (AUTH-02, AUTH-03).
+fn canonical(proof: &AuthProof, records: &[AuthRecord]) -> bool {
+    let ok = |v: &BabyBear| v.value < BABYBEAR_PRIME;
+    let ext_ok = |e: &Ext| e.c.iter().all(ok);
+    records.iter().all(|r| r.public_values().iter().all(ok))
+        && proof.trace_at_z.iter().all(ext_ok)
+        && ext_ok(&proof.q_z)
+        && proof.fri_final_layer.iter().all(ext_ok)
+        && proof.query_proofs.iter().all(|qp| {
+            qp.trace_opening.values.iter().all(ok)
+                && [&qp.quotient_opening, &qp.deep_opening, &qp.deep_opening_pair].iter().all(|o| ext_ok(&o.value))
+                && qp.fri_openings.iter().all(|(a, b)| ext_ok(&a.value) && ext_ok(&b.value))
+        })
+}
```

The check covers every field element the verifier reads:
- the records,
- `trace_at_z` and `q_z`,
- the opened row, quotient, DEEP and FRI values,
- the final layer.

It runs before any arithmetic, which also closes the debug-build panic path from AUTH-07. `BabyBear` itself is unchanged
(TOYNI-02), so any other consumer of toyni needs the same check at its trust boundary.

### AUTH-05: queries are sampled over the whole LDE domain

`crates/auth-air/src/prover.rs` and `crates/auth-air/src/verifier.rs`
```diff
-    let query_indices = transcript.squeeze_indices(NUM_QUERIES, half0);
+    let query_indices = transcript.squeeze_indices(NUM_QUERIES, lde_size);
@@ fn prove
-                deep_opening_pair: open_scalar(&fri_trees[0], &fri_layers[0], qi + half0),
+                deep_opening_pair: open_scalar(&fri_trees[0], &fri_layers[0], qi ^ half0),
@@ fn verify
-        if !verify_scalar(&qp.deep_opening_pair, &proof.fri_commitments[0], qi + half0, lde_size) { return false; }
+        if !verify_scalar(&qp.deep_opening_pair, &proof.fri_commitments[0], qi ^ half0, lde_size) { return false; }
-        let (a0, b0) = (qp.deep_opening.value, qp.deep_opening_pair.value);
+        // qi ranges over the whole domain; fold with (a0, b0) at (lo0, lo0 + lde/2).
+        let lo0 = qi % half0;
+        let (a0, b0) = if qi == lo0 {
+            (qp.deep_opening.value, qp.deep_opening_pair.value)
+        } else {
+            (qp.deep_opening_pair.value, qp.deep_opening.value)
+        };
         let mut folded = (a0 + b0).mul_base(half_inv)
-            + (a0 - b0).mul_base(half_inv) * fri_betas[0] * Ext::from(shifted_elements[qi].inverse());
-        let mut pos = qi;
+            + (a0 - b0).mul_base(half_inv) * fri_betas[0] * Ext::from(shifted_elements[lo0].inverse());
+        let mut pos = lo0;
```

The DEEP check now covers the whole domain at rate 1/4. That gives about 132 bits under the proven bound; the conjectured bound is
capped by the field size (REPORT, Appendix A). Proof format, proof size and prover cost are unchanged. The PoC forger in
`poc/src/lib.rs` samples the same way.

### AUTH-08: proofs are zero-knowledge (FRI randomizer)

The prover commits a uniformly random Ext polynomial `R` of degree below the FRI bound, right after the quotient (before
`z` and the DEEP coefficients), and adds `c_r·R` to the DEEP layer. The verifier opens `R` at each query and adds
`c_r·R(x)` to the DEEP value it expects.

`crates/auth-air/src/prover.rs`
```diff
+    pub randomizer_opening: ScalarOpening,    // QueryProof
+    pub randomizer_commitment: Vec<u8>,       // AuthProof
@@ fn prove
     transcript.absorb_commitment(&quotient_commitment);
+    // R = four random base polynomials of degree < fri_degree_bound, one per Ext limb;
+    // coset LDE, Merkle tree, root absorbed.
+    transcript.absorb_commitment(&randomizer_commitment);
-    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 1).map(|_| transcript.squeeze_ext_challenge()).collect();
+    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 2).map(|_| transcript.squeeze_ext_challenge()).collect();
+    let c_r = deep_coeffs[NUM_COLS + 1];
-            *a = *a * (Ext::from(shifted_elements[start + j]) - z).inverse();
+            *a = *a * (Ext::from(shifted_elements[start + j]) - z).inverse() + c_r * r_evals[start + j];
+                randomizer_opening: open_scalar(&r_tree, &r_evals, qi),
```

`crates/auth-air/src/verifier.rs`
```diff
     transcript.absorb_commitment(&proof.quotient_commitment);
+    transcript.absorb_commitment(&proof.randomizer_commitment);
-    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 1).map(|_| transcript.squeeze_ext_challenge()).collect();
+    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 2).map(|_| transcript.squeeze_ext_challenge()).collect();
+        if !verify_scalar(&qp.randomizer_opening, &proof.randomizer_commitment, qi, lde_size) { return false; }
+        expected = expected + deep_coeffs[NUM_COLS + 1] * qp.randomizer_opening.value;
```
The `canonical()` check also covers `randomizer_opening`.

Why the proof reveals nothing about the witness:
- **Witness columns** carry 268 random mask coefficients (`T + Z_H·R_i`). A proof reveals each column at the 132 query rows
  and at `z`, which is 136 linear functions of the mask. That is fewer than 268, so the revealed values are uniformly random.
- **The quotient** is one row's constraints divided by `Z_H(x)`, so its revealed values follow from rows already revealed.
- **The DEEP and FRI layers** commit to `D + c_r·R`. `R` is uniform and committed before `c_r` is drawn, so this polynomial is
  uniformly random and independent of the witness. Each `R(x_qi)` is fixed by the opened values. Everything FRI reveals can be
  simulated by folding a random polynomial.
- **Unopened Merkle leaves** keep fresh mask or randomizer entropy, so their hashes reveal nothing in the random-oracle model.

This is the standard construction (Haböck and Al Kindi, ePrint 2024/1037): mask the trace for every revealed point, and
randomize the FRI input with a polynomial committed before the batching challenge.

Soundness is unchanged. `R` is committed before the DEEP coefficients and checked at every query like any other batched
polynomial.

Cost: one more Ext LDE and Merkle tree, and one opening per query. At 32,768 authorizations proving goes from about 2.6 s to
2.81 s (about 11.6k auths/s). Most of the extra 265 ms is the sequential Merkle tree.

The PoC forger commits a zero `R`, which a malicious prover is free to do.

## Status

| ID | Severity | Status |
|---|---|---|
| AUTH-01 | Critical | Fixed |
| AUTH-02 | Critical | Fixed |
| AUTH-03 | High | Fixed |
| AUTH-05 | Medium | Fixed |
| AUTH-06 | Low | Open |
| AUTH-07 | Low | Partly fixed: the non-canonical panic path is closed; `derive_z` is still unbounded |
| AUTH-08 | Low | Fixed |
| AUTH-09 – AUTH-12 | Info | Open |

## Re-audit

The PoCs were run against the pre-audit code and against the patched code (`cd poc && cargo test --release`).

| PoC | Pre-audit code | Patched |
|---|---|---|
| f01: small-batch forgery | verifies | rejected |
| f02: non-canonical OOD forgery, 300 records | verifies | rejected |
| f03: non-canonical record aliasing | verifies | rejected |

f01–f03 now assert rejection. Each attack exercises exactly one patch, and each succeeded against the code without it.
In a scratch copy with the AUTH-01 patch removed, the AUTH-05 change alone still rejects f01's rate-1/2 forgery, so the two
patches are independent layers of defense. The crate's own tests pass (7); `tampered_proofs_fail` also covers the
randomizer opening and commitment.

After the AUTH-08 change, an honest proof built through the PoC forger still verifies, so f01–f03 are rejected for the
intended reasons.

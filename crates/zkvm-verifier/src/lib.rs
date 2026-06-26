//! Verifier for the small custom VM.
//!
//! Replays Fiat-Shamir, checks the OOD constraint quotient, Lagrange-binds
//! the program ROM / public input / public output tables, and verifies FRI
//! query openings.
//!
//! The trace is committed over the base field, but all random challenges and
//! the values derived from them (accumulators, quotient, DEEP, FRI) live in the
//! quartic extension `Ext`, matching the prover. Base trace openings are lifted
//! into `Ext` when re-deriving the constraint / DEEP values.

use sha2::{Digest, Sha256};
use toyni::babybear::BabyBear;
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::math::polynomial::Polynomial;
use toyni::merkle::{verify_merkle_proof, MerkleTree};
use toyni::transcript::FiatShamirTranscript;

use zkvm_air::{
    eval_transition_constraints, num_transition_constraints, permutation, TraceView,
};
use zkvm_core::{accum, col, NUM_ACCUM_COLS, NUM_CHANNELS, NUM_TRACE_COLS};

use zkvm_prover::{
    MerkleOpening, MerkleOpeningExt, ScalarOpening, ZkvmProof, BLOWUP, COMPOSITION_DEGREE,
    COSET_SHIFT, NUM_QUERIES,
};

pub struct ZkvmVerifier;

impl ZkvmVerifier {
    /// Verify a proof against the program and entry point the caller expects.
    ///
    /// `expected_program_hash` must be `hash_program(..)` of the program the
    /// caller authored, and `expected_entry_pc` the entry point they intended.
    /// Both `proof.program_hash` and `proof.entry_pc` are prover-supplied, so
    /// without these checks a passing proof only certifies that *some*
    /// self-consistent program ran — not that it was *your* program. Pinning
    /// them here is what makes the proof bind to a specific program.
    pub fn verify(
        &self,
        proof: &ZkvmProof,
        expected_program_hash: &[u8; 32],
        expected_entry_pc: u32,
    ) -> bool {
        // Pin the proof to the caller's program / entry point before doing any
        // further (expensive) work.
        if &proof.program_hash != expected_program_hash { return false; }
        if proof.entry_pc != expected_entry_pc { return false; }

        let trace_len = proof.trace_len;
        let lde_size = proof.lde_size;
        let num_cols = proof.num_cols;
        let num_accum_cols = proof.num_accum_cols;

        if lde_size != trace_len * BLOWUP { return false; }
        if num_cols != NUM_TRACE_COLS { return false; }
        if num_accum_cols != NUM_ACCUM_COLS { return false; }
        if proof.trace_at_z.len() != num_cols || proof.trace_at_gz.len() != num_cols { return false; }
        if proof.accum_at_z.len() != num_accum_cols || proof.accum_at_gz.len() != num_accum_cols { return false; }

        let domain = BabyBearDomain::new(trace_len);
        let extended_domain = BabyBearDomain::new(lde_size);
        let shift = BabyBear::new(COSET_SHIFT);
        let shifted_domain = extended_domain.get_coset(shift);
        let g = domain.group_gen();
        let z_poly = Polynomial::new(domain.vanishing_poly_coeffs());

        // ── 1. Replay Fiat-Shamir ────────────────────────────────────
        let mut transcript = FiatShamirTranscript::new();
        transcript.absorb_commitment(&proof.program_hash);
        transcript.absorb_field(BabyBear::from_u32(proof.entry_pc));
        for &v in &proof.public_inputs { transcript.absorb_field(BabyBear::from_u32(v)); }
        for &v in &proof.public_outputs { transcript.absorb_field(BabyBear::from_u32(v)); }
        transcript.absorb_field(BabyBear::from_u32(proof.public_inputs.len() as u32));
        transcript.absorb_field(BabyBear::from_u32(proof.public_outputs.len() as u32));
        transcript.absorb_commitment(&proof.trace_commitment);

        let gammas: [Ext; 4] = [
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
        ];
        let alphas: [Ext; 4] = [
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
        ];
        if gammas != proof.gammas || alphas != proof.alphas { return false; }

        transcript.absorb_commitment(&proof.accum_commitment);

        let num_main = num_transition_constraints();
        let num_accum = permutation::num_accum_constraints();
        let total_constraints = num_main + num_accum;
        let num_b_first = 5 + 5 * NUM_CHANNELS + 2;
        let num_b_last = 1;
        let total_with_boundary = total_constraints + num_b_first + num_b_last;

        let cweights: Vec<Ext> = (0..total_with_boundary)
            .map(|_| transcript.squeeze_ext_challenge())
            .collect();

        transcript.absorb_commitment(&proof.quotient_commitment);

        let z = derive_z_verifier(&mut transcript);

        for &v in &proof.trace_at_z { transcript.absorb_ext(v); }
        for &v in &proof.trace_at_gz { transcript.absorb_ext(v); }
        for &v in &proof.accum_at_z { transcript.absorb_ext(v); }
        for &v in &proof.accum_at_gz { transcript.absorb_ext(v); }
        transcript.absorb_ext(proof.q_z);

        // ── 2. OOD constraint quotient consistency ───────────────────
        let omega_nm1 = Ext::from(g.pow((trace_len - 1) as u64));
        let one = Ext::one();
        let entry_pc_f = Ext::from_u32(proof.entry_pc);

        let curr_z = TraceView { vals: proof.trace_at_z.clone() };
        let next_gz = TraceView { vals: proof.trace_at_gz.clone() };

        let main_cv = eval_transition_constraints(&curr_z, &next_gz);
        let accum_cv = permutation::eval_accum_constraints(
            &curr_z, &next_gz, &proof.accum_at_z, &proof.accum_at_gz, &gammas, &alphas,
        );

        let mut c_excepted = Ext::zero();
        for (j, &v) in main_cv.iter().enumerate() {
            c_excepted = c_excepted + cweights[j] * v;
        }
        let mut c_wrap = Ext::zero();
        for (j, &v) in accum_cv.iter().enumerate() {
            c_wrap = c_wrap + cweights[num_main + j] * v;
        }
        let z_at_z = eval_base_at_ext(z_poly.coefficients(), z);
        let transition_q_z = (c_excepted * (z - omega_nm1) + c_wrap) * z_at_z.inverse();

        let alpha_b = total_constraints;
        let mut b_first_z = Ext::zero();
        b_first_z = b_first_z + cweights[alpha_b]     * proof.trace_at_z[col::CLK];
        b_first_z = b_first_z + cweights[alpha_b + 1] * (proof.trace_at_z[col::PC] - entry_pc_f);
        b_first_z = b_first_z + cweights[alpha_b + 2] * proof.trace_at_z[col::HALT];
        b_first_z = b_first_z + cweights[alpha_b + 3] * proof.trace_at_z[col::I_IN];
        b_first_z = b_first_z + cweights[alpha_b + 4] * proof.trace_at_z[col::I_OUT];
        for ch in 0..NUM_CHANNELS {
            b_first_z = b_first_z + cweights[alpha_b + 5 + ch] * (proof.accum_at_z[accum::REG + ch] - one);
            b_first_z = b_first_z + cweights[alpha_b + 5 + NUM_CHANNELS + ch] * (proof.accum_at_z[accum::MEM + ch] - one);
            b_first_z = b_first_z + cweights[alpha_b + 5 + 2 * NUM_CHANNELS + ch] * proof.accum_at_z[accum::PROG + ch];
            b_first_z = b_first_z + cweights[alpha_b + 5 + 3 * NUM_CHANNELS + ch] * proof.accum_at_z[accum::PUB_IN + ch];
            b_first_z = b_first_z + cweights[alpha_b + 5 + 4 * NUM_CHANNELS + ch] * proof.accum_at_z[accum::PUB_OUT + ch];
        }
        let rom_b = total_constraints + 5 + 5 * NUM_CHANNELS;
        b_first_z = b_first_z + cweights[rom_b] * proof.trace_at_z[col::PROG];
        let smem_init_z = proof.trace_at_z[col::SMEM + 4] * (one - proof.trace_at_z[col::SMEM + 3]) * proof.trace_at_z[col::SMEM + 1];
        b_first_z = b_first_z + cweights[rom_b + 1] * smem_init_z;
        let b_first_qz = b_first_z * (z - one).inverse();

        let alpha_l = total_constraints + num_b_first;
        let b_last_z = cweights[alpha_l] * (proof.trace_at_z[col::HALT] - one);
        let b_last_qz = b_last_z * (z - omega_nm1).inverse();

        let expected_q_z = transition_q_z + b_first_qz + b_last_qz;
        if expected_q_z != proof.q_z { return false; }

        // ── 3. Bind program ROM to claimed program_hash + Lagrange-bind ─
        // Hash the ROM and compare against program_hash.
        let mut hasher = Sha256::new();
        for &(addr, op, a, b, c) in &proof.program_rom {
            hasher.update(addr.to_le_bytes());
            hasher.update(op.to_le_bytes());
            hasher.update(a.to_le_bytes());
            hasher.update(b.to_le_bytes());
            hasher.update(c.to_le_bytes());
        }
        let expected_hash: [u8; 32] = hasher.finalize().into();
        if expected_hash != proof.program_hash { return false; }

        // Reconstruct ROM table columns and Lagrange-evaluate at z.
        let mut prog_addr_v = vec![BabyBear::zero(); trace_len];
        let mut prog_op_v   = vec![BabyBear::zero(); trace_len];
        let mut prog_a_v    = vec![BabyBear::zero(); trace_len];
        let mut prog_b_v    = vec![BabyBear::zero(); trace_len];
        let mut prog_c_v    = vec![BabyBear::zero(); trace_len];
        for (i, &(addr, op, a, b, c)) in proof.program_rom.iter().enumerate() {
            if i >= trace_len { return false; }
            prog_addr_v[i] = BabyBear::from_u32(addr);
            prog_op_v[i]   = BabyBear::from_u32(op);
            prog_a_v[i]    = BabyBear::from_u32(a);
            prog_b_v[i]    = BabyBear::from_u32(b);
            prog_c_v[i]    = BabyBear::from_u32(c);
        }

        // PROG + 6 is the `real` flag: 1 for the genuine ROM rows (a prefix),
        // 0 for padding. Binding it stops the prover from disabling the in-AIR
        // ROM_ENTRY_WELLFORMED / ROM_PC_DISTINCT contiguity constraints.
        let mut prog_real_v = vec![BabyBear::zero(); trace_len];
        for i in 0..proof.program_rom.len().min(trace_len) {
            prog_real_v[i] = BabyBear::one();
        }

        if proof.trace_at_z[col::PROG    ] != lagrange_ext(&prog_addr_v, z, &domain) { return false; }
        if proof.trace_at_z[col::PROG + 1] != lagrange_ext(&prog_op_v,   z, &domain) { return false; }
        if proof.trace_at_z[col::PROG + 2] != lagrange_ext(&prog_a_v,    z, &domain) { return false; }
        if proof.trace_at_z[col::PROG + 3] != lagrange_ext(&prog_b_v,    z, &domain) { return false; }
        if proof.trace_at_z[col::PROG + 4] != lagrange_ext(&prog_c_v,    z, &domain) { return false; }
        if proof.trace_at_z[col::PROG + 6] != lagrange_ext(&prog_real_v, z, &domain) { return false; }
        // PROG + 5 is the multiplicity column; the prover supplies it and the
        // AIR range-checks it non-negative (ROM_MULT_RANGE). The LogUp closure
        // (Z[0] = Z[n] = 0 enforced by boundary) ties multiplicities to the
        // execution side, so we don't bind it directly.

        // ── 4. Bind public input table ───────────────────────────────
        let mut in_addr_v = vec![BabyBear::zero(); trace_len];
        let mut in_val_v  = vec![BabyBear::zero(); trace_len];
        let mut in_mult_v = vec![BabyBear::zero(); trace_len];
        for (j, &v) in proof.public_inputs.iter().enumerate() {
            if j >= trace_len { return false; }
            in_addr_v[j] = BabyBear::from_u32(j as u32);
            in_val_v[j]  = BabyBear::from_u32(v);
            in_mult_v[j] = BabyBear::one();
        }
        if proof.trace_at_z[col::PUB_IN    ] != lagrange_ext(&in_addr_v, z, &domain) { return false; }
        if proof.trace_at_z[col::PUB_IN + 1] != lagrange_ext(&in_val_v,  z, &domain) { return false; }
        if proof.trace_at_z[col::PUB_IN + 2] != lagrange_ext(&in_mult_v, z, &domain) { return false; }

        // ── 5. Bind public output table ──────────────────────────────
        let mut out_addr_v = vec![BabyBear::zero(); trace_len];
        let mut out_val_v  = vec![BabyBear::zero(); trace_len];
        let mut out_mult_v = vec![BabyBear::zero(); trace_len];
        for (j, &v) in proof.public_outputs.iter().enumerate() {
            if j >= trace_len { return false; }
            out_addr_v[j] = BabyBear::from_u32(j as u32);
            out_val_v[j]  = BabyBear::from_u32(v);
            out_mult_v[j] = BabyBear::one();
        }
        if proof.trace_at_z[col::PUB_OUT    ] != lagrange_ext(&out_addr_v, z, &domain) { return false; }
        if proof.trace_at_z[col::PUB_OUT + 1] != lagrange_ext(&out_val_v,  z, &domain) { return false; }
        if proof.trace_at_z[col::PUB_OUT + 2] != lagrange_ext(&out_mult_v, z, &domain) { return false; }

        // ── 6. Squeeze DEEP coefficients ─────────────────────────────
        let num_deep_terms = 2 * num_cols + 2 * num_accum_cols + 1;
        let deep_coeffs: Vec<Ext> = (0..num_deep_terms)
            .map(|_| transcript.squeeze_ext_challenge())
            .collect();

        // ── 7. Replay FRI commitments / betas ────────────────────────
        if proof.fri_commitments.is_empty() { return false; }

        // Fold-to-degree-bound + final-layer low-degree enforcement (mirrors the
        // prover). D_BOUND = COMPOSITION_DEGREE * trace_len bounds deg(D); the
        // committed final layer has size lde/D_BOUND and must be constant. This
        // is the low-degree enforcement (per-query fold-consistency does not test
        // degree).
        let d_bound = COMPOSITION_DEGREE * trace_len;
        if d_bound == 0 || lde_size % d_bound != 0 { eprintln!("DBG: d_bound div"); return false; }
        let final_layer_size = lde_size / d_bound;
        let expected_folds = (lde_size / final_layer_size).trailing_zeros() as usize;
        if proof.fri_commitments.len() != expected_folds + 1 { return false; }
        if proof.fri_final_layer.len() != final_layer_size { return false; }
        if !proof.fri_final_layer.iter().all(|v| *v == proof.fri_final_layer[0]) { return false; }
        if merkle_root_of_ext(&proof.fri_final_layer) != *proof.fri_commitments.last().unwrap() {
            return false;
        }

        transcript.absorb_commitment(&proof.fri_commitments[0]);
        let mut fri_betas: Vec<Ext> = Vec::new();
        for i in 1..proof.fri_commitments.len() {
            let beta = transcript.squeeze_ext_challenge();
            fri_betas.push(beta);
            transcript.absorb_commitment(&proof.fri_commitments[i]);
        }

        // ── 8. Query indices ─────────────────────────────────────────
        let first_layer_half = lde_size / 2;
        let query_indices = transcript.squeeze_indices(NUM_QUERIES, first_layer_half);
        if proof.query_proofs.len() != NUM_QUERIES { return false; }

        let shifted_elements = shifted_domain.elements();
        let half_inv = BabyBear::new(2).inverse();

        for (qi_idx, qp) in proof.query_proofs.iter().enumerate() {
            let qi = query_indices[qi_idx];
            if qp.index != qi { return false; }
            if qp.fri_openings.len() != expected_folds - 1 { return false; }

            if !verify_row_opening(&qp.trace_opening, &proof.trace_commitment, num_cols) { return false; }
            let idx_g = (qi + BLOWUP) % lde_size;
            if qp.trace_opening_g.index != idx_g { return false; }
            if !verify_row_opening(&qp.trace_opening_g, &proof.trace_commitment, num_cols) { return false; }
            if !verify_row_opening_ext(&qp.accum_opening, &proof.accum_commitment, num_accum_cols) { return false; }
            if qp.accum_opening_g.index != idx_g { return false; }
            if !verify_row_opening_ext(&qp.accum_opening_g, &proof.accum_commitment, num_accum_cols) { return false; }
            if !verify_scalar_opening(&qp.quotient_opening, &proof.quotient_commitment) { return false; }
            if !verify_scalar_opening(&qp.deep_opening, &proof.fri_commitments[0]) { return false; }
            if !verify_scalar_opening(&qp.deep_opening_pair, &proof.fri_commitments[0]) { return false; }

            // x is base; z, g·z are extension.
            let x_i = Ext::from(shifted_elements[qi]);
            // All DEEP quotients use denominator (x - z); the g-shifted terms
            // open T(g·x) against T(gz), whose difference vanishes at x = z.
            // (Must mirror the prover exactly.)
            let inv_x_z = (x_i - z).inverse();

            let mut expected_deep = Ext::zero();
            let mut ci = 0;
            for col_idx in 0..num_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (Ext::from(qp.trace_opening.values[col_idx]) - proof.trace_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            for col_idx in 0..num_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (Ext::from(qp.trace_opening_g.values[col_idx]) - proof.trace_at_gz[col_idx]) * inv_x_z;
                ci += 1;
            }
            for col_idx in 0..num_accum_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.accum_opening.values[col_idx] - proof.accum_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            for col_idx in 0..num_accum_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.accum_opening_g.values[col_idx] - proof.accum_at_gz[col_idx]) * inv_x_z;
                ci += 1;
            }
            expected_deep = expected_deep + deep_coeffs[ci] * (qp.quotient_opening.value - proof.q_z) * inv_x_z;

            if qp.deep_opening.value != expected_deep { return false; }

            let a0 = qp.deep_opening.value;
            let b0 = qp.deep_opening_pair.value;
            let x0_inv = shifted_elements[qi].inverse();
            let mut prev_folded = {
                let avg = (a0 + b0).mul_base(half_inv);
                let diff = (a0 - b0).mul_base(half_inv);
                avg + diff * fri_betas[0] * Ext::from(x0_inv)
            };

            let mut pos = qi;
            for layer in 0..qp.fri_openings.len() {
                let fold_k = layer + 1;
                let layer_size = lde_size >> fold_k;
                let half = layer_size / 2;
                let lo = pos % half;
                let in_first_half = pos == lo;

                let (ref op, ref op_pair) = qp.fri_openings[layer];
                if !verify_scalar_opening(op, &proof.fri_commitments[fold_k]) { return false; }
                if !verify_scalar_opening(op_pair, &proof.fri_commitments[fold_k]) { return false; }

                if in_first_half {
                    if op.value != prev_folded { return false; }
                } else if op_pair.value != prev_folded { return false; }

                let x_inv = shifted_elements[lo].pow(1u64 << fold_k).inverse();
                let a_l = op.value;
                let b_l = op_pair.value;
                let avg = (a_l + b_l).mul_base(half_inv);
                let diff = (a_l - b_l).mul_base(half_inv);
                prev_folded = avg + diff * fri_betas[fold_k] * Ext::from(x_inv);
                pos = lo;
            }

            // Folding this query position through every committed layer must
            // land on the matching position of the (constant, commitment-bound)
            // final layer.
            if proof.fri_final_layer[pos] != prev_folded { return false; }
        }

        true
    }
}

/// Evaluate a base-field-coefficient polynomial at an extension point.
fn eval_base_at_ext(coeffs: &[BabyBear], z: Ext) -> Ext {
    let mut acc = Ext::zero();
    for &c in coeffs.iter().rev() {
        acc = acc * z + Ext::from(c);
    }
    acc
}

fn verify_row_opening(opening: &MerkleOpening, root: &[u8], num_cols: usize) -> bool {
    if opening.values.len() != num_cols { return false; }
    let mut h = Sha256::new();
    for v in &opening.values { h.update(v.to_bytes()); }
    let leaf = h.finalize().to_vec();
    verify_merkle_proof(leaf, &opening.proof, &root.to_vec())
}

fn verify_row_opening_ext(opening: &MerkleOpeningExt, root: &[u8], num_cols: usize) -> bool {
    if opening.values.len() != num_cols { return false; }
    let mut h = Sha256::new();
    for v in &opening.values { h.update(v.to_bytes()); }
    let leaf = h.finalize().to_vec();
    verify_merkle_proof(leaf, &opening.proof, &root.to_vec())
}

fn verify_scalar_opening(opening: &ScalarOpening, root: &[u8]) -> bool {
    let leaf = opening.value.to_bytes().to_vec();
    verify_merkle_proof(leaf, &opening.proof, &root.to_vec())
}

/// Recompute the Merkle root of an Ext-valued layer, matching the prover's
/// `build_scalar_merkle_tree_ext` (leaf = Ext little-endian bytes).
fn merkle_root_of_ext(values: &[Ext]) -> Vec<u8> {
    MerkleTree::new(values.iter().map(|v| v.to_bytes().to_vec()).collect())
        .root()
        .unwrap()
}

/// Barycentric-style Lagrange evaluation of a base-valued table at the
/// extension point z: `(z^n - 1)/n · Σ_i v_i·ω^i/(z - ω^i)`.
fn lagrange_ext(values: &[BabyBear], z: Ext, domain: &BabyBearDomain) -> Ext {
    let n = values.len();
    let elements = domain.elements();
    let z_n = z.pow_u128(n as u128) - Ext::one();
    let n_inv = BabyBear::new(n as u64).inverse();
    let mut sum = Ext::zero();
    for i in 0..n {
        let omega_i = elements[i];
        let denom = z - Ext::from(omega_i);
        // (values[i] * omega_i) is base; scale the Ext (z - ω^i)^-1 by it.
        sum = sum + denom.inverse().mul_base(values[i] * omega_i);
    }
    (sum * z_n).mul_base(n_inv)
}

/// Derive the out-of-domain point in the extension field. A non-base extension
/// element is automatically outside the base domain (so z, g·z avoid it).
fn derive_z_verifier(transcript: &mut FiatShamirTranscript) -> Ext {
    loop {
        let z = transcript.squeeze_ext_challenge();
        if !z.is_base() {
            return z;
        }
    }
}

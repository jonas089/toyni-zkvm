/// STARK verifier for ZKVM proofs (two-phase commitment protocol).

use sha2::{Digest, Sha256};
use toyni::babybear::BabyBear;
use toyni::math::domain::BabyBearDomain;
use toyni::math::polynomial::Polynomial;
use toyni::merkle::verify_merkle_proof;
use toyni::transcript::FiatShamirTranscript;

use zkvm_air::{
    eval_transition_constraints, num_transition_constraints,
    permutation, TraceView,
};
use zkvm_core::trace::{col, NUM_TRACE_COLS, NUM_ACCUM_COLS};

use zkvm_prover::{
    MerkleOpening, ScalarOpening, ZkvmProof, BLOWUP, COSET_SHIFT, NUM_QUERIES,
};

const NOP_INSTR: u32 = 0x00000013;

pub struct ZkvmVerifier;

impl ZkvmVerifier {
    pub fn verify(&self, proof: &ZkvmProof) -> bool {
        let trace_len = proof.trace_len;
        let lde_size = proof.lde_size;
        let num_cols = proof.num_cols;
        let num_accum_cols = proof.num_accum_cols;

        if lde_size != trace_len * BLOWUP {
            return false;
        }
        if num_cols != NUM_TRACE_COLS {
            return false;
        }
        if num_accum_cols != NUM_ACCUM_COLS {
            return false;
        }
        if proof.trace_at_z.len() != num_cols || proof.trace_at_gz.len() != num_cols {
            return false;
        }
        if proof.accum_at_z.len() != num_accum_cols || proof.accum_at_gz.len() != num_accum_cols {
            return false;
        }

        let domain = BabyBearDomain::new(trace_len);
        let extended_domain = BabyBearDomain::new(lde_size);
        let shift = BabyBear::new(COSET_SHIFT);
        let shifted_domain = extended_domain.get_coset(shift);
        let g = domain.group_gen();
        let z_poly = Polynomial::new(domain.vanishing_poly_coeffs());

        // ── 1. Replay Fiat-Shamir (two-phase) ────────────────────────
        let mut transcript = FiatShamirTranscript::new();

        // Bind public data to transcript (must match prover order)
        transcript.absorb_commitment(&proof.program_hash);
        transcript.absorb_field(BabyBear::from_u32(proof.entry_pc));
        for &inp in &proof.public_inputs {
            transcript.absorb_field(BabyBear::from_u32(inp));
        }
        for &out in &proof.public_outputs {
            transcript.absorb_field(BabyBear::from_u32(out));
        }
        transcript.absorb_field(BabyBear::from_u32(proof.public_inputs.len() as u32));
        transcript.absorb_field(BabyBear::from_u32(proof.public_outputs.len() as u32));

        // Phase 1: main trace commitment
        transcript.absorb_commitment(&proof.trace_commitment);

        // Phase 2: permutation challenges (4 pairs)
        let gammas: [BabyBear; 4] = [
            transcript.squeeze_challenge(), transcript.squeeze_challenge(),
            transcript.squeeze_challenge(), transcript.squeeze_challenge(),
        ];
        let alphas: [BabyBear; 4] = [
            transcript.squeeze_challenge(), transcript.squeeze_challenge(),
            transcript.squeeze_challenge(), transcript.squeeze_challenge(),
        ];

        // Verify challenges match proof
        if gammas != proof.gammas || alphas != proof.alphas {
            return false;
        }

        // Phase 2: accumulator commitment
        transcript.absorb_commitment(&proof.accum_commitment);

        // Phase 3: constraint random weights
        let num_main_constraints = num_transition_constraints();
        let num_accum_constraints = permutation::num_accum_constraints();
        let total_constraints = num_main_constraints + num_accum_constraints;
        // Boundary constraints:
        // First-row (16): clk=0, pc=entry_pc, 12 GP accums=1, ACCUM_RANGE=1, IS_HALTED=0
        // Last-row (1): IS_HALTED=1
        let num_boundary_first = 16;
        let num_boundary_last = 1;
        let total_with_boundary = total_constraints + num_boundary_first + num_boundary_last;

        let cweights: Vec<BabyBear> = (0..total_with_boundary)
            .map(|_| transcript.squeeze_challenge())
            .collect();

        transcript.absorb_commitment(&proof.quotient_commitment);

        let z = derive_z_verifier(&mut transcript, &extended_domain, &shifted_domain);

        // Feed OOD values into transcript (same order as prover)
        for &v in &proof.trace_at_z {
            transcript.absorb_field(v);
        }
        for &v in &proof.trace_at_gz {
            transcript.absorb_field(v);
        }
        for &v in &proof.accum_at_z {
            transcript.absorb_field(v);
        }
        for &v in &proof.accum_at_gz {
            transcript.absorb_field(v);
        }
        transcript.absorb_field(proof.q_z);

        // ── 2. OOD constraint check ──────────────────────────────────
        // (DEEP coefficients are squeezed later, after OOD check, matching prover order)
        let omega_n_minus_1 = g.pow((trace_len - 1) as u64);

        let curr_z = TraceView {
            vals: proof.trace_at_z.clone(),
        };
        let next_gz = TraceView {
            vals: proof.trace_at_gz.clone(),
        };

        // Main trace constraints
        let main_cvals = eval_transition_constraints(&curr_z, &next_gz);
        // Accumulator constraints
        let accum_cvals = permutation::eval_accum_constraints(
            &curr_z, &next_gz, &proof.accum_at_z, &proof.accum_at_gz, &gammas, &alphas,
        );

        // Split into excepted (zeroed at last row) and wrap-around (hold everywhere)
        let mut c_excepted = BabyBear::zero();
        let mut c_wrap = BabyBear::zero();
        for (j, &cv) in main_cvals.iter().enumerate() {
            c_excepted = c_excepted + cweights[j] * cv;
        }
        let num_main = main_cvals.len();
        for (j, &cv) in accum_cvals.iter().enumerate() {
            if permutation::is_wrap_constraint(j) {
                c_wrap = c_wrap + cweights[num_main + j] * cv;
            } else {
                c_excepted = c_excepted + cweights[num_main + j] * cv;
            }
        }
        let transition_q_z = (c_excepted * (z - omega_n_minus_1) + c_wrap) / z_poly.evaluate(z);

        // Boundary constraints at first row
        let entry_pc_field = BabyBear::from_u32(proof.entry_pc);
        let mut boundary_first_z = BabyBear::zero();
        let alpha_base = total_constraints;
        boundary_first_z = boundary_first_z + cweights[alpha_base] * proof.trace_at_z[col::CLK];
        boundary_first_z = boundary_first_z + cweights[alpha_base + 1] * (proof.trace_at_z[col::PC] - entry_pc_field);
        // 12 GP accumulators[first] = 1 (4×mem + 4×reg + 4×fetch)
        for a in 0..12 {
            boundary_first_z = boundary_first_z + cweights[alpha_base + 2 + a] * (proof.accum_at_z[a] - BabyBear::one());
        }
        // ACCUM_RANGE[first] = 1
        boundary_first_z = boundary_first_z
            + cweights[alpha_base + 14] * (proof.accum_at_z[permutation::ACCUM_RANGE] - BabyBear::one());
        // IS_HALTED[first] = 0
        boundary_first_z = boundary_first_z
            + cweights[alpha_base + 15] * proof.trace_at_z[col::IS_HALTED];
        let boundary_first_q_z = boundary_first_z / (z - BabyBear::one());

        // Boundary constraints at last row
        let mut boundary_last_z = BabyBear::zero();
        let alpha_last_base = total_constraints + num_boundary_first;
        boundary_last_z = boundary_last_z
            + cweights[alpha_last_base] * (proof.trace_at_z[col::IS_HALTED] - BabyBear::one());
        let boundary_last_q_z = boundary_last_z / (z - omega_n_minus_1);

        let expected_q_z = transition_q_z + boundary_first_q_z + boundary_last_q_z;
        if expected_q_z != proof.q_z {
            return false;
        }

        // ── 3. Program table binding ──────────────────────────────────
        // Verify program_hash matches the ROM and check OOD evaluations
        // of PROG_ADDR and PROG_INSTR against independently computed values.
        {
            // a) Hash the program ROM and check against claimed program_hash
            let mut hasher = Sha256::new();
            for &(addr, instr) in &proof.program_rom {
                hasher.update(addr.to_le_bytes());
                hasher.update(instr.to_le_bytes());
            }
            let expected_hash: [u8; 32] = hasher.finalize().into();
            if expected_hash != proof.program_hash {
                return false;
            }

            // b) Reconstruct the full program table (ROM + padding entry + filler)
            // The program table has one entry per row: ROM entries, then one padding entry, then fillers
            let m = proof.program_rom.len();
            let padding_count = trace_len - proof.num_real_steps;
            let has_padding = padding_count > 0;
            let prog_entries_needed = if has_padding { m + 1 } else { m };
            if prog_entries_needed > trace_len {
                return false;
            }
            let filler_count = trace_len - prog_entries_needed;

            let mut prog_addr_vals = Vec::with_capacity(trace_len);
            let mut prog_instr_vals = Vec::with_capacity(trace_len);

            // Program ROM entries
            for &(addr, instr) in &proof.program_rom {
                prog_addr_vals.push(BabyBear::from_u32(addr));
                prog_instr_vals.push(BabyBear::from_u32(instr));
            }
            // One padding NOP entry (if needed)
            if has_padding {
                prog_addr_vals.push(BabyBear::from_u32(proof.padding_start_pc));
                prog_instr_vals.push(BabyBear::from_u32(NOP_INSTR));
            }
            // Filler entries
            for _ in 0..filler_count {
                prog_addr_vals.push(BabyBear::zero());
                prog_instr_vals.push(BabyBear::from_u32(NOP_INSTR));
            }

            // c) Evaluate the program table polynomials at z using Lagrange interpolation
            let expected_prog_addr = eval_lagrange_at_z(&prog_addr_vals, z, &domain);
            let expected_prog_instr = eval_lagrange_at_z(&prog_instr_vals, z, &domain);

            // d) Check against the OOD values from the proof
            if proof.trace_at_z[col::PROG_ADDR] != expected_prog_addr {
                return false;
            }
            if proof.trace_at_z[col::PROG_INSTR] != expected_prog_instr {
                return false;
            }
        }

        // ── 3b. Output table binding ─────────────────────────────────
        // Verify that OUTPUT_ADDR and OUTPUT_VAL columns match the claimed public_outputs.
        {
            let output_tape_addr: u32 = 0x00300000; // OUTPUT_TAPE_ADDR
            let num_outputs = proof.public_outputs.len();

            let mut out_addr_vals = Vec::with_capacity(trace_len);
            let mut out_val_vals = Vec::with_capacity(trace_len);
            let mut out_mult_vals = Vec::with_capacity(trace_len);

            // Entry 0: count word
            out_addr_vals.push(BabyBear::from_u32(output_tape_addr));
            out_val_vals.push(BabyBear::from_u32(num_outputs as u32));
            out_mult_vals.push(BabyBear::one());

            // Entries 1..num_outputs: output values
            for (j, &val) in proof.public_outputs.iter().enumerate() {
                let addr = output_tape_addr + 4 + 4 * j as u32;
                out_addr_vals.push(BabyBear::from_u32(addr));
                out_val_vals.push(BabyBear::from_u32(val));
                out_mult_vals.push(BabyBear::one());
            }

            // Pad remaining with filler
            while out_addr_vals.len() < trace_len {
                out_addr_vals.push(BabyBear::zero());
                out_val_vals.push(BabyBear::zero());
                out_mult_vals.push(BabyBear::zero());
            }

            // Evaluate via Lagrange interpolation at z
            let expected_out_addr = eval_lagrange_at_z(&out_addr_vals, z, &domain);
            let expected_out_val = eval_lagrange_at_z(&out_val_vals, z, &domain);
            let expected_out_mult = eval_lagrange_at_z(&out_mult_vals, z, &domain);

            if proof.trace_at_z[col::OUTPUT_ADDR] != expected_out_addr {
                return false;
            }
            if proof.trace_at_z[col::OUTPUT_VAL] != expected_out_val {
                return false;
            }
            if proof.trace_at_z[col::OUTPUT_MULT] != expected_out_mult {
                return false;
            }
        }

        // ── 4. Squeeze DEEP random batching coefficients ──────────────
        let num_deep_terms = 2 * num_cols + 2 * num_accum_cols + 1;
        let deep_coeffs: Vec<BabyBear> = (0..num_deep_terms)
            .map(|_| transcript.squeeze_challenge())
            .collect();

        // ── 4. Replay FRI commitments & derive betas ─────────────────
        if proof.fri_commitments.is_empty() {
            return false;
        }
        transcript.absorb_commitment(&proof.fri_commitments[0]);

        let num_fri_folds = proof.fri_commitments.len() - 1;
        let mut fri_betas = Vec::with_capacity(num_fri_folds);
        for i in 1..proof.fri_commitments.len() {
            let beta = transcript.squeeze_challenge();
            fri_betas.push(beta);
            transcript.absorb_commitment(&proof.fri_commitments[i]);
        }

        // ── 5. Derive query indices ──────────────────────────────────
        let first_layer_half = lde_size / 2;
        let query_indices = transcript.squeeze_indices(NUM_QUERIES, first_layer_half);

        if proof.query_proofs.len() != NUM_QUERIES {
            return false;
        }

        let shifted_elements = shifted_domain.elements();
        let half_inv = BabyBear::new(2).inverse();

        // ── 6. Verify each query ─────────────────────────────────────
        for (qi_idx, qp) in proof.query_proofs.iter().enumerate() {
            let qi = query_indices[qi_idx];
            if qp.index != qi {
                return false;
            }

            // 6a. Verify trace row openings
            if !verify_row_opening(&qp.trace_opening, &proof.trace_commitment, num_cols) {
                return false;
            }
            let idx_g = (qi + BLOWUP) % lde_size;
            if qp.trace_opening_g.index != idx_g {
                return false;
            }
            if !verify_row_opening(&qp.trace_opening_g, &proof.trace_commitment, num_cols) {
                return false;
            }

            // 6b. Verify accumulator row openings
            if !verify_row_opening(&qp.accum_opening, &proof.accum_commitment, num_accum_cols) {
                return false;
            }
            if qp.accum_opening_g.index != idx_g {
                return false;
            }
            if !verify_row_opening(&qp.accum_opening_g, &proof.accum_commitment, num_accum_cols) {
                return false;
            }

            // 6c. Verify quotient opening
            if !verify_scalar_opening(&qp.quotient_opening, &proof.quotient_commitment) {
                return false;
            }

            // 6d. Verify DEEP layer
            if !verify_scalar_opening(&qp.deep_opening, &proof.fri_commitments[0]) {
                return false;
            }
            if !verify_scalar_opening(&qp.deep_opening_pair, &proof.fri_commitments[0]) {
                return false;
            }

            // 6e. DEEP polynomial consistency check (random batching)
            let x_i: BabyBear = shifted_elements[qi];
            let inv_x_z: BabyBear = (x_i - z).inverse();
            let inv_x_gz: BabyBear = (x_i - g * z).inverse();

            let mut expected_deep = BabyBear::zero();
            let mut ci = 0;
            // Main trace columns at z
            for col_idx in 0..num_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.trace_opening.values[col_idx] - proof.trace_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            // Main trace columns at g*z
            for col_idx in 0..num_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.trace_opening_g.values[col_idx] - proof.trace_at_gz[col_idx])
                        * inv_x_gz;
                ci += 1;
            }
            // Accumulator columns at z
            for col_idx in 0..num_accum_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.accum_opening.values[col_idx] - proof.accum_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            // Accumulator columns at g*z
            for col_idx in 0..num_accum_cols {
                expected_deep = expected_deep
                    + deep_coeffs[ci] * (qp.accum_opening_g.values[col_idx] - proof.accum_at_gz[col_idx])
                        * inv_x_gz;
                ci += 1;
            }
            // Quotient at z
            expected_deep =
                expected_deep + deep_coeffs[ci] * (qp.quotient_opening.value - proof.q_z) * inv_x_z;

            if qp.deep_opening.value != expected_deep {
                return false;
            }

            // 6f. First FRI fold
            let a0 = qp.deep_opening.value;
            let b0 = qp.deep_opening_pair.value;
            let x0: BabyBear = shifted_elements[qi];

            let mut prev_folded = {
                let avg = (a0 + b0) * half_inv;
                let diff = (a0 - b0) * half_inv;
                avg + diff * fri_betas[0] * x0.inverse()
            };

            // 6g. Intermediate FRI layers
            let mut pos = qi;
            for layer in 0..qp.fri_openings.len() {
                let fold_k = layer + 1;
                let layer_size = lde_size >> fold_k;
                let half = layer_size / 2;

                let lo = pos % half;
                let in_first_half = pos == lo;

                let (ref op, ref op_pair) = qp.fri_openings[layer];

                if !verify_scalar_opening(op, &proof.fri_commitments[fold_k]) {
                    return false;
                }
                if !verify_scalar_opening(op_pair, &proof.fri_commitments[fold_k]) {
                    return false;
                }

                if in_first_half {
                    if op.value != prev_folded {
                        return false;
                    }
                } else if op_pair.value != prev_folded {
                    return false;
                }

                let x = shifted_elements[lo].pow(1u64 << fold_k);
                let a_l = op.value;
                let b_l = op_pair.value;
                let avg = (a_l + b_l) * half_inv;
                let diff = (a_l - b_l) * half_inv;
                prev_folded = avg + diff * fri_betas[fold_k] * x.inverse();

                pos = lo;
            }

            // 6h. Final FRI value check
            if prev_folded != proof.fri_final_value {
                return false;
            }
        }

        true
    }
}

fn verify_row_opening(opening: &MerkleOpening, root: &[u8], num_cols: usize) -> bool {
    if opening.values.len() != num_cols {
        return false;
    }
    let mut hasher = Sha256::new();
    for v in &opening.values {
        let bytes: [u8; 8] = v.to_bytes();
        hasher.update(bytes);
    }
    let leaf = hasher.finalize().to_vec();
    verify_merkle_proof(leaf, &opening.proof, &root.to_vec())
}

fn verify_scalar_opening(opening: &ScalarOpening, root: &[u8]) -> bool {
    let leaf = opening.value.to_bytes().to_vec();
    verify_merkle_proof(leaf, &opening.proof, &root.to_vec())
}

/// Evaluate a polynomial (given by its values on the trace domain) at point z
/// using the Lagrange interpolation formula:
///   P(z) = (z^n - 1) / n * Σ_{i=0}^{n-1} f_i * ω^i / (z - ω^i)
fn eval_lagrange_at_z(
    values: &[BabyBear],
    z: BabyBear,
    domain: &BabyBearDomain,
) -> BabyBear {
    let n = values.len();
    let elements = domain.elements();
    let z_n = z.pow(n as u64) - BabyBear::one(); // z^n - 1
    let n_inv = BabyBear::new(n as u64).inverse(); // 1/n

    let mut sum = BabyBear::zero();
    for i in 0..n {
        let omega_i = elements[i]; // ω^i
        let denom = z - omega_i;   // z - ω^i
        // Each Lagrange basis is: (z^n - 1) / (n * (z - ω^i)) * ω^i
        // But we factor out (z^n - 1) / n and sum f_i * ω^i / (z - ω^i)
        sum = sum + values[i] * omega_i * denom.inverse();
    }
    sum * z_n * n_inv
}

fn derive_z_verifier(
    transcript: &mut FiatShamirTranscript,
    extended_domain: &BabyBearDomain,
    shifted_domain: &BabyBearDomain,
) -> BabyBear {
    let ext_set: std::collections::HashSet<BabyBear> =
        extended_domain.elements().into_iter().collect();
    let shift_set: std::collections::HashSet<BabyBear> =
        shifted_domain.elements().into_iter().collect();
    let g = extended_domain.group_gen();

    loop {
        let z = transcript.squeeze_challenge();
        if !ext_set.contains(&z)
            && !shift_set.contains(&z)
            && !shift_set.contains(&(g * z))
        {
            return z;
        }
    }
}

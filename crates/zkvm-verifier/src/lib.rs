#![allow(clippy::assign_op_pattern, clippy::needless_range_loop)]
//! Engine-generic verifier for the small custom VM.
//!
//! Replays Fiat-Shamir, checks the out-of-domain constraint-quotient identity,
//! Lagrange-binds the program ROM / public I/O tables to the caller's public
//! data, and spot-checks the DEEP/FRI chain. Written once over `toyni::Engine`
//! so it verifies proofs from either the roots-of-unity or the circle engine.

use sha2::{Digest, Sha256};

use toyni::engine::Engine;
use toyni::field::Field;
use toyni::merkle::{verify_path, Hash};
use toyni::transcript::Transcript;

use zkvm_air::{num_transition_constraints, permutation};
use zkvm_core::{col, NUM_ACCUM_COLS, NUM_TRACE_COLS};
use zkvm_prover::{
    fri_degree_bound, num_b_first, quotient_identity, row_digest, scalar_digest,
    RowOpening, ScalarOpening, ZkvmProof, BLOWUP, NUM_QUERIES, };

pub struct ZkvmVerifier;

impl ZkvmVerifier {
    pub fn verify<E: Engine>(
        &self,
        proof: &ZkvmProof<E>,
        expected_program_hash: &[u8; 32],
        expected_entry_pc: u32,
    ) -> bool {
        verify::<E>(proof, expected_program_hash, expected_entry_pc)
    }
}

pub fn verify<E: Engine>(
    proof: &ZkvmProof<E>,
    expected_program_hash: &[u8; 32],
    expected_entry_pc: u32,
) -> bool {
    if &proof.program_hash != expected_program_hash {
        return false;
    }
    if proof.entry_pc != expected_entry_pc {
        return false;
    }

    let trace_len = proof.trace_len;
    let num_cols = proof.num_cols;
    if !trace_len.is_power_of_two() || trace_len < 2 {
        return false;
    }
    if num_cols != NUM_TRACE_COLS || proof.num_accum_cols != NUM_ACCUM_COLS {
        return false;
    }
    if proof.trace_at_z.len() != num_cols || proof.trace_at_gz.len() != num_cols {
        return false;
    }
    if proof.queries.len() != NUM_QUERIES {
        return false;
    }

    let log_trace = trace_len.trailing_zeros();
    let log_eval = log_trace + BLOWUP.trailing_zeros();
    let lde_size = 1usize << log_eval;
    let log_bound = fri_degree_bound(trace_len).trailing_zeros();
    let half = lde_size / 2;

    let trace_tf = E::transform(log_trace);
    let points = E::eval_points(log_eval);
    let rotation_step = E::rotation_step(log_trace, log_eval);

    let num_main = num_transition_constraints::<E::Ext>();
    let num_accum = permutation::num_accum_constraints();
    let total_constraints = num_main + num_accum;
    let total_with_boundary = total_constraints + num_b_first() + 1;

    // ── transcript replay ────────────────────────────────────────────
    let mut t = Transcript::new(b"zkvm");
    t.absorb_commitment(&proof.program_hash);
    t.absorb_field(E::Base::from_u64(proof.entry_pc as u64));
    for &v in &proof.public_inputs {
        t.absorb_field(E::Base::from_u64(v as u64));
    }
    for &v in &proof.public_outputs {
        t.absorb_field(E::Base::from_u64(v as u64));
    }
    t.absorb_field(E::Base::from_u64(proof.public_inputs.len() as u64));
    t.absorb_field(E::Base::from_u64(proof.public_outputs.len() as u64));
    t.absorb_commitment(&proof.trace_root);

    let gammas: [E::Ext; 4] = std::array::from_fn(|_| E::draw_ext(&mut t));
    let alphas: [E::Ext; 4] = std::array::from_fn(|_| E::draw_ext(&mut t));
    if gammas != proof.gammas || alphas != proof.alphas {
        return false;
    }
    t.absorb_commitment(&proof.accum_root);
    let cweights: Vec<E::Ext> = (0..total_with_boundary).map(|_| E::draw_ext(&mut t)).collect();
    t.absorb_commitment(&proof.quotient_root);

    let gamma = E::draw_ood(&mut t);
    let van_z = E::vanishing_at_ood(log_trace, gamma);
    let entry_pc_e = E::Ext::from(E::Base::from_u64(proof.entry_pc as u64));

    for &v in &proof.trace_at_z {
        E::absorb_ext(&mut t, v);
    }
    for &v in &proof.trace_at_gz {
        E::absorb_ext(&mut t, v);
    }
    for &v in &proof.accum_at_z {
        E::absorb_ext(&mut t, v);
    }
    for &v in &proof.accum_at_gz {
        E::absorb_ext(&mut t, v);
    }
    E::absorb_ext(&mut t, proof.q_z);

    // ── out-of-domain constraint-quotient identity ───────────────────
    let q_expected = quotient_identity::<E>(
        log_trace,
        gamma,
        &proof.trace_at_z,
        &proof.trace_at_gz,
        &proof.accum_at_z,
        &proof.accum_at_gz,
        &cweights,
        &gammas,
        &alphas,
        entry_pc_e,
        van_z,
        num_main,
        total_constraints,
    );
    if q_expected != proof.q_z {
        return false;
    }

    // ── bind program ROM + public tables ─────────────────────────────
    let mut hasher = Sha256::new();
    for &(addr, op, a, b, c) in &proof.program_rom {
        hasher.update(addr.to_le_bytes());
        hasher.update(op.to_le_bytes());
        hasher.update(a.to_le_bytes());
        hasher.update(b.to_le_bytes());
        hasher.update(c.to_le_bytes());
    }
    let rom_hash: [u8; 32] = hasher.finalize().into();
    if rom_hash != proof.program_hash {
        return false;
    }
    if proof.program_rom.len() > trace_len {
        return false;
    }

    let eval_col = |values: Vec<E::Base>| eval_public_table::<E>(&values, log_trace, gamma, &trace_tf);

    let mut addr_v = vec![E::Base::ZERO; trace_len];
    let mut op_v = vec![E::Base::ZERO; trace_len];
    let mut a_v = vec![E::Base::ZERO; trace_len];
    let mut b_v = vec![E::Base::ZERO; trace_len];
    let mut c_v = vec![E::Base::ZERO; trace_len];
    let mut real_v = vec![E::Base::ZERO; trace_len];
    for (i, &(addr, op, a, b, c)) in proof.program_rom.iter().enumerate() {
        addr_v[i] = E::Base::from_u64(addr as u64);
        op_v[i] = E::Base::from_u64(op as u64);
        a_v[i] = E::Base::from_u64(a as u64);
        b_v[i] = E::Base::from_u64(b as u64);
        c_v[i] = E::Base::from_u64(c as u64);
        real_v[i] = E::Base::ONE;
    }
    if proof.trace_at_z[col::PROG] != eval_col(addr_v)
        || proof.trace_at_z[col::PROG + 1] != eval_col(op_v)
        || proof.trace_at_z[col::PROG + 2] != eval_col(a_v)
        || proof.trace_at_z[col::PROG + 3] != eval_col(b_v)
        || proof.trace_at_z[col::PROG + 4] != eval_col(c_v)
        || proof.trace_at_z[col::PROG + 6] != eval_col(real_v)
    {
        return false;
    }

    let mut in_addr = vec![E::Base::ZERO; trace_len];
    let mut in_val = vec![E::Base::ZERO; trace_len];
    let mut in_mult = vec![E::Base::ZERO; trace_len];
    for (j, &v) in proof.public_inputs.iter().enumerate() {
        if j >= trace_len {
            return false;
        }
        in_addr[j] = E::Base::from_u64(j as u64);
        in_val[j] = E::Base::from_u64(v as u64);
        in_mult[j] = E::Base::ONE;
    }
    if proof.trace_at_z[col::PUB_IN] != eval_col(in_addr)
        || proof.trace_at_z[col::PUB_IN + 1] != eval_col(in_val)
        || proof.trace_at_z[col::PUB_IN + 2] != eval_col(in_mult)
    {
        return false;
    }

    let mut out_addr = vec![E::Base::ZERO; trace_len];
    let mut out_val = vec![E::Base::ZERO; trace_len];
    let mut out_mult = vec![E::Base::ZERO; trace_len];
    for (j, &v) in proof.public_outputs.iter().enumerate() {
        if j >= trace_len {
            return false;
        }
        out_addr[j] = E::Base::from_u64(j as u64);
        out_val[j] = E::Base::from_u64(v as u64);
        out_mult[j] = E::Base::ONE;
    }
    if proof.trace_at_z[col::PUB_OUT] != eval_col(out_addr)
        || proof.trace_at_z[col::PUB_OUT + 1] != eval_col(out_val)
        || proof.trace_at_z[col::PUB_OUT + 2] != eval_col(out_mult)
    {
        return false;
    }

    // ── DEEP + FRI ───────────────────────────────────────────────────
    let num_deep = 2 * num_cols + 2 * NUM_ACCUM_COLS + 1;
    let deep: Vec<E::Ext> = (0..num_deep).map(|_| E::draw_ext(&mut t)).collect();
    let challenges = E::fri_replay(&mut t, &proof.fri, log_bound);
    let query_indices = t.draw_indices(NUM_QUERIES, half);
    if !E::fri_check_shape(&proof.fri, log_eval, log_bound, NUM_QUERIES) {
        return false;
    }
    let fri_qps = E::fri_query_proofs(&proof.fri);

    for (qi_idx, &qi) in query_indices.iter().enumerate() {
        let qp = &proof.queries[qi_idx];
        if qp.trace.len() != 4 || qp.accum.len() != 4 || qp.quotient.len() != 2 {
            return false;
        }
        let positions = [
            qi,
            E::rotation_index(log_eval, qi, rotation_step),
            qi + half,
            E::rotation_index(log_eval, qi + half, rotation_step),
        ];
        // Merkle openings.
        for (k, &pos) in positions.iter().enumerate() {
            if !verify_row::<E::Base>(&proof.trace_root, pos, &qp.trace[k], num_cols) {
                return false;
            }
            if !verify_row::<E::Ext>(&proof.accum_root, pos, &qp.accum[k], NUM_ACCUM_COLS) {
                return false;
            }
        }
        if !verify_scalar::<E::Ext>(&proof.quotient_root, qi, &qp.quotient[0])
            || !verify_scalar::<E::Ext>(&proof.quotient_root, qi + half, &qp.quotient[1])
        {
            return false;
        }

        // Reconstruct the DEEP-batched value at qi and its sibling.
        let word_q = reconstruct_deep::<E>(
            gamma, points[qi], &deep, &qp.trace[0].values, &qp.trace[1].values,
            &qp.accum[0].values, &qp.accum[1].values, qp.quotient[0].value, proof,
        );
        let word_sib = reconstruct_deep::<E>(
            gamma, points[qi + half], &deep, &qp.trace[2].values, &qp.trace[3].values,
            &qp.accum[2].values, &qp.accum[3].values, qp.quotient[1].value, proof,
        );

        if !E::fri_verify_query(
            &proof.fri, log_eval, log_bound, &challenges, qi, word_q, word_sib, &fri_qps[qi_idx],
        ) {
            return false;
        }
    }
    true
}

/// Evaluate the trace-domain interpolant of a base-valued public table at the
/// out-of-domain point (binding a committed table column to public data).
fn eval_public_table<E: Engine>(
    values: &[E::Base],
    log_trace: u32,
    gamma: E::Ood,
    tf: &E::Transform,
) -> E::Ext {
    let n = 1usize << log_trace;
    let mut v = vec![E::Base::ZERO; n];
    for (row, &val) in values.iter().enumerate() {
        v[E::fft_index_of_row(log_trace, row)] = val;
    }
    E::interpolate(&mut v, tf);
    E::eval_at_ood(&v, gamma)
}

#[allow(clippy::too_many_arguments)]
fn reconstruct_deep<E: Engine>(
    gamma: E::Ood,
    point: E::Point,
    deep: &[E::Ext],
    trace_self: &[E::Base],
    trace_next: &[E::Base],
    accum_self: &[E::Ext],
    accum_next: &[E::Ext],
    q_val: E::Ext,
    proof: &ZkvmProof<E>,
) -> E::Ext {
    let inv = E::deep_denom_inv_at(gamma, point);
    let num_cols = proof.num_cols;
    let mut d = E::Ext::ZERO;
    let mut ci = 0;
    for c in 0..num_cols {
        d = d + deep[ci] * (E::Ext::from(trace_self[c]) - proof.trace_at_z[c]) * inv;
        ci += 1;
    }
    for c in 0..num_cols {
        d = d + deep[ci] * (E::Ext::from(trace_next[c]) - proof.trace_at_gz[c]) * inv;
        ci += 1;
    }
    for c in 0..NUM_ACCUM_COLS {
        d = d + deep[ci] * (accum_self[c] - proof.accum_at_z[c]) * inv;
        ci += 1;
    }
    for c in 0..NUM_ACCUM_COLS {
        d = d + deep[ci] * (accum_next[c] - proof.accum_at_gz[c]) * inv;
        ci += 1;
    }
    d + deep[ci] * (q_val - proof.q_z) * inv
}

fn verify_row<F: Field>(root: &Hash, pos: usize, o: &RowOpening<F>, num_cols: usize) -> bool {
    if o.values.len() != num_cols {
        return false;
    }
    let leaf = row_digest(&o.values, &o.salt);
    verify_path(root, pos, &leaf, &o.path)
}

fn verify_scalar<F: Field>(root: &Hash, pos: usize, o: &ScalarOpening<F>) -> bool {
    let leaf = scalar_digest(o.value, &o.salt);
    verify_path(root, pos, &leaf, &o.path)
}

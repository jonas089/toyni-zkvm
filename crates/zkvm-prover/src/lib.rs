#![allow(clippy::assign_op_pattern, clippy::needless_range_loop)]
//! Engine-generic STARK prover for the small custom VM.
//!
//! The proof pipeline — commit the trace, commit the permutation/lookup
//! accumulators, commit the combined constraint quotient, sample out-of-domain,
//! batch the single-point DEEP quotients, FRI to a constant final layer — is
//! written once over `toyni::Engine`. Switching from the roots-of-unity engine
//! to the circle engine changes only the field, domain geometry, FFT and FRI;
//! the VM's constraint logic (transitions + LogUp / grand-product
//! accumulators) is field-generic and untouched.

use rand::Rng;
use sha2::{Digest, Sha256};

use toyni::engine::Engine;
use toyni::field::{batch_inverse, ExtField, Field};
use toyni::merkle::{Hash, MerkleTree};
use toyni::transcript::Transcript;

use zkvm_air::{eval_transition_constraints, num_transition_constraints, permutation, TraceView};
use zkvm_core::{accum, col, NUM_ACCUM_COLS, NUM_CHANNELS, NUM_TRACE_COLS};

/// Spot-check queries (~2^-132 at the tested rate).
pub const NUM_QUERIES: usize = 132;
/// LDE blowup.
pub const BLOWUP: usize = 16;
/// Max total degree of any AIR constraint (register grand product is degree 4).
pub const COMPOSITION_DEGREE: usize = 4;
/// Random blinding coefficients per committed column.
pub const MASK_DEGREE: usize = 2 * NUM_QUERIES + 4;
const SALT_LEN: usize = 16;

/// FRI degree bound: smallest power of two above deg(D) of the masked DEEP
/// composition; the prover folds to a final layer of size lde/D_BOUND.
pub fn fri_degree_bound(trace_len: usize) -> usize {
    (COMPOSITION_DEGREE * (trace_len + MASK_DEGREE) - trace_len).next_power_of_two()
}

/// Number of first-row boundary constraints.
pub fn num_b_first() -> usize {
    5 + 5 * NUM_CHANNELS + 2
}

// ── proof data structures ─────────────────────────────────────────────

/// Opening of a committed row: the column values, the leaf salt, and the
/// Merkle path. The row position is derived by the verifier.
#[derive(Debug, Clone)]
pub struct RowOpening<F> {
    pub values: Vec<F>,
    pub salt: [u8; SALT_LEN],
    pub path: Vec<Hash>,
}

/// Opening of a single committed scalar.
#[derive(Debug, Clone)]
pub struct ScalarOpening<F> {
    pub value: F,
    pub salt: [u8; SALT_LEN],
    pub path: Vec<Hash>,
}

/// Per-query openings. `trace`/`accum` are opened at `[qi, next(qi), qi+half,
/// next(qi+half)]` (self + next-row, for the query and its FRI sibling); the
/// quotient at `[qi, qi+half]`.
#[derive(Debug, Clone)]
pub struct QueryProof<E: Engine> {
    pub trace: Vec<RowOpening<E::Base>>,
    pub accum: Vec<RowOpening<E::Ext>>,
    pub quotient: Vec<ScalarOpening<E::Ext>>,
}

#[derive(Clone)]
pub struct ZkvmProof<E: Engine> {
    pub trace_len: usize,
    pub num_cols: usize,
    pub num_accum_cols: usize,

    pub trace_root: Hash,
    pub accum_root: Hash,
    pub quotient_root: Hash,

    pub trace_at_z: Vec<E::Ext>,
    pub trace_at_gz: Vec<E::Ext>,
    pub accum_at_z: Vec<E::Ext>,
    pub accum_at_gz: Vec<E::Ext>,
    pub q_z: E::Ext,

    pub gammas: [E::Ext; 4],
    pub alphas: [E::Ext; 4],

    pub fri: E::FriProof,
    pub queries: Vec<QueryProof<E>>,

    pub program_hash: [u8; 32],
    pub public_inputs: Vec<u32>,
    pub public_outputs: Vec<u32>,
    pub entry_pc: u32,
    pub program_rom: Vec<(u32, u32, u32, u32, u32)>,
}

// ── prover ────────────────────────────────────────────────────────────

pub struct ZkvmProver<E: Engine> {
    columns: Vec<Vec<E::Base>>,
    program_hash: [u8; 32],
    public_inputs: Vec<u32>,
    public_outputs: Vec<u32>,
    entry_pc: u32,
    program_rom: Vec<(u32, u32, u32, u32, u32)>,
}

impl<E: Engine> ZkvmProver<E> {
    pub fn new(
        columns: Vec<Vec<E::Base>>,
        program_hash: [u8; 32],
        public_inputs: Vec<u32>,
        public_outputs: Vec<u32>,
        entry_pc: u32,
        program_rom: Vec<(u32, u32, u32, u32, u32)>,
    ) -> Self {
        assert!(!columns.is_empty());
        let n = columns[0].len();
        assert!(n.is_power_of_two() && n >= 2);
        assert_eq!(columns.len(), NUM_TRACE_COLS);
        for c in &columns {
            assert_eq!(c.len(), n);
        }
        Self {
            columns,
            program_hash,
            public_inputs,
            public_outputs,
            entry_pc,
            program_rom,
        }
    }

    pub fn prove(&self) -> ZkvmProof<E> {
        let num_cols = self.columns.len();
        let trace_len = self.columns[0].len();
        let log_trace = trace_len.trailing_zeros();
        let log_eval = log_trace + BLOWUP.trailing_zeros();
        let lde_size = 1usize << log_eval;
        let log_bound = fri_degree_bound(trace_len).trailing_zeros();
        let mut rng = rand::thread_rng();

        let trace_tf = E::transform(log_trace);
        let eval_tf = E::transform(log_eval);
        let points = E::eval_points(log_eval);
        let rotation_step = E::rotation_step(log_trace, log_eval);
        let vn = E::vanishing_over_eval(log_trace, &points);
        let mask_log = (2 * MASK_DEGREE)
            .next_power_of_two()
            .trailing_zeros()
            .min(log_trace);

        // ── Phase 1: trace ──────────────────────────────────────────────
        let mut trace_coeffs: Vec<Vec<E::Base>> = Vec::with_capacity(num_cols);
        let mut trace_mask: Vec<Vec<E::Base>> = Vec::with_capacity(num_cols);
        let mut trace_lde: Vec<Vec<E::Base>> = Vec::with_capacity(num_cols);
        for (c, col_vals) in self.columns.iter().enumerate() {
            // Only witness columns are blinded; the public Lagrange-bound tables
            // (program ROM + public I/O) carry no witness and stay unblinded.
            let blind = c < col::PROG;
            let mut values = vec![E::Base::ZERO; trace_len];
            for (row, &v) in col_vals.iter().enumerate() {
                values[E::fft_index_of_row(log_trace, row)] = v;
            }
            E::interpolate(&mut values, &trace_tf);
            let coeffs = values;
            let mut lde = E::evaluate_lde(&coeffs, log_trace, log_eval, &eval_tf);
            let r: Vec<E::Base> = if blind {
                (0..1usize << mask_log)
                    .map(|_| E::Base::random(&mut rng))
                    .collect()
            } else {
                Vec::new()
            };
            if blind {
                let r_lde = E::evaluate_lde(&r, mask_log, log_eval, &eval_tf);
                for i in 0..lde_size {
                    lde[i] += vn[i] * r_lde[i];
                }
            }
            trace_coeffs.push(coeffs);
            trace_mask.push(r);
            trace_lde.push(lde);
        }
        let trace_salts = salts(lde_size, &mut rng);
        let trace_tree = commit_rows::<E::Base>(&trace_lde, &trace_salts);
        let trace_root = trace_tree.root();

        let mut transcript = Transcript::new(b"zkvm");
        transcript.absorb_commitment(&self.program_hash);
        transcript.absorb_field(E::Base::from_u64(self.entry_pc as u64));
        for &v in &self.public_inputs {
            transcript.absorb_field(E::Base::from_u64(v as u64));
        }
        for &v in &self.public_outputs {
            transcript.absorb_field(E::Base::from_u64(v as u64));
        }
        transcript.absorb_field(E::Base::from_u64(self.public_inputs.len() as u64));
        transcript.absorb_field(E::Base::from_u64(self.public_outputs.len() as u64));
        transcript.absorb_commitment(&trace_root);

        // ── Phase 2: accumulators ───────────────────────────────────────
        let gammas: [E::Ext; 4] = std::array::from_fn(|_| E::draw_ext(&mut transcript));
        let alphas: [E::Ext; 4] = std::array::from_fn(|_| E::draw_ext(&mut transcript));

        let accum_columns =
            permutation::compute_accumulators::<E::Base, E::Ext>(&self.columns, &gammas, &alphas);
        assert_eq!(accum_columns.len(), NUM_ACCUM_COLS);
        zkvm_air::validate_full_trace::<E::Base, E::Ext>(
            &self.columns,
            &accum_columns,
            &gammas,
            &alphas,
        )
        .expect("trace fails AIR validation");

        let mut accum_coeffs: Vec<Vec<E::Ext>> = Vec::with_capacity(NUM_ACCUM_COLS);
        let mut accum_mask: Vec<Vec<E::Ext>> = Vec::with_capacity(NUM_ACCUM_COLS);
        let mut accum_lde: Vec<Vec<E::Ext>> = Vec::with_capacity(NUM_ACCUM_COLS);
        for col_vals in &accum_columns {
            let mut values = vec![E::Ext::ZERO; trace_len];
            for (row, &v) in col_vals.iter().enumerate() {
                values[E::fft_index_of_row(log_trace, row)] = v;
            }
            E::interpolate_ext(&mut values, &trace_tf);
            let coeffs = values;
            let mut lde = E::evaluate_lde_ext(&coeffs, log_trace, log_eval, &eval_tf);
            let r: Vec<E::Ext> = (0..1usize << mask_log)
                .map(|_| E::Ext::random(&mut rng))
                .collect();
            let r_lde = E::evaluate_lde_ext(&r, mask_log, log_eval, &eval_tf);
            for i in 0..lde_size {
                lde[i] = lde[i] + r_lde[i].mul_base(vn[i]);
            }
            accum_coeffs.push(coeffs);
            accum_mask.push(r);
            accum_lde.push(lde);
        }
        let accum_salts = salts(lde_size, &mut rng);
        let accum_tree = commit_rows::<E::Ext>(&accum_lde, &accum_salts);
        let accum_root = accum_tree.root();
        transcript.absorb_commitment(&accum_root);

        // ── Phase 3: combined constraint quotient ───────────────────────
        let num_main = num_transition_constraints::<E::Ext>();
        let num_accum = permutation::num_accum_constraints();
        let total_constraints = num_main + num_accum;
        let total_with_boundary = total_constraints + num_b_first() + 1;
        let cweights: Vec<E::Ext> = (0..total_with_boundary)
            .map(|_| E::draw_ext(&mut transcript))
            .collect();

        let inv_vh = batch_inverse(&vn);
        let p_last = E::trace_point(log_trace, trace_len - 1);
        let p_first = E::trace_point(log_trace, 0);
        let excl = E::point_vanishing_over_eval(p_last, &points);
        let inv_last = E::boundary_denom_inv_over_eval(p_last, &points);
        let inv_first = E::boundary_denom_inv_over_eval(p_first, &points);
        let entry_pc_e = E::Ext::from(E::Base::from_u64(self.entry_pc as u64));
        let alpha_b = total_constraints;
        let rom_b = total_constraints + 5 + 5 * NUM_CHANNELS;
        let alpha_l = total_constraints + num_b_first();

        let q_evals: Vec<E::Ext> = (0..lde_size)
            .map(|i| {
                let next_i = E::rotation_index(log_eval, i, rotation_step);
                let curr = build_trace_view::<E>(&trace_lde, i);
                let next = build_trace_view::<E>(&trace_lde, next_i);
                let curr_acc: Vec<E::Ext> = accum_lde.iter().map(|c| c[i]).collect();
                let next_acc: Vec<E::Ext> = accum_lde.iter().map(|c| c[next_i]).collect();

                let main_cv = eval_transition_constraints(&curr, &next);
                let accum_cv = permutation::eval_accum_constraints(
                    &curr, &next, &curr_acc, &next_acc, &gammas, &alphas,
                );
                let mut c_excepted = E::Ext::ZERO;
                for (j, &v) in main_cv.iter().enumerate() {
                    c_excepted = c_excepted + cweights[j] * v;
                }
                let mut c_wrap = E::Ext::ZERO;
                for (j, &v) in accum_cv.iter().enumerate() {
                    c_wrap = c_wrap + cweights[num_main + j] * v;
                }
                let transition_q = (c_excepted * excl[i] + c_wrap).mul_base(inv_vh[i]);

                let one = E::Ext::ONE;
                let mut b_first = E::Ext::ZERO;
                b_first = b_first + cweights[alpha_b] * curr.col(col::CLK);
                b_first = b_first + cweights[alpha_b + 1] * (curr.col(col::PC) - entry_pc_e);
                b_first = b_first + cweights[alpha_b + 2] * curr.col(col::HALT);
                b_first = b_first + cweights[alpha_b + 3] * curr.col(col::I_IN);
                b_first = b_first + cweights[alpha_b + 4] * curr.col(col::I_OUT);
                for ch in 0..NUM_CHANNELS {
                    b_first = b_first + cweights[alpha_b + 5 + ch] * (curr_acc[accum::REG + ch] - one);
                    b_first = b_first + cweights[alpha_b + 5 + NUM_CHANNELS + ch] * (curr_acc[accum::MEM + ch] - one);
                    b_first = b_first + cweights[alpha_b + 5 + 2 * NUM_CHANNELS + ch] * curr_acc[accum::PROG + ch];
                    b_first = b_first + cweights[alpha_b + 5 + 3 * NUM_CHANNELS + ch] * curr_acc[accum::PUB_IN + ch];
                    b_first = b_first + cweights[alpha_b + 5 + 4 * NUM_CHANNELS + ch] * curr_acc[accum::PUB_OUT + ch];
                }
                b_first = b_first + cweights[rom_b] * curr.col(col::PROG);
                let smem_init = curr.col(col::SMEM + 4) * (one - curr.col(col::SMEM + 3)) * curr.col(col::SMEM + 1);
                b_first = b_first + cweights[rom_b + 1] * smem_init;
                let b_first_q = b_first * inv_first[i];

                let b_last = cweights[alpha_l] * (curr.col(col::HALT) - one);
                let b_last_q = b_last * inv_last[i];

                transition_q + b_first_q + b_last_q
            })
            .collect();

        let q_salts = salts(lde_size, &mut rng);
        let q_tree = commit_scalars::<E::Ext>(&q_evals, &q_salts);
        let quotient_root = q_tree.root();
        transcript.absorb_commitment(&quotient_root);

        // ── Phase 4: out-of-domain ──────────────────────────────────────
        let gamma = E::draw_ood(&mut transcript);
        let gz = E::mask_point(gamma, 1, log_trace);
        let van_z = E::vanishing_at_ood(log_trace, gamma);
        let van_gz = E::vanishing_at_ood(log_trace, gz);

        let trace_at_z = ood_base::<E>(&trace_coeffs, &trace_mask, gamma, van_z, num_cols);
        let trace_at_gz = ood_base::<E>(&trace_coeffs, &trace_mask, gz, van_gz, num_cols);
        let accum_at_z = ood_ext::<E>(&accum_coeffs, &accum_mask, gamma, van_z);
        let accum_at_gz = ood_ext::<E>(&accum_coeffs, &accum_mask, gz, van_gz);

        let q_z = quotient_identity::<E>(
            log_trace, gamma, &trace_at_z, &trace_at_gz, &accum_at_z, &accum_at_gz, &cweights,
            &gammas, &alphas, entry_pc_e, van_z, num_main, total_constraints,
        );

        for &v in &trace_at_z {
            E::absorb_ext(&mut transcript, v);
        }
        for &v in &trace_at_gz {
            E::absorb_ext(&mut transcript, v);
        }
        for &v in &accum_at_z {
            E::absorb_ext(&mut transcript, v);
        }
        for &v in &accum_at_gz {
            E::absorb_ext(&mut transcript, v);
        }
        E::absorb_ext(&mut transcript, q_z);

        // ── Phase 5: DEEP ───────────────────────────────────────────────
        let num_deep = 2 * num_cols + 2 * NUM_ACCUM_COLS + 1;
        let deep: Vec<E::Ext> = (0..num_deep).map(|_| E::draw_ext(&mut transcript)).collect();
        let inv_z = E::deep_denom_inv_over_eval(gamma, &points);

        let d_evals: Vec<E::Ext> = (0..lde_size)
            .map(|i| {
                let next_i = E::rotation_index(log_eval, i, rotation_step);
                let mut d = E::Ext::ZERO;
                let mut ci = 0;
                for c in 0..num_cols {
                    d = d + deep[ci] * (E::Ext::from(trace_lde[c][i]) - trace_at_z[c]) * inv_z[i];
                    ci += 1;
                }
                for c in 0..num_cols {
                    d = d + deep[ci] * (E::Ext::from(trace_lde[c][next_i]) - trace_at_gz[c]) * inv_z[i];
                    ci += 1;
                }
                for c in 0..NUM_ACCUM_COLS {
                    d = d + deep[ci] * (accum_lde[c][i] - accum_at_z[c]) * inv_z[i];
                    ci += 1;
                }
                for c in 0..NUM_ACCUM_COLS {
                    d = d + deep[ci] * (accum_lde[c][next_i] - accum_at_gz[c]) * inv_z[i];
                    ci += 1;
                }
                d + deep[ci] * (q_evals[i] - q_z) * inv_z[i]
            })
            .collect();

        // ── Phase 6: FRI + queries ──────────────────────────────────────
        let fri_prover = E::fri_commit(&mut transcript, d_evals, log_eval, log_bound, &eval_tf);
        let half = lde_size / 2;
        let query_indices = transcript.draw_indices(NUM_QUERIES, half);

        let queries: Vec<QueryProof<E>> = query_indices
            .iter()
            .map(|&qi| {
                let positions = [
                    qi,
                    E::rotation_index(log_eval, qi, rotation_step),
                    qi + half,
                    E::rotation_index(log_eval, qi + half, rotation_step),
                ];
                QueryProof {
                    trace: positions
                        .iter()
                        .map(|&p| open_row::<E::Base>(&trace_tree, &trace_lde, &trace_salts, p))
                        .collect(),
                    accum: positions
                        .iter()
                        .map(|&p| open_row::<E::Ext>(&accum_tree, &accum_lde, &accum_salts, p))
                        .collect(),
                    quotient: [qi, qi + half]
                        .iter()
                        .map(|&p| open_scalar::<E::Ext>(&q_tree, &q_evals, &q_salts, p))
                        .collect(),
                }
            })
            .collect();

        let fri = E::fri_into_proof(fri_prover, &query_indices);

        ZkvmProof {
            trace_len,
            num_cols,
            num_accum_cols: NUM_ACCUM_COLS,
            trace_root,
            accum_root,
            quotient_root,
            trace_at_z,
            trace_at_gz,
            accum_at_z,
            accum_at_gz,
            q_z,
            gammas,
            alphas,
            fri,
            queries,
            program_hash: self.program_hash,
            public_inputs: self.public_inputs.clone(),
            public_outputs: self.public_outputs.clone(),
            entry_pc: self.entry_pc,
            program_rom: self.program_rom.clone(),
        }
    }
}

/// OOD evaluation of a masked base column set: `coeffs(pt) + van·mask(pt)`.
fn ood_base<E: Engine>(
    coeffs: &[Vec<E::Base>],
    mask: &[Vec<E::Base>],
    pt: E::Ood,
    van: E::Ext,
    num_cols: usize,
) -> Vec<E::Ext> {
    (0..num_cols)
        .map(|c| {
            let mut v = E::eval_at_ood(&coeffs[c], pt);
            if !mask[c].is_empty() {
                v = v + van * E::eval_at_ood(&mask[c], pt);
            }
            v
        })
        .collect()
}

fn ood_ext<E: Engine>(
    coeffs: &[Vec<E::Ext>],
    mask: &[Vec<E::Ext>],
    pt: E::Ood,
    van: E::Ext,
) -> Vec<E::Ext> {
    (0..NUM_ACCUM_COLS)
        .map(|c| E::eval_ext_at_ood(&coeffs[c], pt) + van * E::eval_ext_at_ood(&mask[c], pt))
        .collect()
}

/// The combined constraint quotient at the out-of-domain point, from the
/// claimed mask values — the verifier's identity and the prover's `q(gamma)`.
#[allow(clippy::too_many_arguments)]
pub fn quotient_identity<E: Engine>(
    log_trace: u32,
    gamma: E::Ood,
    trace_at_z: &[E::Ext],
    trace_at_gz: &[E::Ext],
    accum_at_z: &[E::Ext],
    accum_at_gz: &[E::Ext],
    cweights: &[E::Ext],
    gammas: &[E::Ext; 4],
    alphas: &[E::Ext; 4],
    entry_pc_e: E::Ext,
    van_z: E::Ext,
    num_main: usize,
    total_constraints: usize,
) -> E::Ext {
    let trace_len = 1usize << log_trace;
    let curr = TraceView::<E::Ext> { vals: trace_at_z.to_vec() };
    let next = TraceView::<E::Ext> { vals: trace_at_gz.to_vec() };
    let main_cv = eval_transition_constraints(&curr, &next);
    let accum_cv =
        permutation::eval_accum_constraints(&curr, &next, accum_at_z, accum_at_gz, gammas, alphas);

    let mut c_excepted = E::Ext::ZERO;
    for (j, &v) in main_cv.iter().enumerate() {
        c_excepted = c_excepted + cweights[j] * v;
    }
    let mut c_wrap = E::Ext::ZERO;
    for (j, &v) in accum_cv.iter().enumerate() {
        c_wrap = c_wrap + cweights[num_main + j] * v;
    }
    let p_last = E::trace_point(log_trace, trace_len - 1);
    let p_first = E::trace_point(log_trace, 0);
    let excl_z = E::point_vanishing_at_ood(p_last, gamma);
    let transition_q = (c_excepted * excl_z + c_wrap) * van_z.inverse();

    let one = E::Ext::ONE;
    let alpha_b = total_constraints;
    let mut b_first = E::Ext::ZERO;
    b_first = b_first + cweights[alpha_b] * trace_at_z[col::CLK];
    b_first = b_first + cweights[alpha_b + 1] * (trace_at_z[col::PC] - entry_pc_e);
    b_first = b_first + cweights[alpha_b + 2] * trace_at_z[col::HALT];
    b_first = b_first + cweights[alpha_b + 3] * trace_at_z[col::I_IN];
    b_first = b_first + cweights[alpha_b + 4] * trace_at_z[col::I_OUT];
    for ch in 0..NUM_CHANNELS {
        b_first = b_first + cweights[alpha_b + 5 + ch] * (accum_at_z[accum::REG + ch] - one);
        b_first = b_first + cweights[alpha_b + 5 + NUM_CHANNELS + ch] * (accum_at_z[accum::MEM + ch] - one);
        b_first = b_first + cweights[alpha_b + 5 + 2 * NUM_CHANNELS + ch] * accum_at_z[accum::PROG + ch];
        b_first = b_first + cweights[alpha_b + 5 + 3 * NUM_CHANNELS + ch] * accum_at_z[accum::PUB_IN + ch];
        b_first = b_first + cweights[alpha_b + 5 + 4 * NUM_CHANNELS + ch] * accum_at_z[accum::PUB_OUT + ch];
    }
    let rom_b = total_constraints + 5 + 5 * NUM_CHANNELS;
    b_first = b_first + cweights[rom_b] * trace_at_z[col::PROG];
    let smem_init = trace_at_z[col::SMEM + 4] * (one - trace_at_z[col::SMEM + 3]) * trace_at_z[col::SMEM + 1];
    b_first = b_first + cweights[rom_b + 1] * smem_init;
    let b_first_q = b_first * E::boundary_denom_inv_at_ood(p_first, gamma);

    let alpha_l = total_constraints + num_b_first();
    let b_last = cweights[alpha_l] * (trace_at_z[col::HALT] - one);
    let b_last_q = b_last * E::boundary_denom_inv_at_ood(p_last, gamma);

    transition_q + b_first_q + b_last_q
}

// ── row / scalar commitments ──────────────────────────────────────────
// Each row/scalar leaf is `SHA256(cell bytes || salt)`; the salt hides the
// small base-field cell values that an opening would otherwise reveal.

fn build_trace_view<E: Engine>(trace_lde: &[Vec<E::Base>], row: usize) -> TraceView<E::Ext> {
    TraceView {
        vals: trace_lde.iter().map(|c| E::Ext::from(c[row])).collect(),
    }
}

fn salts(count: usize, rng: &mut impl Rng) -> Vec<[u8; SALT_LEN]> {
    (0..count).map(|_| rng.r#gen::<[u8; SALT_LEN]>()).collect()
}

pub fn row_digest<F: Field>(values: &[F], salt: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    for v in values {
        h.update(v.to_bytes());
    }
    h.update(salt);
    h.finalize().to_vec()
}

pub fn scalar_digest<F: Field>(value: F, salt: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(value.to_bytes());
    h.update(salt);
    h.finalize().to_vec()
}

fn commit_rows<F: Field>(cols: &[Vec<F>], salts: &[[u8; SALT_LEN]]) -> MerkleTree {
    let n = cols[0].len();
    let leaves: Vec<Vec<u8>> = (0..n)
        .map(|i| row_digest(&cols.iter().map(|c| c[i]).collect::<Vec<_>>(), &salts[i]))
        .collect();
    MerkleTree::new(&leaves)
}

fn commit_scalars<F: Field>(evals: &[F], salts: &[[u8; SALT_LEN]]) -> MerkleTree {
    let leaves: Vec<Vec<u8>> = (0..evals.len())
        .map(|i| scalar_digest(evals[i], &salts[i]))
        .collect();
    MerkleTree::new(&leaves)
}

fn open_row<F: Field>(
    tree: &MerkleTree,
    cols: &[Vec<F>],
    salts: &[[u8; SALT_LEN]],
    index: usize,
) -> RowOpening<F> {
    RowOpening {
        values: cols.iter().map(|c| c[index]).collect(),
        salt: salts[index],
        path: tree.prove(index),
    }
}

fn open_scalar<F: Field>(
    tree: &MerkleTree,
    evals: &[F],
    salts: &[[u8; SALT_LEN]],
    index: usize,
) -> ScalarOpening<F> {
    ScalarOpening {
        value: evals[index],
        salt: salts[index],
        path: tree.prove(index),
    }
}

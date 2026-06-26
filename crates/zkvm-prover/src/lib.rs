//! STARK prover for the small custom VM, built on Toyni primitives.
//!
//! Two-phase commit: trace, then accumulator columns. Then a combined
//! quotient over (transition + accumulator + boundary) constraints, then
//! DEEP composition + FRI + queries.

use sha2::{Digest, Sha256};
use toyni::babybear::BabyBear;
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::math::fri::fri_fold_ext;
use toyni::math::polynomial::Polynomial;
use toyni::merkle::{MerkleProof, MerkleTree};
use toyni::transcript::FiatShamirTranscript;

use zkvm_air::{
    eval_transition_constraints, num_transition_constraints, permutation, TraceView,
};
use zkvm_core::{accum, col, NUM_ACCUM_COLS, NUM_CHANNELS, NUM_TRACE_COLS};

/// Evaluate a base-field-coefficient polynomial at an extension point.
fn eval_base_at_ext(coeffs: &[BabyBear], z: Ext) -> Ext {
    let mut acc = Ext::zero();
    for &c in coeffs.iter().rev() {
        acc = acc * z + Ext::from(c);
    }
    acc
}

/// Evaluate an extension-field-coefficient polynomial at an extension point.
fn eval_ext_at_ext(coeffs: &[Ext], z: Ext) -> Ext {
    let mut acc = Ext::zero();
    for &c in coeffs.iter().rev() {
        acc = acc * z + c;
    }
    acc
}

/// Blind a base-field column in place: P += Z_H * R with fresh random R.
/// Z_H = x^n - 1, so Z_H*R = x^n*R - R (subtract R low, add it back shifted n).
fn mask_poly_base(poly: &mut Vec<BabyBear>, n: usize, rng: &mut impl rand::Rng) {
    let r: Vec<BabyBear> = (0..MASK_DEGREE).map(|_| BabyBear::random(rng)).collect();
    if poly.len() < n + MASK_DEGREE {
        poly.resize(n + MASK_DEGREE, BabyBear::zero());
    }
    for i in 0..MASK_DEGREE {
        poly[i] = poly[i] - r[i];
        poly[n + i] = poly[n + i] + r[i];
    }
}

/// Extension-field analogue of `mask_poly_base` for the accumulator columns.
fn mask_poly_ext(poly: &mut Vec<Ext>, n: usize, rng: &mut impl rand::Rng) {
    let r: Vec<Ext> = (0..MASK_DEGREE).map(|_| Ext::random(rng)).collect();
    if poly.len() < n + MASK_DEGREE {
        poly.resize(n + MASK_DEGREE, Ext::zero());
    }
    for i in 0..MASK_DEGREE {
        poly[i] = poly[i] - r[i];
        poly[n + i] = poly[n + i] + r[i];
    }
}

/// Spot-check queries. The tested RS rate is at most 1/2 (~1 bit each), so 132
/// queries give ~2^-132.
pub const NUM_QUERIES: usize = 132;
/// LDE blowup. Masking pushes deg(D) up to ~8*n on the small test trace, so
/// blowup 16 keeps the FRI rate <= 1/2 (better on large traces).
pub const BLOWUP: usize = 16;
/// Max total degree of any AIR constraint: the register grand product (acc
/// times 3 slot factors) and the memory read-after-write check are degree 4.
pub const COMPOSITION_DEGREE: usize = 4;
/// Random blinding coefficients per committed column (X_hat = X + Z_H * R).
/// Covers every revealed evaluation: 2 openings per query + 2 OOD points.
pub const MASK_DEGREE: usize = 2 * NUM_QUERIES + 4;
/// Coset shift used for the LDE domain.
pub const COSET_SHIFT: u64 = 7;

/// FRI degree bound: smallest power of two above deg(D) of the masked DEEP
/// composition. The prover folds to a final layer of size lde/D_BOUND.
pub fn fri_degree_bound(trace_len: usize) -> usize {
    (COMPOSITION_DEGREE * (trace_len + MASK_DEGREE) - trace_len).next_power_of_two()
}

// ── proof data structures ─────────────────────────────────────────────

/// Opening of a base-field committed row (the trace).
#[derive(Debug, Clone)]
pub struct MerkleOpening {
    pub index: usize,
    pub values: Vec<BabyBear>,
    pub proof: MerkleProof,
}

/// Opening of an extension-field committed row (the accumulators).
#[derive(Debug, Clone)]
pub struct MerkleOpeningExt {
    pub index: usize,
    pub values: Vec<Ext>,
    pub proof: MerkleProof,
}

#[derive(Debug, Clone)]
pub struct QueryProof {
    pub index: usize,
    pub trace_opening: MerkleOpening,
    pub trace_opening_g: MerkleOpening,
    pub accum_opening: MerkleOpeningExt,
    pub accum_opening_g: MerkleOpeningExt,
    pub quotient_opening: ScalarOpening,
    pub deep_opening: ScalarOpening,
    pub deep_opening_pair: ScalarOpening,
    pub fri_openings: Vec<(ScalarOpening, ScalarOpening)>,
}

/// Opening of a single extension-field committed value (quotient / DEEP / FRI).
#[derive(Debug, Clone)]
pub struct ScalarOpening {
    pub index: usize,
    pub value: Ext,
    pub proof: MerkleProof,
}

#[derive(Debug)]
pub struct ZkvmProof {
    pub trace_len: usize,
    pub lde_size: usize,
    pub num_cols: usize,
    pub num_accum_cols: usize,

    pub trace_commitment: Vec<u8>,
    pub accum_commitment: Vec<u8>,
    pub quotient_commitment: Vec<u8>,

    pub trace_at_z: Vec<Ext>,
    pub trace_at_gz: Vec<Ext>,
    pub accum_at_z: Vec<Ext>,
    pub accum_at_gz: Vec<Ext>,
    pub q_z: Ext,

    pub gammas: [Ext; 4],
    pub alphas: [Ext; 4],

    pub fri_commitments: Vec<Vec<u8>>,
    /// Full final FRI layer (size lde/D_BOUND), sent in clear; the verifier
    /// checks it is constant. This is what enforces the low-degree bound.
    pub fri_final_layer: Vec<Ext>,
    pub query_proofs: Vec<QueryProof>,

    pub program_hash: [u8; 32],
    pub public_inputs: Vec<u32>,
    pub public_outputs: Vec<u32>,
    pub entry_pc: u32,

    /// Program ROM as a list of (addr, opcode, op_a, op_b, op_c) tuples,
    /// in canonical order. Used by the verifier to Lagrange-bind the
    /// program-table columns at the OOD point.
    pub program_rom: Vec<(u32, u32, u32, u32, u32)>,
}

// ── prover ────────────────────────────────────────────────────────────

pub struct ZkvmProver {
    columns: Vec<Vec<BabyBear>>,
    program_hash: [u8; 32],
    public_inputs: Vec<u32>,
    public_outputs: Vec<u32>,
    entry_pc: u32,
    program_rom: Vec<(u32, u32, u32, u32, u32)>,
}

impl ZkvmProver {
    pub fn new(
        columns: Vec<Vec<BabyBear>>,
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
        for c in &columns { assert_eq!(c.len(), n); }
        Self {
            columns, program_hash, public_inputs, public_outputs, entry_pc, program_rom,
        }
    }

    pub fn prove(&self, use_gpu: bool) -> ZkvmProof {
        let t_total = std::time::Instant::now();
        let num_cols = self.columns.len();
        let trace_len = self.columns[0].len();
        let lde_size = trace_len * BLOWUP;
        eprintln!(
            "[prove] start: trace_len={}, lde_size={}, num_cols={}, gpu={}",
            trace_len, lde_size, num_cols, use_gpu
        );

        let domain = BabyBearDomain::new(trace_len).with_gpu(use_gpu);
        let extended_domain = BabyBearDomain::new(lde_size).with_gpu(use_gpu);
        let shift = BabyBear::new(COSET_SHIFT);
        let shifted_domain = extended_domain.get_coset(shift);
        let g = domain.group_gen();
        let shifted_elements = shifted_domain.elements();

        // ── Phase 1: trace ───────────────────────────────────────────
        let t = std::time::Instant::now();
        eprintln!("[prove] [1/8] trace IFFT + LDE FFT ({} cols)...", num_cols);
        let mut trace_polys: Vec<Vec<BabyBear>> = self.columns.iter().map(|c| domain.ifft(c)).collect();
        // Blind the witness columns for zero-knowledge (X_hat = X + Z_H * R,
        // equal to X on the trace domain). The public, Lagrange-bound columns
        // (program ROM + public I/O tables) carry no witness and are checked
        // against public data at the OOD point, so they are left unblinded.
        let mut rng = rand::thread_rng();
        let public_cols = [
            col::PROG, col::PROG + 1, col::PROG + 2, col::PROG + 3, col::PROG + 4, col::PROG + 6,
            col::PUB_IN, col::PUB_IN + 1, col::PUB_IN + 2,
            col::PUB_OUT, col::PUB_OUT + 1, col::PUB_OUT + 2,
        ];
        for (i, p) in trace_polys.iter_mut().enumerate() {
            if !public_cols.contains(&i) {
                mask_poly_base(p, trace_len, &mut rng);
            }
        }
        let trace_lde: Vec<Vec<BabyBear>> = trace_polys.iter().map(|c| shifted_domain.fft(c)).collect();
        eprintln!("[prove] [1/8] FFTs done in {:.2?}", t.elapsed());
        let t = std::time::Instant::now();
        let trace_tree = build_row_merkle_tree(&trace_lde, lde_size);
        let trace_commitment = trace_tree.root().unwrap();
        eprintln!("[prove] [1/8] trace merkle done in {:.2?}", t.elapsed());

        let mut transcript = FiatShamirTranscript::new();
        transcript.absorb_commitment(&self.program_hash);
        transcript.absorb_field(BabyBear::from_u32(self.entry_pc));
        for &v in &self.public_inputs { transcript.absorb_field(BabyBear::from_u32(v)); }
        for &v in &self.public_outputs { transcript.absorb_field(BabyBear::from_u32(v)); }
        transcript.absorb_field(BabyBear::from_u32(self.public_inputs.len() as u32));
        transcript.absorb_field(BabyBear::from_u32(self.public_outputs.len() as u32));
        transcript.absorb_commitment(&trace_commitment);

        // ── Phase 2: accumulators ────────────────────────────────────
        // Lookup / permutation challenges are drawn from the extension field
        // for ~124-bit soundness.
        let gammas: [Ext; 4] = [
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
        ];
        let alphas: [Ext; 4] = [
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
            transcript.squeeze_ext_challenge(), transcript.squeeze_ext_challenge(),
        ];

        let t = std::time::Instant::now();
        eprintln!("[prove] [2/8] compute accumulators...");
        let accum_columns = permutation::compute_accumulators(&self.columns, &gammas, &alphas);
        assert_eq!(accum_columns.len(), NUM_ACCUM_COLS);
        eprintln!("[prove] [2/8] accumulators done in {:.2?}", t.elapsed());

        // Self-check: every constraint should evaluate to zero on the trace.
        if let Err(e) = zkvm_air::validate_full_trace(&self.columns, &accum_columns, &gammas, &alphas) {
            panic!("trace fails validation: {}", e);
        }

        let t = std::time::Instant::now();
        eprintln!("[prove] [2/8] accum IFFT + LDE FFT ({} cols)...", NUM_ACCUM_COLS);
        let mut accum_polys: Vec<Vec<Ext>> = accum_columns.iter().map(|c| domain.ifft_ext(c)).collect();
        for p in accum_polys.iter_mut() {
            mask_poly_ext(p, trace_len, &mut rng);
        }
        let accum_lde: Vec<Vec<Ext>> = accum_polys.iter().map(|c| shifted_domain.fft_ext(c)).collect();
        eprintln!("[prove] [2/8] accum FFTs done in {:.2?}", t.elapsed());
        let t = std::time::Instant::now();
        let accum_tree = build_row_merkle_tree_ext(&accum_lde, lde_size);
        let accum_commitment = accum_tree.root().unwrap();
        eprintln!("[prove] [2/8] accum merkle done in {:.2?}", t.elapsed());
        transcript.absorb_commitment(&accum_commitment);

        // ── Phase 3: combined constraint quotient ────────────────────
        let num_main = num_transition_constraints();
        let num_accum = permutation::num_accum_constraints();
        let total_constraints = num_main + num_accum;
        // Boundary first-row: 5 state cells (CLK, PC, HALT, I_IN, I_OUT)
        //   + 5 args × NUM_CHANNELS accumulator inits
        //   + ROM entry address (PROG addr[0] = 0)
        //   + sorted-memory init record (SORTED_BOUNDARY_ENTRY).
        // Boundary last-row: HALT = 1.
        let num_b_first = 5 + 5 * NUM_CHANNELS + 2;
        let num_b_last = 1;
        let total_with_boundary = total_constraints + num_b_first + num_b_last;

        let z_poly = Polynomial::new(domain.vanishing_poly_coeffs());
        let omega_n_minus_1 = g.pow((trace_len - 1) as u64);
        let entry_pc_f = Ext::from_u32(self.entry_pc);
        let omega_0 = BabyBear::one();

        let cweights: Vec<Ext> = (0..total_with_boundary)
            .map(|_| transcript.squeeze_ext_challenge())
            .collect();

        let t = std::time::Instant::now();
        eprintln!(
            "[prove] [3/8] constraint quotient over {} rows (single-threaded CPU)...",
            lde_size
        );
        let progress_step = (lde_size / 16).max(1);
        let mut q_evals = vec![Ext::zero(); lde_size];
        for i in 0..lde_size {
            if i > 0 && i % progress_step == 0 {
                eprintln!(
                    "[prove]   constraint loop {}/{}  ({:.0}%)  elapsed {:.2?}",
                    i, lde_size,
                    100.0 * i as f64 / lde_size as f64,
                    t.elapsed()
                );
            }
            let curr = build_trace_view(&trace_lde, i);
            let next_idx = (i + BLOWUP) % lde_size;
            let next = build_trace_view(&trace_lde, next_idx);

            let curr_acc: Vec<Ext> = accum_lde.iter().map(|c| c[i]).collect();
            let next_acc: Vec<Ext> = accum_lde.iter().map(|c| c[next_idx]).collect();

            let main_cv = eval_transition_constraints(&curr, &next);
            let accum_cv = permutation::eval_accum_constraints(
                &curr, &next, &curr_acc, &next_acc, &gammas, &alphas,
            );

            // Main constraints: all excepted (zeroed at last row).
            let mut c_excepted = Ext::zero();
            for (j, &v) in main_cv.iter().enumerate() {
                c_excepted = c_excepted + cweights[j] * v;
            }
            // Accum constraints: all wrap-around (hold everywhere).
            let mut c_wrap = Ext::zero();
            for (j, &v) in accum_cv.iter().enumerate() {
                c_wrap = c_wrap + cweights[num_main + j] * v;
            }

            // x, the exception factor and the vanishing value are base-field
            // (the domain is base); combine with the Ext constraint sums via
            // cheap base-scalar multiplies / a base inverse.
            let x = shifted_elements[i];
            let exception = x - omega_n_minus_1;
            let z_val_inv = z_poly.evaluate(x).inverse();
            let transition_q = (c_excepted.mul_base(exception) + c_wrap).mul_base(z_val_inv);

            // First-row boundaries.
            let alpha_b = total_constraints;
            let one = Ext::one();
            let mut b_first = Ext::zero();
            b_first = b_first + cweights[alpha_b]     * curr.col(col::CLK);
            b_first = b_first + cweights[alpha_b + 1] * (curr.col(col::PC) - entry_pc_f);
            b_first = b_first + cweights[alpha_b + 2] * curr.col(col::HALT);
            b_first = b_first + cweights[alpha_b + 3] * curr.col(col::I_IN);
            b_first = b_first + cweights[alpha_b + 4] * curr.col(col::I_OUT);
            // Per-channel accumulator initial values (4 GP→1, 12 LogUp→0).
            for ch in 0..NUM_CHANNELS {
                b_first = b_first + cweights[alpha_b + 5 + ch] * (curr_acc[accum::REG + ch] - one);
                b_first = b_first + cweights[alpha_b + 5 + NUM_CHANNELS + ch] * (curr_acc[accum::MEM + ch] - one);
                b_first = b_first + cweights[alpha_b + 5 + 2 * NUM_CHANNELS + ch] * curr_acc[accum::PROG + ch];
                b_first = b_first + cweights[alpha_b + 5 + 3 * NUM_CHANNELS + ch] * curr_acc[accum::PUB_IN + ch];
                b_first = b_first + cweights[alpha_b + 5 + 4 * NUM_CHANNELS + ch] * curr_acc[accum::PUB_OUT + ch];
            }
            // ROM entry address: first ROM row is PC 0 (ROM_ENTRY_WELLFORMED).
            let rom_b = total_constraints + 5 + 5 * NUM_CHANNELS;
            b_first = b_first + cweights[rom_b] * curr.col(col::PROG);
            // Sorted-memory init record: first entry, if a used read, has val 0.
            let smem_init = curr.col(col::SMEM + 4) * (one - curr.col(col::SMEM + 3)) * curr.col(col::SMEM + 1);
            b_first = b_first + cweights[rom_b + 1] * smem_init;
            let b_first_q = b_first.mul_base((x - omega_0).inverse());

            // Last-row boundary.
            let alpha_l = total_constraints + num_b_first;
            let b_last = cweights[alpha_l] * (curr.col(col::HALT) - one);
            let b_last_q = b_last.mul_base((x - omega_n_minus_1).inverse());

            q_evals[i] = transition_q + b_first_q + b_last_q;
        }
        eprintln!("[prove] [3/8] done in {:.2?}", t.elapsed());

        // ── Phase 4: commit quotient ─────────────────────────────────
        let t = std::time::Instant::now();
        eprintln!("[prove] [4/8] quotient merkle...");
        let q_tree = build_scalar_merkle_tree_ext(&q_evals);
        let quotient_commitment = q_tree.root().unwrap();
        eprintln!("[prove] [4/8] done in {:.2?}", t.elapsed());
        transcript.absorb_commitment(&quotient_commitment);

        // ── Phase 5: OOD ─────────────────────────────────────────────
        let t = std::time::Instant::now();
        eprintln!("[prove] [5/8] OOD evaluation...");
        let z = derive_z(&mut transcript, &extended_domain, &shifted_domain);
        let gz = z.mul_base(g);

        let trace_at_z: Vec<Ext> = trace_polys.iter().map(|c| eval_base_at_ext(c, z)).collect();
        let trace_at_gz: Vec<Ext> = trace_polys.iter().map(|c| eval_base_at_ext(c, gz)).collect();
        let accum_at_z: Vec<Ext> = accum_polys.iter().map(|c| eval_ext_at_ext(c, z)).collect();
        let accum_at_gz: Vec<Ext> = accum_polys.iter().map(|c| eval_ext_at_ext(c, gz)).collect();

        let q_coeffs = shifted_domain.ifft_ext(&q_evals);
        let q_z = eval_ext_at_ext(&q_coeffs, z);

        // Reconstruct q(z) and verify it matches.
        let curr_z = TraceView { vals: trace_at_z.clone() };
        let next_gz = TraceView { vals: trace_at_gz.clone() };
        let main_cv = eval_transition_constraints(&curr_z, &next_gz);
        let accum_cv = permutation::eval_accum_constraints(
            &curr_z, &next_gz, &accum_at_z, &accum_at_gz, &gammas, &alphas,
        );
        let mut c_excepted_z = Ext::zero();
        for (j, &v) in main_cv.iter().enumerate() {
            c_excepted_z = c_excepted_z + cweights[j] * v;
        }
        let mut c_wrap_z = Ext::zero();
        for (j, &v) in accum_cv.iter().enumerate() {
            c_wrap_z = c_wrap_z + cweights[num_main + j] * v;
        }
        let omega_nm1_e = Ext::from(omega_n_minus_1);
        let z_at_z = eval_base_at_ext(z_poly.coefficients(), z);
        let transition_q_z = (c_excepted_z * (z - omega_nm1_e) + c_wrap_z) * z_at_z.inverse();

        let one = Ext::one();
        let alpha_b = total_constraints;
        let mut b_first_z = Ext::zero();
        b_first_z = b_first_z + cweights[alpha_b]     * trace_at_z[col::CLK];
        b_first_z = b_first_z + cweights[alpha_b + 1] * (trace_at_z[col::PC] - entry_pc_f);
        b_first_z = b_first_z + cweights[alpha_b + 2] * trace_at_z[col::HALT];
        b_first_z = b_first_z + cweights[alpha_b + 3] * trace_at_z[col::I_IN];
        b_first_z = b_first_z + cweights[alpha_b + 4] * trace_at_z[col::I_OUT];
        for ch in 0..NUM_CHANNELS {
            b_first_z = b_first_z + cweights[alpha_b + 5 + ch] * (accum_at_z[accum::REG + ch] - one);
            b_first_z = b_first_z + cweights[alpha_b + 5 + NUM_CHANNELS + ch] * (accum_at_z[accum::MEM + ch] - one);
            b_first_z = b_first_z + cweights[alpha_b + 5 + 2 * NUM_CHANNELS + ch] * accum_at_z[accum::PROG + ch];
            b_first_z = b_first_z + cweights[alpha_b + 5 + 3 * NUM_CHANNELS + ch] * accum_at_z[accum::PUB_IN + ch];
            b_first_z = b_first_z + cweights[alpha_b + 5 + 4 * NUM_CHANNELS + ch] * accum_at_z[accum::PUB_OUT + ch];
        }
        let rom_b = total_constraints + 5 + 5 * NUM_CHANNELS;
        b_first_z = b_first_z + cweights[rom_b] * trace_at_z[col::PROG];
        let smem_init_z = trace_at_z[col::SMEM + 4] * (one - trace_at_z[col::SMEM + 3]) * trace_at_z[col::SMEM + 1];
        b_first_z = b_first_z + cweights[rom_b + 1] * smem_init_z;
        let b_first_qz = b_first_z * (z - one).inverse();

        let alpha_l = total_constraints + num_b_first;
        let b_last_z = cweights[alpha_l] * (trace_at_z[col::HALT] - one);
        let b_last_qz = b_last_z * (z - omega_nm1_e).inverse();

        let computed_q_z = transition_q_z + b_first_qz + b_last_qz;
        assert_eq!(computed_q_z, q_z, "OOD constraint check failed");
        eprintln!("[prove] [5/8] done in {:.2?}", t.elapsed());

        for &v in &trace_at_z { transcript.absorb_ext(v); }
        for &v in &trace_at_gz { transcript.absorb_ext(v); }
        for &v in &accum_at_z { transcript.absorb_ext(v); }
        for &v in &accum_at_gz { transcript.absorb_ext(v); }
        transcript.absorb_ext(q_z);

        // ── Phase 6: DEEP ────────────────────────────────────────────
        let num_deep_terms = 2 * num_cols + 2 * NUM_ACCUM_COLS + 1;
        let deep_coeffs: Vec<Ext> = (0..num_deep_terms)
            .map(|_| transcript.squeeze_ext_challenge())
            .collect();

        let t = std::time::Instant::now();
        eprintln!(
            "[prove] [6/8] DEEP composition over {} rows (single-threaded CPU)...",
            lde_size
        );
        let progress_step = (lde_size / 16).max(1);
        let d_evals: Vec<Ext> = (0..lde_size).map(|i| {
            if i > 0 && i % progress_step == 0 {
                eprintln!(
                    "[prove]   DEEP loop {}/{}  ({:.0}%)  elapsed {:.2?}",
                    i, lde_size,
                    100.0 * i as f64 / lde_size as f64,
                    t.elapsed()
                );
            }
            // x is base; the OOD points z, g·z are extension, so the
            // denominators (x - z) etc. are extension elements.
            let x = Ext::from(shifted_elements[i]);
            // All DEEP quotients use denominator (x - z); for the g-shifted
            // terms, T(g*x) - T(gz) vanishes at x = z, so they stay low-degree.
            let inv_x_z = (x - z).inverse();

            let mut d = Ext::zero();
            let mut ci = 0;
            for col_idx in 0..num_cols {
                d = d + deep_coeffs[ci] * (Ext::from(trace_lde[col_idx][i]) - trace_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            let next_i = (i + BLOWUP) % lde_size;
            for col_idx in 0..num_cols {
                d = d + deep_coeffs[ci] * (Ext::from(trace_lde[col_idx][next_i]) - trace_at_gz[col_idx]) * inv_x_z;
                ci += 1;
            }
            for col_idx in 0..NUM_ACCUM_COLS {
                d = d + deep_coeffs[ci] * (accum_lde[col_idx][i] - accum_at_z[col_idx]) * inv_x_z;
                ci += 1;
            }
            for col_idx in 0..NUM_ACCUM_COLS {
                d = d + deep_coeffs[ci] * (accum_lde[col_idx][next_i] - accum_at_gz[col_idx]) * inv_x_z;
                ci += 1;
            }
            d = d + deep_coeffs[ci] * (q_evals[i] - q_z) * inv_x_z;
            d
        }).collect();
        eprintln!("[prove] [6/8] done in {:.2?}", t.elapsed());

        // ── Phase 7: FRI ─────────────────────────────────────────────
        let t = std::time::Instant::now();
        eprintln!("[prove] [7/8] FRI commit + folding...");
        let mut fri_layers: Vec<Vec<Ext>> = Vec::new();
        let mut fri_trees: Vec<MerkleTree> = Vec::new();
        let mut fri_commitments: Vec<Vec<u8>> = Vec::new();

        fri_layers.push(d_evals.clone());
        let tree0 = build_scalar_merkle_tree_ext(&d_evals);
        let root0 = tree0.root().unwrap();
        transcript.absorb_commitment(&root0);
        fri_commitments.push(root0);
        fri_trees.push(tree0);

        let mut current = d_evals;
        let mut xs: Vec<BabyBear> = shifted_elements.clone();
        // Fold down to the degree-bound layer (size lde/D_BOUND). For an honest
        // proof that layer is constant; the verifier checks that, which enforces
        // the degree bound. The round count is fixed, not data-dependent.
        let final_layer_size = lde_size / fri_degree_bound(trace_len);
        while current.len() > final_layer_size {
            let beta = transcript.squeeze_ext_challenge();
            let folded = fri_fold_ext(&current, &xs, beta);
            xs.truncate(folded.len());
            for x in &mut xs { *x = *x * *x; }
            fri_layers.push(folded.clone());
            let tree = build_scalar_merkle_tree_ext(&folded);
            let root = tree.root().unwrap();
            transcript.absorb_commitment(&root);
            fri_commitments.push(root);
            fri_trees.push(tree);
            current = folded;
        }
        let fri_final_layer = current;
        eprintln!(
            "[prove] [7/8] done in {:.2?} ({} layers)",
            t.elapsed(),
            fri_layers.len()
        );

        // ── Phase 8: queries ─────────────────────────────────────────
        let t = std::time::Instant::now();
        eprintln!("[prove] [8/8] building {} query proofs...", NUM_QUERIES);
        let first_layer_half = fri_layers[0].len() / 2;
        let query_indices = transcript.squeeze_indices(NUM_QUERIES, first_layer_half);

        let mut query_proofs = Vec::with_capacity(NUM_QUERIES);
        for &qi in &query_indices {
            let idx_g = (qi + BLOWUP) % lde_size;

            let trace_opening = open_row_merkle(&trace_tree, &trace_lde, qi, num_cols);
            let trace_opening_g = open_row_merkle(&trace_tree, &trace_lde, idx_g, num_cols);
            let accum_opening = open_row_merkle_ext(&accum_tree, &accum_lde, qi, NUM_ACCUM_COLS);
            let accum_opening_g = open_row_merkle_ext(&accum_tree, &accum_lde, idx_g, NUM_ACCUM_COLS);
            let quotient_opening = open_scalar_merkle_ext(&q_tree, &q_evals, qi);

            let half0 = fri_layers[0].len() / 2;
            let deep_opening = open_scalar_merkle_ext(&fri_trees[0], &fri_layers[0], qi);
            let deep_opening_pair = open_scalar_merkle_ext(&fri_trees[0], &fri_layers[0], qi + half0);

            let mut fri_openings = Vec::new();
            let mut idx = qi;
            for layer_idx in 1..fri_layers.len() - 1 {
                let half = fri_layers[layer_idx].len() / 2;
                idx = idx % half;
                let op = open_scalar_merkle_ext(&fri_trees[layer_idx], &fri_layers[layer_idx], idx);
                let op_pair = open_scalar_merkle_ext(&fri_trees[layer_idx], &fri_layers[layer_idx], idx + half);
                fri_openings.push((op, op_pair));
            }

            query_proofs.push(QueryProof {
                index: qi,
                trace_opening, trace_opening_g,
                accum_opening, accum_opening_g,
                quotient_opening,
                deep_opening, deep_opening_pair,
                fri_openings,
            });
        }
        eprintln!("[prove] [8/8] done in {:.2?}", t.elapsed());
        eprintln!("[prove] TOTAL: {:.2?}", t_total.elapsed());

        ZkvmProof {
            trace_len, lde_size, num_cols,
            num_accum_cols: NUM_ACCUM_COLS,
            trace_commitment, accum_commitment, quotient_commitment,
            trace_at_z, trace_at_gz, accum_at_z, accum_at_gz, q_z,
            gammas, alphas,
            fri_commitments, fri_final_layer, query_proofs,
            program_hash: self.program_hash,
            public_inputs: self.public_inputs.clone(),
            public_outputs: self.public_outputs.clone(),
            entry_pc: self.entry_pc,
            program_rom: self.program_rom.clone(),
        }
    }
}

// ── helpers ───────────────────────────────────────────────────────────

fn build_trace_view(trace_lde: &[Vec<BabyBear>], row: usize) -> TraceView {
    // Lift the base-field trace row into the extension field for constraint
    // evaluation (base embeds as a + 0X + 0X^2 + 0X^3).
    TraceView { vals: trace_lde.iter().map(|c| Ext::from(c[row])).collect() }
}

fn build_row_merkle_tree(cols: &[Vec<BabyBear>], lde_size: usize) -> MerkleTree {
    let num_cols = cols.len();
    let leaves: Vec<Vec<u8>> = (0..lde_size).map(|i| {
        let mut h = Sha256::new();
        for col in 0..num_cols {
            h.update(cols[col][i].to_bytes());
        }
        h.finalize().to_vec()
    }).collect();
    MerkleTree::new(leaves)
}

fn build_row_merkle_tree_ext(cols: &[Vec<Ext>], lde_size: usize) -> MerkleTree {
    let num_cols = cols.len();
    let leaves: Vec<Vec<u8>> = (0..lde_size).map(|i| {
        let mut h = Sha256::new();
        for col in 0..num_cols {
            h.update(cols[col][i].to_bytes());
        }
        h.finalize().to_vec()
    }).collect();
    MerkleTree::new(leaves)
}

fn build_scalar_merkle_tree_ext(evals: &[Ext]) -> MerkleTree {
    MerkleTree::new(evals.iter().map(|v| v.to_bytes().to_vec()).collect())
}

fn open_row_merkle(tree: &MerkleTree, cols: &[Vec<BabyBear>], index: usize, num_cols: usize) -> MerkleOpening {
    let proof = tree.get_proof(index).expect("Index out of bounds");
    let values: Vec<BabyBear> = (0..num_cols).map(|c| cols[c][index]).collect();
    MerkleOpening { index, values, proof }
}

fn open_row_merkle_ext(tree: &MerkleTree, cols: &[Vec<Ext>], index: usize, num_cols: usize) -> MerkleOpeningExt {
    let proof = tree.get_proof(index).expect("Index out of bounds");
    let values: Vec<Ext> = (0..num_cols).map(|c| cols[c][index]).collect();
    MerkleOpeningExt { index, values, proof }
}

fn open_scalar_merkle_ext(tree: &MerkleTree, evals: &[Ext], index: usize) -> ScalarOpening {
    let proof = tree.get_proof(index).expect("Index out of bounds");
    ScalarOpening { index, value: evals[index], proof }
}

/// Derive the out-of-domain point in the extension field. A random extension
/// element is outside the base evaluation domain unless it happens to be a base
/// element (negligible), so we only need to reject the base case to guarantee
/// z, g·z ∉ domain (keeping the DEEP denominators invertible).
fn derive_z(
    transcript: &mut FiatShamirTranscript,
    _extended_domain: &BabyBearDomain,
    _shifted_domain: &BabyBearDomain,
) -> Ext {
    loop {
        let z = transcript.squeeze_ext_challenge();
        if !z.is_base() {
            return z;
        }
    }
}

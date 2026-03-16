/// Grand product permutation arguments with 4 parallel challenge pairs
/// for ~2^{-60} soundness (instead of ~2^{-15} with a single pair).
///
/// Each argument runs 4 independent accumulators with (γ_k, α_k):
///   Z_k[0] = 1
///   Z_k[i+1] = Z_k[i] * Π(exec_tuple + γ_k) / Π(sorted_tuple + γ_k)
/// A cheating prover must fool all 4 independently: Pr ≤ (n/|F|)^4 ≈ 2^{-60}.

use toyni::babybear::BabyBear;
use zkvm_core::trace::col;

use crate::TraceView;

/// Accumulator column indices within the accumulator trace (19 total).
pub const ACCUM_MEM_0: usize = 0;
pub const ACCUM_MEM_1: usize = 1;
pub const ACCUM_MEM_2: usize = 2;
pub const ACCUM_MEM_3: usize = 3;
pub const ACCUM_REG_0: usize = 4;
pub const ACCUM_REG_1: usize = 5;
pub const ACCUM_REG_2: usize = 6;
pub const ACCUM_REG_3: usize = 7;
pub const ACCUM_FETCH_0: usize = 8;
pub const ACCUM_FETCH_1: usize = 9;
pub const ACCUM_FETCH_2: usize = 10;
pub const ACCUM_FETCH_3: usize = 11;
pub const ACCUM_RANGE: usize = 12;
pub const ACCUM_HELPER_0: usize = 13;
pub const ACCUM_HELPER_1: usize = 14;
pub const ACCUM_HELPER_2: usize = 15;
pub const ACCUM_HELPER_3: usize = 16;
pub const ACCUM_HELPER_4: usize = 17;
pub const ACCUM_HELPER_5: usize = 18;

/// Compress a tuple of field elements into a single element using powers of α.
fn compress(vals: &[BabyBear], alpha: BabyBear) -> BabyBear {
    let mut result = BabyBear::zero();
    let mut alpha_pow = BabyBear::one();
    for &v in vals {
        result = result + v * alpha_pow;
        alpha_pow = alpha_pow * alpha;
    }
    result
}

/// Compute all 19 accumulator columns from the main trace columns.
///
/// Uses 4 independent (γ, α) pairs for mem, reg, fetch arguments.
pub fn compute_accumulators(
    columns: &[Vec<BabyBear>],
    gammas: &[BabyBear; 4],
    alphas: &[BabyBear; 4],
) -> Vec<Vec<BabyBear>> {
    let n = columns[0].len();

    // 12 parallel GP/LogUp accumulators: 4 mem + 4 reg + 4 fetch
    let mut accums: Vec<Vec<BabyBear>> = (0..12).map(|_| vec![BabyBear::zero(); n]).collect();

    // Initialize all 12 accumulators to 1
    for k in 0..12 {
        accums[k][0] = BabyBear::one();
    }

    for i in 0..n - 1 {
        for run in 0..4 {
            let gamma = gammas[run];
            let alpha = alphas[run];

            // ── Memory accumulator ──
            let exec_mem = compress(&[
                columns[col::MEM_ADDR][i],
                columns[col::MEM_VAL][i],
                columns[col::CLK][i],
                columns[col::IS_STORE][i],
            ], alpha);
            let sorted_mem = compress(&[
                columns[col::SORTED_MEM_ADDR][i],
                columns[col::SORTED_MEM_VAL][i],
                columns[col::SORTED_MEM_CLK][i],
                columns[col::SORTED_MEM_IS_WRITE][i],
            ], alpha);
            let num = exec_mem + gamma;
            let den = sorted_mem + gamma;
            accums[ACCUM_MEM_0 + run][i + 1] = accums[ACCUM_MEM_0 + run][i] * num * den.inverse();

            // ── Register accumulator ──
            let exec_rs1 = compress(&[
                columns[col::RS1_IDX][i], columns[col::RS1_VAL][i],
                columns[col::CLK][i], BabyBear::zero(),
            ], alpha);
            let exec_rs2 = compress(&[
                columns[col::RS2_IDX][i], columns[col::RS2_VAL][i],
                columns[col::CLK][i], BabyBear::zero(),
            ], alpha);
            let exec_rd = compress(&[
                columns[col::RD_IDX][i], columns[col::RD_VAL][i],
                columns[col::CLK][i], BabyBear::one(),
            ], alpha);
            let sorted_a = compress(&[
                columns[col::SORTED_REG_A_IDX][i], columns[col::SORTED_REG_A_VAL][i],
                columns[col::SORTED_REG_A_CLK][i], columns[col::SORTED_REG_A_IS_WRITE][i],
            ], alpha);
            let sorted_b = compress(&[
                columns[col::SORTED_REG_B_IDX][i], columns[col::SORTED_REG_B_VAL][i],
                columns[col::SORTED_REG_B_CLK][i], columns[col::SORTED_REG_B_IS_WRITE][i],
            ], alpha);
            let sorted_c = compress(&[
                columns[col::SORTED_REG_C_IDX][i], columns[col::SORTED_REG_C_VAL][i],
                columns[col::SORTED_REG_C_CLK][i], columns[col::SORTED_REG_C_IS_WRITE][i],
            ], alpha);
            let reg_num = (exec_rs1 + gamma) * (exec_rs2 + gamma) * (exec_rd + gamma);
            let reg_den = (sorted_a + gamma) * (sorted_b + gamma) * (sorted_c + gamma);
            accums[ACCUM_REG_0 + run][i + 1] = accums[ACCUM_REG_0 + run][i] * reg_num * reg_den.inverse();

            // ── Fetch accumulator (LogUp) ──
            let exec_fetch = compress(&[
                columns[col::PC][i], columns[col::INSTRUCTION][i],
            ], alpha);
            let prog_entry = compress(&[
                columns[col::PROG_ADDR][i], columns[col::PROG_INSTR][i],
            ], alpha);
            let mult = columns[col::PROG_MULT][i];
            let exec_term = (exec_fetch + gamma).inverse();
            let rom_term = if mult.is_zero() {
                BabyBear::zero()
            } else {
                mult * (prog_entry + gamma).inverse()
            };
            accums[ACCUM_FETCH_0 + run][i + 1] = accums[ACCUM_FETCH_0 + run][i] + exec_term - rom_term;
        }
    }

    // ── LogUp range check: 1 accumulator + 6 helper columns ────────
    // Groups 0-3: value limbs (LIMB_START + group*4 + k)
    // Group 4: ordering limbs (ORDERING_MEM_LO/HI, ORDERING_REG_A_LO/HI)
    // Group 5: ordering limbs (ORDERING_REG_B_LO/HI, ORDERING_REG_C_LO/HI)
    let gamma_range = gammas[0] + alphas[0];

    let ordering_group_4 = [
        col::ORDERING_MEM_LO, col::ORDERING_MEM_HI,
        col::ORDERING_REG_A_LO, col::ORDERING_REG_A_HI,
    ];
    let ordering_group_5 = [
        col::ORDERING_REG_B_LO, col::ORDERING_REG_B_HI,
        col::ORDERING_REG_C_LO, col::ORDERING_REG_C_HI,
    ];

    let mut range_z = vec![BabyBear::zero(); n];
    range_z[0] = BabyBear::one();
    let mut helpers: Vec<Vec<BabyBear>> = (0..6).map(|_| vec![BabyBear::zero(); n]).collect();

    for i in 0..n {
        // Groups 0-3: standard value limbs
        for group in 0..4 {
            let mut limb_sum = BabyBear::zero();
            for k in 0..4 {
                let limb = columns[col::LIMB_START + group * 4 + k][i];
                limb_sum = limb_sum + (limb + gamma_range).inverse();
            }
            helpers[group][i] = limb_sum;
        }
        // Group 4: ordering limbs (mem + reg A)
        {
            let mut limb_sum = BabyBear::zero();
            for &c in &ordering_group_4 {
                limb_sum = limb_sum + (columns[c][i] + gamma_range).inverse();
            }
            helpers[4][i] = limb_sum;
        }
        // Group 5: ordering limbs (reg B + reg C)
        {
            let mut limb_sum = BabyBear::zero();
            for &c in &ordering_group_5 {
                limb_sum = limb_sum + (columns[c][i] + gamma_range).inverse();
            }
            helpers[5][i] = limb_sum;
        }

        if i < n - 1 {
            let table_val = columns[col::RANGE_TABLE_VAL][i];
            let mult = columns[col::RANGE_MULT][i];
            let table_term = table_val + gamma_range;
            let total_helper = helpers[0][i] + helpers[1][i] + helpers[2][i]
                + helpers[3][i] + helpers[4][i] + helpers[5][i];
            range_z[i + 1] = range_z[i] + total_helper - mult * table_term.inverse();
        }
    }

    // Build the 19-column result
    let mut result = accums; // 12 columns
    result.push(range_z);       // index 12
    result.push(helpers.remove(0)); // index 13
    result.push(helpers.remove(0)); // index 14
    result.push(helpers.remove(0)); // index 15
    result.push(helpers.remove(0)); // index 16
    result.push(helpers.remove(0)); // index 17 (ACCUM_HELPER_4)
    result.push(helpers.remove(0)); // index 18 (ACCUM_HELPER_5)
    result
}

/// Evaluate accumulator transition constraints.
///
/// Returns 39 constraints:
/// - 0-3:   4 memory GP transitions (wrap-around)
/// - 4-7:   4 register GP transitions (wrap-around)
/// - 8-11:  4 fetch LogUp transitions (wrap-around)
/// - 12-15: sorted memory read-after-write (excepted)
/// - 16-27: sorted register read-after-write (excepted)
/// - 28:    LogUp Z transition (wrap-around)
/// - 29-32: LogUp helper constraints 0-3 (wrap-around)
/// - 33:    Memory ordering reconstruction (excepted)
/// - 34-36: Register ordering reconstruction A/B/C (excepted)
/// - 37-38: LogUp helper constraints 4-5 (wrap-around)
pub fn eval_accum_constraints(
    curr: &TraceView,
    next: &TraceView,
    curr_accum: &[BabyBear],
    next_accum: &[BabyBear],
    gammas: &[BabyBear; 4],
    alphas: &[BabyBear; 4],
) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    // ── 4 Memory accumulator transitions (indices 0-3) ────────────
    for run in 0..4 {
        let gamma = gammas[run];
        let alpha = alphas[run];
        let exec_mem = compress(&[
            curr.col(col::MEM_ADDR), curr.col(col::MEM_VAL),
            curr.col(col::CLK), curr.col(col::IS_STORE),
        ], alpha);
        let sorted_mem = compress(&[
            curr.col(col::SORTED_MEM_ADDR), curr.col(col::SORTED_MEM_VAL),
            curr.col(col::SORTED_MEM_CLK), curr.col(col::SORTED_MEM_IS_WRITE),
        ], alpha);
        constraints.push(
            next_accum[ACCUM_MEM_0 + run] * (sorted_mem + gamma)
            - curr_accum[ACCUM_MEM_0 + run] * (exec_mem + gamma)
        );
    }

    // ── 4 Register accumulator transitions (indices 4-7) ──────────
    for run in 0..4 {
        let gamma = gammas[run];
        let alpha = alphas[run];
        let exec_rs1 = compress(&[
            curr.col(col::RS1_IDX), curr.col(col::RS1_VAL),
            curr.col(col::CLK), BabyBear::zero(),
        ], alpha);
        let exec_rs2 = compress(&[
            curr.col(col::RS2_IDX), curr.col(col::RS2_VAL),
            curr.col(col::CLK), BabyBear::zero(),
        ], alpha);
        let exec_rd = compress(&[
            curr.col(col::RD_IDX), curr.col(col::RD_VAL),
            curr.col(col::CLK), BabyBear::one(),
        ], alpha);
        let sorted_a = compress(&[
            curr.col(col::SORTED_REG_A_IDX), curr.col(col::SORTED_REG_A_VAL),
            curr.col(col::SORTED_REG_A_CLK), curr.col(col::SORTED_REG_A_IS_WRITE),
        ], alpha);
        let sorted_b = compress(&[
            curr.col(col::SORTED_REG_B_IDX), curr.col(col::SORTED_REG_B_VAL),
            curr.col(col::SORTED_REG_B_CLK), curr.col(col::SORTED_REG_B_IS_WRITE),
        ], alpha);
        let sorted_c = compress(&[
            curr.col(col::SORTED_REG_C_IDX), curr.col(col::SORTED_REG_C_VAL),
            curr.col(col::SORTED_REG_C_CLK), curr.col(col::SORTED_REG_C_IS_WRITE),
        ], alpha);
        constraints.push(
            next_accum[ACCUM_REG_0 + run]
                * (sorted_a + gamma) * (sorted_b + gamma) * (sorted_c + gamma)
            - curr_accum[ACCUM_REG_0 + run]
                * (exec_rs1 + gamma) * (exec_rs2 + gamma) * (exec_rd + gamma)
        );
    }

    // ── 4 Fetch accumulator transitions (LogUp, indices 8-11) ─────
    for run in 0..4 {
        let gamma = gammas[run];
        let alpha = alphas[run];
        let exec_fetch = compress(&[
            curr.col(col::PC), curr.col(col::INSTRUCTION),
        ], alpha);
        let prog_entry = compress(&[
            curr.col(col::PROG_ADDR), curr.col(col::PROG_INSTR),
        ], alpha);
        let prog_mult = curr.col(col::PROG_MULT);
        constraints.push(
            (next_accum[ACCUM_FETCH_0 + run] - curr_accum[ACCUM_FETCH_0 + run])
                * (exec_fetch + gamma) * (prog_entry + gamma)
            - (prog_entry + gamma)
            + prog_mult * (exec_fetch + gamma)
        );
    }

    // ── Sorted memory read-after-write (indices 12-15) ────────────
    {
        let next_addr = next.col(col::SORTED_MEM_ADDR);
        let curr_addr = curr.col(col::SORTED_MEM_ADDR);
        let n_same = next.col(col::SORTED_MEM_SAME_ADDR);
        let n_dinv = next.col(col::SORTED_MEM_DIFF_INV);

        // same_addr is boolean
        constraints.push(n_same * (n_same - BabyBear::one()));
        // When same_addr=1: addresses match
        constraints.push(n_same * (next_addr - curr_addr));
        // When same_addr=0: (addr_diff) * diff_inv = 1
        constraints.push(
            (BabyBear::one() - n_same)
            * (BabyBear::one() - (next_addr - curr_addr) * n_dinv)
        );
        // Read-after-write: same addr + next is read → values match
        let n_is_write = next.col(col::SORTED_MEM_IS_WRITE);
        let n_val = next.col(col::SORTED_MEM_VAL);
        let c_val = curr.col(col::SORTED_MEM_VAL);
        constraints.push(
            n_same * (BabyBear::one() - n_is_write) * (n_val - c_val)
        );
    }

    // ── Sorted register read-after-write (cross-slot, indices 16-27) ─
    {
        // Transition: B[i] after A[i]
        let prev_idx = curr.col(col::SORTED_REG_A_IDX);
        let prev_val = curr.col(col::SORTED_REG_A_VAL);
        let next_idx_val = curr.col(col::SORTED_REG_B_IDX);
        let next_val = curr.col(col::SORTED_REG_B_VAL);
        let next_is_write = curr.col(col::SORTED_REG_B_IS_WRITE);
        let s = curr.col(col::SORTED_REG_A_SAME_IDX);
        let d = curr.col(col::SORTED_REG_A_DIFF_INV);

        constraints.push(s * (s - BabyBear::one()));
        constraints.push(s * (next_idx_val - prev_idx));
        constraints.push((BabyBear::one() - s) * (BabyBear::one() - (next_idx_val - prev_idx) * d));
        constraints.push(s * (BabyBear::one() - next_is_write) * (next_val - prev_val) * next_idx_val);
    }
    {
        // Transition: C[i] after B[i]
        let prev_idx = curr.col(col::SORTED_REG_B_IDX);
        let prev_val = curr.col(col::SORTED_REG_B_VAL);
        let next_idx_val = curr.col(col::SORTED_REG_C_IDX);
        let next_val = curr.col(col::SORTED_REG_C_VAL);
        let next_is_write = curr.col(col::SORTED_REG_C_IS_WRITE);
        let s = curr.col(col::SORTED_REG_B_SAME_IDX);
        let d = curr.col(col::SORTED_REG_B_DIFF_INV);

        constraints.push(s * (s - BabyBear::one()));
        constraints.push(s * (next_idx_val - prev_idx));
        constraints.push((BabyBear::one() - s) * (BabyBear::one() - (next_idx_val - prev_idx) * d));
        constraints.push(s * (BabyBear::one() - next_is_write) * (next_val - prev_val) * next_idx_val);
    }
    {
        // Transition: A[i+1] after C[i]
        let prev_idx = curr.col(col::SORTED_REG_C_IDX);
        let prev_val = curr.col(col::SORTED_REG_C_VAL);
        let next_idx_val = next.col(col::SORTED_REG_A_IDX);
        let next_val = next.col(col::SORTED_REG_A_VAL);
        let next_is_write = next.col(col::SORTED_REG_A_IS_WRITE);
        let s = curr.col(col::SORTED_REG_C_SAME_IDX);
        let d = curr.col(col::SORTED_REG_C_DIFF_INV);

        constraints.push(s * (s - BabyBear::one()));
        constraints.push(s * (next_idx_val - prev_idx));
        constraints.push((BabyBear::one() - s) * (BabyBear::one() - (next_idx_val - prev_idx) * d));
        constraints.push(s * (BabyBear::one() - next_is_write) * (next_val - prev_val) * next_idx_val);
    }

    // ── LogUp range check (indices 28-32) ─────────────────────────
    let gamma_range = gammas[0] + alphas[0];

    // Z transition (index 28) — includes all 6 helper groups
    {
        let z_curr = curr_accum[ACCUM_RANGE];
        let z_next = next_accum[ACCUM_RANGE];
        let h0 = curr_accum[ACCUM_HELPER_0];
        let h1 = curr_accum[ACCUM_HELPER_1];
        let h2 = curr_accum[ACCUM_HELPER_2];
        let h3 = curr_accum[ACCUM_HELPER_3];
        let h4 = curr_accum[ACCUM_HELPER_4];
        let h5 = curr_accum[ACCUM_HELPER_5];
        let table_val = curr.col(col::RANGE_TABLE_VAL);
        let mult = curr.col(col::RANGE_MULT);
        let tg = table_val + gamma_range;

        constraints.push(
            (z_next - z_curr - h0 - h1 - h2 - h3 - h4 - h5) * tg + mult
        );
    }

    // Helper constraints 0-3 (indices 29-32)
    for group in 0..4usize {
        let h_g = curr_accum[ACCUM_HELPER_0 + group];

        let mut ls = [BabyBear::zero(); 4];
        for k in 0..4 {
            ls[k] = curr.col(col::LIMB_START + group * 4 + k) + gamma_range;
        }

        let prod_all = ls[0] * ls[1] * ls[2] * ls[3];
        let sum_excl = ls[1] * ls[2] * ls[3]
            + ls[0] * ls[2] * ls[3]
            + ls[0] * ls[1] * ls[3]
            + ls[0] * ls[1] * ls[2];

        constraints.push(h_g * prod_all - sum_excl);
    }

    // ── Ordering reconstruction constraints (indices 33-36, excepted) ─
    // Decompose diff into 16-bit limbs to enforce diff ∈ [0, 2^32).
    // diff = lo + hi * 65536 with lo, hi range-checked to [0, 65535].
    let c64k = BabyBear::new(65536);
    let one = BabyBear::one();

    // Memory ordering (index 33):
    {
        let n_same = next.col(col::SORTED_MEM_SAME_ADDR);
        let diff = n_same * (next.col(col::SORTED_MEM_CLK) - curr.col(col::SORTED_MEM_CLK))
            + (one - n_same) * (next.col(col::SORTED_MEM_ADDR) - curr.col(col::SORTED_MEM_ADDR));
        let lo = curr.col(col::ORDERING_MEM_LO);
        let hi = curr.col(col::ORDERING_MEM_HI);
        constraints.push(diff - lo - hi * c64k);
    }

    // Register A ordering (index 34): B[i] vs A[i]
    {
        let s = curr.col(col::SORTED_REG_A_SAME_IDX);
        let diff = s * (curr.col(col::SORTED_REG_B_CLK) - curr.col(col::SORTED_REG_A_CLK))
            + (one - s) * (curr.col(col::SORTED_REG_B_IDX) - curr.col(col::SORTED_REG_A_IDX));
        let lo = curr.col(col::ORDERING_REG_A_LO);
        let hi = curr.col(col::ORDERING_REG_A_HI);
        constraints.push(diff - lo - hi * c64k);
    }

    // Register B ordering (index 35): C[i] vs B[i]
    {
        let s = curr.col(col::SORTED_REG_B_SAME_IDX);
        let diff = s * (curr.col(col::SORTED_REG_C_CLK) - curr.col(col::SORTED_REG_B_CLK))
            + (one - s) * (curr.col(col::SORTED_REG_C_IDX) - curr.col(col::SORTED_REG_B_IDX));
        let lo = curr.col(col::ORDERING_REG_B_LO);
        let hi = curr.col(col::ORDERING_REG_B_HI);
        constraints.push(diff - lo - hi * c64k);
    }

    // Register C ordering (index 36): A[i+1] vs C[i]
    {
        let s = curr.col(col::SORTED_REG_C_SAME_IDX);
        let diff = s * (next.col(col::SORTED_REG_A_CLK) - curr.col(col::SORTED_REG_C_CLK))
            + (one - s) * (next.col(col::SORTED_REG_A_IDX) - curr.col(col::SORTED_REG_C_IDX));
        let lo = curr.col(col::ORDERING_REG_C_LO);
        let hi = curr.col(col::ORDERING_REG_C_HI);
        constraints.push(diff - lo - hi * c64k);
    }

    // Note: First-write constraints (memory + register) are deferred to a follow-up.
    // They require trace engineering (injecting initialization rows for input tape
    // and register values) to avoid false violations on valid programs.

    // ── Helper constraints 4-5 (indices 37-38, wrap-around) ──────
    // Group 4: ORDERING_MEM_LO/HI, ORDERING_REG_A_LO/HI
    {
        let h_g = curr_accum[ACCUM_HELPER_4];
        let ls = [
            curr.col(col::ORDERING_MEM_LO) + gamma_range,
            curr.col(col::ORDERING_MEM_HI) + gamma_range,
            curr.col(col::ORDERING_REG_A_LO) + gamma_range,
            curr.col(col::ORDERING_REG_A_HI) + gamma_range,
        ];
        let prod_all = ls[0] * ls[1] * ls[2] * ls[3];
        let sum_excl = ls[1] * ls[2] * ls[3]
            + ls[0] * ls[2] * ls[3]
            + ls[0] * ls[1] * ls[3]
            + ls[0] * ls[1] * ls[2];
        constraints.push(h_g * prod_all - sum_excl);
    }

    // Group 5: ORDERING_REG_B_LO/HI, ORDERING_REG_C_LO/HI
    {
        let h_g = curr_accum[ACCUM_HELPER_5];
        let ls = [
            curr.col(col::ORDERING_REG_B_LO) + gamma_range,
            curr.col(col::ORDERING_REG_B_HI) + gamma_range,
            curr.col(col::ORDERING_REG_C_LO) + gamma_range,
            curr.col(col::ORDERING_REG_C_HI) + gamma_range,
        ];
        let prod_all = ls[0] * ls[1] * ls[2] * ls[3];
        let sum_excl = ls[1] * ls[2] * ls[3]
            + ls[0] * ls[2] * ls[3]
            + ls[0] * ls[1] * ls[3]
            + ls[0] * ls[1] * ls[2];
        constraints.push(h_g * prod_all - sum_excl);
    }

    constraints
}

/// Number of accumulator constraints per transition.
pub fn num_accum_constraints() -> usize {
    // 4 memory GP + 4 register GP + 4 fetch LogUp = 12
    // + 4 sorted memory + 12 sorted register = 16
    // + 1 LogUp Z + 4 LogUp helpers 0-3 = 5
    // + 4 ordering reconstruction = 4
    // + 2 LogUp helpers 4-5 = 2
    // Total: 39
    12 + 16 + 5 + 4 + 2
}

/// Returns true if accum constraint at index `j` is a wrap-around constraint
/// (must hold at ALL rows including the last, for accumulator closure).
/// Indices 0-11: permutation transitions (wrap).
/// Indices 12-27: sorted table constraints (excepted).
/// Indices 28-32: LogUp range check (wrap).
/// Indices 33-36: ordering reconstruction (excepted).
/// Indices 37-38: LogUp helpers 4-5 (wrap).
pub fn is_wrap_constraint(j: usize) -> bool {
    j < 12 || (j >= 28 && j <= 32) || j >= 37
}

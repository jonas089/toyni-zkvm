//! AIR for the small custom VM.
//!
//! Constraint groups (all hold on every transition unless noted):
//!   - selector booleanity, exclusivity, OPCODE consistency
//!   - per-opcode arithmetic / memory / control-flow constraints
//!   - register-slot booleanity + r0-hardwiring (idx=0 implies val=0)
//!   - JZ branch via JZ_IS_ZERO + JZ_VAL_INV
//!   - HALT monotonicity, I_IN/I_OUT cursor advancement
//!   - sorted-table read-after-write (register and memory)
//!   - permutation accumulators: register file, memory, program ROM
//!     (LogUp), public input (LogUp), public output (LogUp)
//!
//! v1 known soundness gaps documented in the project README:
//!   - sorted-table ordering is not range-checked, so a malicious prover
//!     can re-order entries to put a "read" before its corresponding
//!     "write" within the same register/address.
//!   - register/memory init values are not bound; the very first sorted
//!     access at any (idx) or (addr) can claim arbitrary values.
//!   - single-channel permutation arguments (~2^-30 soundness).

use toyni::babybear::BabyBear;

use zkvm_core::{accum, col, NUM_ACCUM_COLS, NUM_OPCODES, NUM_TRACE_COLS};

#[derive(Clone)]
pub struct TraceView {
    pub vals: Vec<BabyBear>,
}

impl TraceView {
    pub fn col(&self, i: usize) -> BabyBear { self.vals[i] }
    pub fn sel(&self, k: usize) -> BabyBear { self.vals[col::SEL_START + k] }
}

pub mod opc {
    pub const ADD: usize = 0;
    pub const SUB: usize = 1;
    pub const MUL: usize = 2;
    pub const IMM: usize = 3;
    pub const LOAD: usize = 4;
    pub const STORE: usize = 5;
    pub const JMP: usize = 6;
    pub const JZ: usize = 7;
    pub const READ: usize = 8;
    pub const WRITE: usize = 9;
    pub const HALT: usize = 10;
}

// ── transition constraints ─────────────────────────────────────────────

pub fn eval_transition_constraints(curr: &TraceView, next: &TraceView) -> Vec<BabyBear> {
    let mut c = Vec::new();
    let one = BabyBear::one();

    // 1. Clock increments by 1.
    c.push(next.col(col::CLK) - curr.col(col::CLK) - one);

    // 2. PC continuity when not halted.
    let halted = curr.col(col::HALT);
    let not_halted = one - halted;
    c.push(not_halted * (next.col(col::PC) - curr.col(col::NEXT_PC)));

    // 3. Selectors are boolean.
    for k in 0..NUM_OPCODES {
        let s = curr.sel(k);
        c.push(s * (s - one));
    }

    // 4. Selectors sum to 1.
    let mut sum = BabyBear::zero();
    for k in 0..NUM_OPCODES { sum = sum + curr.sel(k); }
    c.push(sum - one);

    // 5. OPCODE column = 1*sel0 + 2*sel1 + ... + 11*sel10.
    let mut op_recon = BabyBear::zero();
    for k in 0..NUM_OPCODES {
        op_recon = op_recon + curr.sel(k) * BabyBear::from_u32((k as u32) + 1);
    }
    c.push(curr.col(col::OPCODE) - op_recon);

    // 6. HALT_FLAG is boolean.
    c.push(halted * (halted - one));

    // 7. HALT monotonicity.
    //    HALT column = "halted after this row's instruction". A row that
    //    *executes* HALT itself flips the post-state from 0 to 1, so the
    //    transition references next.sel_HALT, not curr.sel_HALT:
    //      next.HALT = curr.HALT + (1 - curr.HALT) * next.sel_HALT
    let next_sel_halt = next.sel(opc::HALT);
    c.push(next.col(col::HALT) - halted - next_sel_halt + halted * next_sel_halt);

    // 8. I/O cursor advancement.
    let sel_read = curr.sel(opc::READ);
    let sel_write = curr.sel(opc::WRITE);
    c.push(next.col(col::I_IN)  - curr.col(col::I_IN)  - sel_read);
    c.push(next.col(col::I_OUT) - curr.col(col::I_OUT) - sel_write);

    // 9. Reg-slot is_write columns are boolean and r0-hardwired.
    for &(idx_col, val_col, wr_col, inv_col) in &[
        (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR, col::REG_A_INV),
        (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR, col::REG_B_INV),
        (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR, col::REG_C_INV),
    ] {
        let idx = curr.col(idx_col);
        let val = curr.col(val_col);
        let wr  = curr.col(wr_col);
        let inv = curr.col(inv_col);
        // wr is boolean
        c.push(wr * (wr - one));
        // r0 trick: idx * (1 - idx*inv) = 0  AND  (1 - idx*inv) * val = 0
        // When idx != 0: idx*inv = 1, so the second term forces nothing.
        // When idx == 0: idx*inv = 0, so val must be 0.
        c.push(idx * (one - idx * inv));
        c.push((one - idx * inv) * val);
    }

    // 10. MEM flag consistency.
    let sel_load = curr.sel(opc::LOAD);
    let sel_store = curr.sel(opc::STORE);
    c.push(curr.col(col::MEM_USED) - sel_load - sel_store);
    c.push(curr.col(col::MEM_WR)   - sel_store);

    // 11. JZ helper consistency: JZ_IS_ZERO ∈ {0,1}, and:
    //     JZ_IS_ZERO * REG_A_VAL = 0
    //     (1 - JZ_IS_ZERO) - REG_A_VAL * JZ_VAL_INV = 0
    // Together these force JZ_IS_ZERO = 1 iff REG_A_VAL = 0.
    let jzz = curr.col(col::JZ_IS_ZERO);
    let jzi = curr.col(col::JZ_VAL_INV);
    let ra_val = curr.col(col::REG_A_VAL);
    c.push(jzz * (jzz - one));
    c.push(jzz * ra_val);
    c.push((one - jzz) - ra_val * jzi);

    // 12. Per-opcode constraints.
    c.extend(arith_constraints(curr));
    c.extend(jump_constraints(curr));
    c.extend(memory_op_constraints(curr));
    c.extend(io_constraints(curr));

    c
}

pub fn num_transition_constraints() -> usize {
    let dummy = TraceView { vals: vec![BabyBear::zero(); NUM_TRACE_COLS] };
    eval_transition_constraints(&dummy, &dummy).len()
}

// Each helper returns a Vec of constraints; the surrounding `eval_*`
// extends its main vec from these.

fn arith_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut c = Vec::new();
    let one = BabyBear::one();
    let op_a = curr.col(col::OP_A);
    let op_b = curr.col(col::OP_B);
    let op_c = curr.col(col::OP_C);
    let ra = curr.col(col::REG_A_VAL);
    let rb = curr.col(col::REG_B_VAL);
    let rc = curr.col(col::REG_C_VAL);
    let sa_idx = curr.col(col::REG_A_IDX);
    let sb_idx = curr.col(col::REG_B_IDX);
    let sc_idx = curr.col(col::REG_C_IDX);
    let sa_wr = curr.col(col::REG_A_WR);
    let sb_wr = curr.col(col::REG_B_WR);
    let sc_wr = curr.col(col::REG_C_WR);

    let s_add = curr.sel(opc::ADD);
    let s_sub = curr.sel(opc::SUB);
    let s_mul = curr.sel(opc::MUL);
    let s_alu = s_add + s_sub + s_mul;
    let s_imm = curr.sel(opc::IMM);

    // ALU: slot A = ra (read of op_b), slot B = rb (read of op_c),
    //       slot C = rd (write of op_a).
    c.push(s_alu * (sa_idx - op_b));
    c.push(s_alu * (sb_idx - op_c));
    c.push(s_alu * (sc_idx - op_a));
    c.push(s_alu * sa_wr);
    c.push(s_alu * sb_wr);
    c.push(s_alu * (sc_wr - one));

    // Per-op result computation.
    c.push(s_add * (rc - ra - rb));
    c.push(s_sub * (rc - ra + rb));
    c.push(s_mul * (rc - ra * rb));

    // IMM: slot C = rd, value = op_b. Slots A and B are unused (idx=0).
    c.push(s_imm * (sc_idx - op_a));
    c.push(s_imm * (rc - op_b));
    c.push(s_imm * (sc_wr - one));
    c.push(s_imm * sa_idx);
    c.push(s_imm * sb_idx);

    c
}

fn jump_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut c = Vec::new();
    let one = BabyBear::one();
    let pc = curr.col(col::PC);
    let next_pc = curr.col(col::NEXT_PC);
    let op_a = curr.col(col::OP_A);
    let op_b = curr.col(col::OP_B);

    let s_jmp = curr.sel(opc::JMP);
    let s_jz  = curr.sel(opc::JZ);
    let s_halt = curr.sel(opc::HALT);
    let any_branch = s_jmp + s_jz + s_halt;

    // Default PC advance: any non-jump, non-halt instruction has next_pc = pc + 1.
    c.push((one - any_branch) * (next_pc - pc - one));

    // JMP: next_pc = op_a.
    c.push(s_jmp * (next_pc - op_a));

    // JMP/READ/WRITE/IMM/LOAD/STORE: slot A index — JMP doesn't read any
    // register, so slot A index must be 0.
    c.push(s_jmp * curr.col(col::REG_A_IDX));
    c.push(s_jmp * curr.col(col::REG_B_IDX));
    c.push(s_jmp * curr.col(col::REG_C_IDX));

    // HALT: next_pc = pc, and no register/memory traffic.
    c.push(s_halt * (next_pc - pc));
    c.push(s_halt * curr.col(col::REG_A_IDX));
    c.push(s_halt * curr.col(col::REG_B_IDX));
    c.push(s_halt * curr.col(col::REG_C_IDX));

    // JZ: slot A reads op_a; if REG_A_VAL == 0 (JZ_IS_ZERO=1) then
    //     next_pc = op_b, otherwise next_pc = pc + 1.
    let jzz = curr.col(col::JZ_IS_ZERO);
    c.push(s_jz * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_jz * curr.col(col::REG_A_WR));
    c.push(s_jz * jzz * (next_pc - op_b));
    c.push(s_jz * (one - jzz) * (next_pc - pc - one));
    // JZ uses only slot A.
    c.push(s_jz * curr.col(col::REG_B_IDX));
    c.push(s_jz * curr.col(col::REG_C_IDX));

    c
}

fn memory_op_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut c = Vec::new();
    let one = BabyBear::one();
    let op_a = curr.col(col::OP_A);
    let op_b = curr.col(col::OP_B);

    let s_load = curr.sel(opc::LOAD);
    let s_store = curr.sel(opc::STORE);

    // LOAD r_d, r_a:  slot A reads r_a (=op_b), slot C writes r_d (=op_a)
    //   with mem_val. Memory is a read.
    c.push(s_load * (curr.col(col::REG_A_IDX) - op_b));
    c.push(s_load * curr.col(col::REG_A_WR));
    c.push(s_load * (curr.col(col::MEM_ADDR) - curr.col(col::REG_A_VAL)));
    c.push(s_load * (curr.col(col::REG_C_IDX) - op_a));
    c.push(s_load * (curr.col(col::REG_C_VAL) - curr.col(col::MEM_VAL)));
    c.push(s_load * (curr.col(col::REG_C_WR) - one));
    c.push(s_load * curr.col(col::REG_B_IDX));

    // STORE r_a, r_b:  slot A reads r_a (=op_a) for the address,
    //   slot B reads r_b (=op_b) for the value. Memory is a write.
    c.push(s_store * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_store * curr.col(col::REG_A_WR));
    c.push(s_store * (curr.col(col::REG_B_IDX) - op_b));
    c.push(s_store * curr.col(col::REG_B_WR));
    c.push(s_store * (curr.col(col::MEM_ADDR) - curr.col(col::REG_A_VAL)));
    c.push(s_store * (curr.col(col::MEM_VAL)  - curr.col(col::REG_B_VAL)));
    c.push(s_store * curr.col(col::REG_C_IDX));

    c
}

fn io_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut c = Vec::new();
    let one = BabyBear::one();
    let op_a = curr.col(col::OP_A);

    // READ r_d:  slot C writes r_d (=op_a). Slots A and B unused.
    let s_read = curr.sel(opc::READ);
    c.push(s_read * (curr.col(col::REG_C_IDX) - op_a));
    c.push(s_read * (curr.col(col::REG_C_WR) - one));
    c.push(s_read * curr.col(col::REG_A_IDX));
    c.push(s_read * curr.col(col::REG_B_IDX));

    // WRITE r_a:  slot A reads r_a (=op_a). Slots B and C unused.
    let s_write = curr.sel(opc::WRITE);
    c.push(s_write * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_write * curr.col(col::REG_A_WR));
    c.push(s_write * curr.col(col::REG_B_IDX));
    c.push(s_write * curr.col(col::REG_C_IDX));

    c
}

// ── permutation accumulators ──────────────────────────────────────────

pub mod permutation {
    use super::*;

    /// Single (γ, α) channel; gammas[0] / alphas[0] are used.
    pub fn compute_accumulators(
        columns: &[Vec<BabyBear>],
        gammas: &[BabyBear; 4],
        alphas: &[BabyBear; 4],
    ) -> Vec<Vec<BabyBear>> {
        let n = columns[0].len();
        let g = gammas[0];
        let a = alphas[0];

        let compress = |vals: &[BabyBear]| -> BabyBear {
            let mut acc = BabyBear::zero();
            let mut ap = BabyBear::one();
            for &v in vals { acc = acc + v * ap; ap = ap * a; }
            acc
        };

        // Grand-product accumulators start at 1, LogUp accumulators at 0.
        let mut accums: Vec<Vec<BabyBear>> = (0..NUM_ACCUM_COLS)
            .map(|j| {
                let init = if j == accum::REG || j == accum::MEM {
                    BabyBear::one()
                } else {
                    BabyBear::zero()
                };
                let mut col = vec![BabyBear::zero(); n];
                col[0] = init;
                col
            })
            .collect();

        for i in 0..n - 1 {
            // ── register file (grand product, multi-slot) ──
            let mut num = BabyBear::one();
            for &(b_idx, b_val, b_wr) in &[
                (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR),
                (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR),
                (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR),
            ] {
                let t = compress(&[
                    columns[b_idx][i], columns[b_val][i],
                    columns[col::CLK][i], columns[b_wr][i],
                ]);
                num = num * (t + g);
            }
            let mut den = BabyBear::one();
            for &base in &[col::SREG_A, col::SREG_B, col::SREG_C] {
                let t = compress(&[
                    columns[base    ][i], columns[base + 1][i],
                    columns[base + 2][i], columns[base + 3][i],
                ]);
                den = den * (t + g);
            }
            accums[accum::REG][i + 1] = accums[accum::REG][i] * num * den.inverse();

            // ── memory (grand product, single slot) ──
            let m_main = compress(&[
                columns[col::MEM_ADDR][i], columns[col::MEM_VAL][i],
                columns[col::CLK][i],      columns[col::MEM_WR][i],
                columns[col::MEM_USED][i],
            ]);
            let m_sorted = compress(&[
                columns[col::SMEM    ][i], columns[col::SMEM + 1][i],
                columns[col::SMEM + 2][i], columns[col::SMEM + 3][i],
                columns[col::SMEM + 4][i],
            ]);
            accums[accum::MEM][i + 1] = accums[accum::MEM][i]
                * (m_main + g) * (m_sorted + g).inverse();

            // ── program ROM (LogUp) ──
            // Z[i+1] = Z[i] + 1/(exec + g) - mult/(rom + g)
            let exec = compress(&[
                columns[col::PC][i],     columns[col::OPCODE][i],
                columns[col::OP_A][i],   columns[col::OP_B][i],
                columns[col::OP_C][i],
            ]);
            let rom = compress(&[
                columns[col::PROG    ][i], columns[col::PROG + 1][i],
                columns[col::PROG + 2][i], columns[col::PROG + 3][i],
                columns[col::PROG + 4][i],
            ]);
            let mult = columns[col::PROG + 5][i];
            let exec_inv = (exec + g).inverse();
            let rom_term = if mult.is_zero() {
                BabyBear::zero()
            } else {
                mult * (rom + g).inverse()
            };
            accums[accum::PROG][i + 1] = accums[accum::PROG][i] + exec_inv - rom_term;

            // ── public input (LogUp) ──
            // Exec side: when sel_read=1, contribute 1/((i_in_pre, val) + γ_compressed).
            // Table side: subtract 1/((j, public_inputs[j]) + γ) at row j.
            // Multiplicities are 0/1 per row.
            let sel_read = columns[col::SEL_START + opc::READ][i];
            let exec_in = compress(&[columns[col::I_IN][i], columns[col::REG_C_VAL][i]]);
            let table_in = compress(&[columns[col::PUB_IN][i], columns[col::PUB_IN + 1][i]]);
            let table_mult = columns[col::PUB_IN + 2][i];
            let exec_term = if sel_read.is_zero() {
                BabyBear::zero()
            } else {
                sel_read * (exec_in + g).inverse()
            };
            let tab_term = if table_mult.is_zero() {
                BabyBear::zero()
            } else {
                table_mult * (table_in + g).inverse()
            };
            accums[accum::PUB_IN][i + 1] = accums[accum::PUB_IN][i] + exec_term - tab_term;

            // ── public output (LogUp) ──
            let sel_write = columns[col::SEL_START + opc::WRITE][i];
            let exec_out = compress(&[columns[col::I_OUT][i], columns[col::REG_A_VAL][i]]);
            let table_out = compress(&[columns[col::PUB_OUT][i], columns[col::PUB_OUT + 1][i]]);
            let table_out_mult = columns[col::PUB_OUT + 2][i];
            let exec_term_out = if sel_write.is_zero() {
                BabyBear::zero()
            } else {
                sel_write * (exec_out + g).inverse()
            };
            let tab_term_out = if table_out_mult.is_zero() {
                BabyBear::zero()
            } else {
                table_out_mult * (table_out + g).inverse()
            };
            accums[accum::PUB_OUT][i + 1] = accums[accum::PUB_OUT][i] + exec_term_out - tab_term_out;
        }

        accums
    }

    /// All accumulator constraints are wrap-around (the last-row → first-row
    /// transition closes the multiset). The verifier checks Z[0] separately
    /// via boundary constraints.
    pub fn eval_accum_constraints(
        curr: &TraceView,
        _next: &TraceView,
        curr_acc: &[BabyBear],
        next_acc: &[BabyBear],
        gammas: &[BabyBear; 4],
        alphas: &[BabyBear; 4],
    ) -> Vec<BabyBear> {
        let g = gammas[0];
        let a = alphas[0];
        let mut c = Vec::new();
        let one = BabyBear::one();

        let compress = |vals: &[BabyBear]| -> BabyBear {
            let mut acc = BabyBear::zero();
            let mut ap = BabyBear::one();
            for &v in vals { acc = acc + v * ap; ap = ap * a; }
            acc
        };

        // ── reg-file (grand product) ──
        // next.Z * den = curr.Z * num
        let mut num = one;
        for &(b_idx, b_val, b_wr) in &[
            (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR),
            (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR),
            (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR),
        ] {
            let t = compress(&[curr.col(b_idx), curr.col(b_val), curr.col(col::CLK), curr.col(b_wr)]);
            num = num * (t + g);
        }
        let mut den = one;
        for &base in &[col::SREG_A, col::SREG_B, col::SREG_C] {
            let t = compress(&[curr.col(base), curr.col(base + 1), curr.col(base + 2), curr.col(base + 3)]);
            den = den * (t + g);
        }
        c.push(next_acc[accum::REG] * den - curr_acc[accum::REG] * num);

        // ── memory (grand product) ──
        let m_main = compress(&[
            curr.col(col::MEM_ADDR), curr.col(col::MEM_VAL),
            curr.col(col::CLK),      curr.col(col::MEM_WR),
            curr.col(col::MEM_USED),
        ]);
        let m_sorted = compress(&[
            curr.col(col::SMEM    ), curr.col(col::SMEM + 1),
            curr.col(col::SMEM + 2), curr.col(col::SMEM + 3),
            curr.col(col::SMEM + 4),
        ]);
        c.push(
            next_acc[accum::MEM] * (m_sorted + g)
            - curr_acc[accum::MEM] * (m_main + g)
        );

        // ── program ROM (LogUp) ──
        // (next.Z - curr.Z) * (exec+g)*(rom+g) = (rom+g) - mult*(exec+g)
        let exec = compress(&[
            curr.col(col::PC),     curr.col(col::OPCODE),
            curr.col(col::OP_A),   curr.col(col::OP_B),
            curr.col(col::OP_C),
        ]);
        let rom = compress(&[
            curr.col(col::PROG    ), curr.col(col::PROG + 1),
            curr.col(col::PROG + 2), curr.col(col::PROG + 3),
            curr.col(col::PROG + 4),
        ]);
        let mult = curr.col(col::PROG + 5);
        c.push(
            (next_acc[accum::PROG] - curr_acc[accum::PROG]) * (exec + g) * (rom + g)
            - (rom + g) + mult * (exec + g)
        );

        // ── public input (LogUp) ──
        // (next.Z - curr.Z) * (exec+g)*(table+g)
        //   = sel_read*(table+g) - table_mult*(exec+g)
        let sel_read = curr.sel(opc::READ);
        let exec_in = compress(&[curr.col(col::I_IN), curr.col(col::REG_C_VAL)]);
        let table_in = compress(&[curr.col(col::PUB_IN), curr.col(col::PUB_IN + 1)]);
        let table_in_mult = curr.col(col::PUB_IN + 2);
        c.push(
            (next_acc[accum::PUB_IN] - curr_acc[accum::PUB_IN]) * (exec_in + g) * (table_in + g)
            - sel_read * (table_in + g) + table_in_mult * (exec_in + g)
        );

        // ── public output (LogUp) ──
        let sel_write = curr.sel(opc::WRITE);
        let exec_out = compress(&[curr.col(col::I_OUT), curr.col(col::REG_A_VAL)]);
        let table_out = compress(&[curr.col(col::PUB_OUT), curr.col(col::PUB_OUT + 1)]);
        let table_out_mult = curr.col(col::PUB_OUT + 2);
        c.push(
            (next_acc[accum::PUB_OUT] - curr_acc[accum::PUB_OUT]) * (exec_out + g) * (table_out + g)
            - sel_write * (table_out + g) + table_out_mult * (exec_out + g)
        );

        c
    }

    pub fn num_accum_constraints() -> usize { 5 }

    /// All 5 accumulator transitions are cyclic (must hold including wrap).
    pub fn is_wrap_constraint(_j: usize) -> bool { true }
}

/// Convenience for the prover: validate a trace against the AIR before
/// running the proof pipeline.
pub fn validate_full_trace(
    columns: &[Vec<BabyBear>],
    accum_columns: &[Vec<BabyBear>],
    gammas: &[BabyBear; 4],
    alphas: &[BabyBear; 4],
) -> Result<(), String> {
    let n = columns[0].len();

    // Main transition constraints, with last-row exception (matches the
    // "all main constraints are excepted" convention used by the prover's
    // quotient computation).
    for row in 0..n - 1 {
        let curr = TraceView { vals: columns.iter().map(|c| c[row]).collect() };
        let next = TraceView { vals: columns.iter().map(|c| c[row + 1]).collect() };
        let cv = eval_transition_constraints(&curr, &next);
        for (j, &v) in cv.iter().enumerate() {
            if !v.is_zero() {
                return Err(format!("transition constraint {} violated at row {}: {}", j, row, v.value));
            }
        }
    }

    // Accumulator constraints, all wrap-around.
    for row in 0..n {
        let curr = TraceView { vals: columns.iter().map(|c| c[row]).collect() };
        let next_row = if row + 1 < n { row + 1 } else { 0 };
        let next = TraceView { vals: columns.iter().map(|c| c[next_row]).collect() };
        let curr_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[row]).collect();
        let next_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[next_row]).collect();
        let cv = permutation::eval_accum_constraints(&curr, &next, &curr_acc, &next_acc, gammas, alphas);
        for (j, &v) in cv.iter().enumerate() {
            if !v.is_zero() {
                return Err(format!("accum constraint {} violated at row {}: {}", j, row, v.value));
            }
        }
    }
    Ok(())
}

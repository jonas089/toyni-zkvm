//! AIR for the small custom VM.
//!
//! The goal of this constraint set is a *fully constrained* minimal VM: every
//! column is either derived by a transition/boundary constraint or bound by a
//! permutation / lookup argument, leaving the prover no unconstrained freedom.
//!
//! Transition constraint groups (hold on every transition; the last row is
//! excepted, matching the cyclic FRI domain used by the prover):
//!   - clock / PC / selector / opcode reconstruction
//!   - HALT booleanity, monotonicity, PC-freeze, and post-halt HALT replay
//!   - public I/O cursor advancement
//!   - register-slot well-formedness: activity flag, inactive-zeroing,
//!     write booleanity, r0 hardwiring (idx=0 ⇒ val=0)
//!   - per-opcode slot activity / indices / read-write roles and semantics
//!   - JZ is-zero helper
//!   - program-ROM well-formedness (real flag, contiguity, multiplicity range)
//!   - sorted-table read-after-write + init binding + strict-ordering range
//!     check + r0 pin (registers)
//!
//! Accumulator constraints (cyclic, hold on every row):
//!   - register / memory grand products
//!   - program-ROM / public-input / public-output LogUps
//!
//! Boundary constraints (see the prover/verifier): first-row machine state,
//! accumulator initial values, the sorted-memory init record, the ROM entry
//! address, and the last-row HALT flag.
//!
//! ## Field usage
//!
//! The trace itself is over the base field BabyBear, but all constraints are
//! evaluated over the quartic extension `Ext`. The prover lifts base trace
//! values into `Ext` (base embeds as `a + 0X + 0X^2 + 0X^3`) before evaluating
//! constraints, so a single code path serves both the on-domain quotient
//! computation and the out-of-domain (extension-point) opening check. Drawing
//! the random challenges from `Ext` is what lifts the lookup / permutation and
//! FRI soundness from ~31 bits (base field) to ~124 bits.

use toyni::babybear::BabyBear;
use toyni::ext::Ext;

use zkvm_core::{accum, col, NUM_ACCUM_COLS, NUM_CHANNELS, NUM_OPCODES, NUM_TRACE_COLS};

/// A single trace row lifted into the extension field.
#[derive(Clone)]
pub struct TraceView {
    pub vals: Vec<Ext>,
}

impl TraceView {
    pub fn col(&self, i: usize) -> Ext { self.vals[i] }
    pub fn sel(&self, k: usize) -> Ext { self.vals[col::SEL_START + k] }

    /// Lift a base-field trace row into the extension field.
    pub fn from_base(vals: &[BabyBear]) -> Self {
        TraceView { vals: vals.iter().map(|&v| Ext::from(v)).collect() }
    }
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

// The three register-access slots as (idx, val, wr, inv, active) column bases.
const REG_SLOTS: [(usize, usize, usize, usize, usize); 3] = [
    (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR, col::REG_A_INV, col::REG_A_ACT),
    (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR, col::REG_B_INV, col::REG_B_ACT),
    (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR, col::REG_C_INV, col::REG_C_ACT),
];

// ── transition constraints ─────────────────────────────────────────────

pub fn eval_transition_constraints(curr: &TraceView, next: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();

    // CLK_INCREMENT: clock advances by 1 (CLK_INIT is a boundary constraint).
    c.push(next.col(col::CLK) - curr.col(col::CLK) - one);

    // PC_CONTINUITY: when not halted, next PC equals this row's NEXT_PC.
    let halted = curr.col(col::HALT);
    let not_halted = one - halted;
    c.push(not_halted * (next.col(col::PC) - curr.col(col::NEXT_PC)));

    // SEL_BOOLEAN.
    for k in 0..NUM_OPCODES {
        let s = curr.sel(k);
        c.push(s * (s - one));
    }

    // SEL_SUM_ONE.
    let mut sum = Ext::zero();
    for k in 0..NUM_OPCODES { sum = sum + curr.sel(k); }
    c.push(sum - one);

    // OPCODE_RECON: OPCODE = Σ (k+1)·sel_k.
    let mut op_recon = Ext::zero();
    for k in 0..NUM_OPCODES {
        op_recon = op_recon + curr.sel(k) * Ext::from_u32((k as u32) + 1);
    }
    c.push(curr.col(col::OPCODE) - op_recon);

    // HALT_BOOLEAN.
    c.push(halted * (halted - one));

    // HALT_MONOTONE: the HALT column is "halted after this row". A row that
    // executes HALT flips it 0→1, so the transition references next.sel_HALT:
    //   next.HALT = curr.HALT + (1 - curr.HALT) * next.sel_HALT
    let next_sel_halt = next.sel(opc::HALT);
    c.push(next.col(col::HALT) - halted - next_sel_halt + halted * next_sel_halt);

    // POST_HALT_REPEATS_HALT: any row in the halted state re-executes HALT, so
    // padding touches no register / memory / I/O lane and its frozen-PC ROM
    // lookup matches the real HALT entry.
    c.push(halted * (one - curr.sel(opc::HALT)));

    // I/O cursor advancement.
    let sel_read = curr.sel(opc::READ);
    let sel_write = curr.sel(opc::WRITE);
    c.push(next.col(col::I_IN)  - curr.col(col::I_IN)  - sel_read);
    c.push(next.col(col::I_OUT) - curr.col(col::I_OUT) - sel_write);

    // Register-slot well-formedness.
    for &(idx_col, val_col, wr_col, inv_col, act_col) in &REG_SLOTS {
        let idx = curr.col(idx_col);
        let val = curr.col(val_col);
        let wr  = curr.col(wr_col);
        let inv = curr.col(inv_col);
        let act = curr.col(act_col);
        // SLOT_ACTIVE_BOOLEAN.
        c.push(act * (act - one));
        // SLOT_INACTIVE_ZEROED: an inactive slot has idx, val, wr all zero.
        c.push((one - act) * idx);
        c.push((one - act) * val);
        c.push((one - act) * wr);
        // SLOT_WR_BOOLEAN.
        c.push(wr * (wr - one));
        // R0_IDX_INV: idx is zero or has a committed inverse.
        c.push(idx * (one - idx * inv));
        // R0_VAL_ZERO: idx = 0 ⇒ val = 0.
        c.push((one - idx * inv) * val);
    }

    // OPCODE_SLOT_ACTIVITY: each opcode activates exactly the slots it uses.
    let s_add = curr.sel(opc::ADD);
    let s_sub = curr.sel(opc::SUB);
    let s_mul = curr.sel(opc::MUL);
    let s_alu = s_add + s_sub + s_mul;
    let s_imm = curr.sel(opc::IMM);
    let s_load = curr.sel(opc::LOAD);
    let s_store = curr.sel(opc::STORE);
    c.push(curr.col(col::REG_A_ACT) - (s_alu + s_load + s_store + curr.sel(opc::JZ) + sel_write));
    c.push(curr.col(col::REG_B_ACT) - (s_alu + s_store));
    c.push(curr.col(col::REG_C_ACT) - (s_alu + s_imm + s_load + sel_read));

    // MEM_WIRING (flags): MEM_USED set iff LOAD/STORE, MEM_WR set iff STORE.
    c.push(curr.col(col::MEM_USED) - s_load - s_store);
    c.push(curr.col(col::MEM_WR)   - s_store);

    // MEM_UNUSED_ZEROED: a row with MEM_USED = 0 carries no memory tuple, so its
    // addr/val must be 0. Without this an "unused" row can smuggle an arbitrary
    // (addr, val) into the memory grand product, where it sorts between a real
    // write and read and poisons the read-after-write value (forge any LOAD).
    let mem_unused = one - curr.col(col::MEM_USED);
    c.push(mem_unused * curr.col(col::MEM_ADDR));
    c.push(mem_unused * curr.col(col::MEM_VAL));

    // JZ is-zero helper.
    let jzz = curr.col(col::JZ_IS_ZERO);
    let jzi = curr.col(col::JZ_VAL_INV);
    let ra_val = curr.col(col::REG_A_VAL);
    c.push(jzz * (jzz - one));            // JZ_ZERO_BOOLEAN
    c.push(jzz * ra_val);                 // JZ_ZERO_KILL
    c.push((one - jzz) - ra_val * jzi);   // JZ_NONZERO_INV

    // Per-opcode semantics.
    c.extend(arith_constraints(curr));
    c.extend(jump_constraints(curr));
    c.extend(memory_op_constraints(curr));
    c.extend(io_constraints(curr));

    // Program-ROM well-formedness.
    c.extend(rom_constraints(curr, next));

    // Sorted-table transitions: three register slots and one memory slot.
    c.extend(reg_slot_transition(curr, curr,
        col::SREG_A, col::SREG_B, col::SREG_A + 5, col::DIFF_BITS_AB));
    c.extend(reg_slot_transition(curr, curr,
        col::SREG_B, col::SREG_C, col::SREG_B + 5, col::DIFF_BITS_BC));
    c.extend(reg_slot_transition(curr, next,
        col::SREG_C, col::SREG_A, col::SREG_C + 5, col::DIFF_BITS_CA));
    c.extend(mem_slot_transition(curr, next));

    c
}

/// Program-ROM table well-formedness. The table columns are also Lagrange-bound
/// by the verifier (which fixes addr = row index for every real entry); these
/// in-AIR constraints are the matching in-circuit checks.
fn rom_constraints(curr: &TraceView, next: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();

    let real = curr.col(col::PROG + 6);
    let next_real = next.col(col::PROG + 6);
    let addr = curr.col(col::PROG);
    let next_addr = next.col(col::PROG);

    // `real` is boolean and forms a contiguous prefix (monotone non-increasing).
    c.push(real * (real - one));
    c.push(next_real * (one - real));
    // ROM_ENTRY_WELLFORMED / ROM_PC_DISTINCT: real entries are contiguous, so
    // PCs are distinct and gap-free. When the next row is real, its address is
    // exactly one more than this one.
    c.push(next_real * (next_addr - addr - one));

    // ROM_MULT_RANGE: the multiplicity is a DIFF_BITS-bit non-negative value.
    let mult = curr.col(col::PROG + 5);
    let mut recon = Ext::zero();
    for k in 0..col::DIFF_BITS {
        let bit = curr.col(col::MULT_BITS_PROG + k);
        c.push(bit * (bit - one));
        recon = recon + bit * Ext::from_u32(1u32 << k);
    }
    c.push(mult - recon);

    c
}

/// Constraint pack for a sorted register-slot transition (prev → next).
/// `prev_view` and `next_view` differ only for the cross-row C → A[i+1] case.
fn reg_slot_transition(
    prev_view: &TraceView,
    next_view: &TraceView,
    prev_base: usize,
    next_base: usize,
    aux_base: usize,
    bits_base: usize,
) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();

    let prev_idx = prev_view.col(prev_base);
    let prev_val = prev_view.col(prev_base + 1);
    let prev_t   = prev_view.col(prev_base + 2);
    let prev_inv = prev_view.col(prev_base + 4);
    let next_idx = next_view.col(next_base);
    let next_val = next_view.col(next_base + 1);
    let next_t   = next_view.col(next_base + 2);
    let next_wr  = next_view.col(next_base + 3);

    let same_idx = prev_view.col(aux_base);
    let diff_inv = prev_view.col(aux_base + 1);

    // SORTED_R0_PIN on the prev entry: idx = 0 ⇒ val = 0. Each sorted entry is
    // the `prev` of exactly one transition, so this pins every entry's r0 value.
    c.push(prev_idx * (one - prev_idx * prev_inv));
    c.push((one - prev_idx * prev_inv) * prev_val);

    // SORTED_SAME_KEY_BOOLEAN.
    c.push(same_idx * (same_idx - one));
    // SORTED_SAME_KEY_MATCH.
    c.push(same_idx * (next_idx - prev_idx));
    // SORTED_DIFF_KEY_INV.
    c.push((one - same_idx) * (one - (next_idx - prev_idx) * diff_inv));

    // SORTED_RAW: same key + next is a read ⇒ value matches.
    c.push(same_idx * (one - next_wr) * (next_val - prev_val));
    // Init binding: a fresh idx (same_idx = 0) read ⇒ val = 0.
    c.push((one - same_idx) * (one - next_wr) * next_val);

    // SORTED_STRICT_DIFF: diff = 1 + Σ bit_k·2^k, each bit boolean. diff is the
    // access-time delta within a key, else the index delta. The "+1" forces
    // strict positivity, so the ordering is genuinely increasing.
    let diff = same_idx * (next_t - prev_t) + (one - same_idx) * (next_idx - prev_idx);
    let mut recon = one;
    for k in 0..col::DIFF_BITS {
        let bit = prev_view.col(bits_base + k);
        c.push(bit * (bit - one));
        recon = recon + bit * Ext::from_u32(1u32 << k);
    }
    c.push(diff - recon);

    c
}

/// Constraint pack for the sorted memory transition.
fn mem_slot_transition(curr: &TraceView, next: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();

    let prev_addr = curr.col(col::SMEM);
    let prev_val  = curr.col(col::SMEM + 1);
    let prev_clk  = curr.col(col::SMEM + 2);
    let next_addr = next.col(col::SMEM);
    let next_val  = next.col(col::SMEM + 1);
    let next_clk  = next.col(col::SMEM + 2);
    let next_wr   = next.col(col::SMEM + 3);
    let next_used = next.col(col::SMEM + 4);

    let same_addr = curr.col(col::SMEM + 5);
    let diff_inv  = curr.col(col::SMEM + 6);

    c.push(same_addr * (same_addr - one));
    c.push(same_addr * (next_addr - prev_addr));
    c.push((one - same_addr) * (one - (next_addr - prev_addr) * diff_inv));

    // R-A-W (only when the next access is used and is a read).
    c.push(next_used * same_addr * (one - next_wr) * (next_val - prev_val));
    // Init binding (next used, fresh address, read ⇒ 0).
    c.push(next_used * (one - same_addr) * (one - next_wr) * next_val);

    // SORTED_STRICT_DIFF: clk is unique per row so the (addr, clk) key is
    // strictly increasing; diff = 1 + decomposition.
    let diff = same_addr * (next_clk - prev_clk) + (one - same_addr) * (next_addr - prev_addr);
    let mut recon = one;
    for k in 0..col::DIFF_BITS {
        let bit = curr.col(col::DIFF_BITS_M + k);
        c.push(bit * (bit - one));
        recon = recon + bit * Ext::from_u32(1u32 << k);
    }
    c.push(diff - recon);

    // SORTED_MEM_UNUSED_ZEROED: an unused sorted entry must be (addr, val) =
    // (0, 0). Combined with MEM_UNUSED_ZEROED on the main side and the grand
    // product (which forces multiset equality), no unused entry can ever sit at
    // a real address carrying an arbitrary value. This is the explicit, local
    // form of the same invariant the grand product already implies.
    let curr_used = curr.col(col::SMEM + 4);
    c.push((one - curr_used) * prev_addr);
    c.push((one - curr_used) * prev_val);

    c
}

pub fn num_transition_constraints() -> usize {
    let dummy = TraceView { vals: vec![Ext::zero(); NUM_TRACE_COLS] };
    eval_transition_constraints(&dummy, &dummy).len()
}

// Each helper returns a Vec of constraints; the surrounding `eval_*`
// extends its main vec from these. Slots not used by an opcode are forced
// inactive (and thereby idx/val/wr = 0) by OPCODE_SLOT_ACTIVITY +
// SLOT_INACTIVE_ZEROED, so these helpers only pin the *active* slots.

fn arith_constraints(curr: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();
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

    // ALU: slot A reads op_b, slot B reads op_c, slot C writes op_a.
    c.push(s_alu * (sa_idx - op_b));
    c.push(s_alu * (sb_idx - op_c));
    c.push(s_alu * (sc_idx - op_a));
    c.push(s_alu * sa_wr);
    c.push(s_alu * sb_wr);
    c.push(s_alu * (sc_wr - one));

    // ALU_RESULT.
    c.push(s_add * (rc - ra - rb));
    c.push(s_sub * (rc - ra + rb));
    c.push(s_mul * (rc - ra * rb));

    // IMM: slot C writes op_a with value op_b.
    c.push(s_imm * (sc_idx - op_a));
    c.push(s_imm * (rc - op_b));
    c.push(s_imm * (sc_wr - one));

    c
}

fn jump_constraints(curr: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();
    let pc = curr.col(col::PC);
    let next_pc = curr.col(col::NEXT_PC);
    let op_a = curr.col(col::OP_A);
    let op_b = curr.col(col::OP_B);

    let s_jmp = curr.sel(opc::JMP);
    let s_jz  = curr.sel(opc::JZ);
    let s_halt = curr.sel(opc::HALT);
    let any_branch = s_jmp + s_jz + s_halt;

    // DEFAULT_NEXT_PC: non-branch, non-halt opcodes advance PC by 1.
    c.push((one - any_branch) * (next_pc - pc - one));

    // JMP_NEXT_PC.
    c.push(s_jmp * (next_pc - op_a));

    // HALT_NEXT_PC: a HALT row freezes the PC.
    c.push(s_halt * (next_pc - pc));

    // JZ_NEXT_PC: slot A reads op_a; branch to op_b when zero, else PC + 1.
    let jzz = curr.col(col::JZ_IS_ZERO);
    c.push(s_jz * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_jz * curr.col(col::REG_A_WR));
    c.push(s_jz * jzz * (next_pc - op_b));
    c.push(s_jz * (one - jzz) * (next_pc - pc - one));

    c
}

fn memory_op_constraints(curr: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();
    let op_a = curr.col(col::OP_A);
    let op_b = curr.col(col::OP_B);

    let s_load = curr.sel(opc::LOAD);
    let s_store = curr.sel(opc::STORE);

    // LOAD rd, ra: slot A reads ra (= op_b) as the address, slot C writes rd
    // (= op_a) with the memory value; memory is a read.
    c.push(s_load * (curr.col(col::REG_A_IDX) - op_b));
    c.push(s_load * curr.col(col::REG_A_WR));
    c.push(s_load * (curr.col(col::MEM_ADDR) - curr.col(col::REG_A_VAL)));
    c.push(s_load * (curr.col(col::REG_C_IDX) - op_a));
    c.push(s_load * (curr.col(col::REG_C_VAL) - curr.col(col::MEM_VAL)));
    c.push(s_load * (curr.col(col::REG_C_WR) - one));

    // STORE ra, rb: slot A reads ra (= op_a) for the address, slot B reads rb
    // (= op_b) for the value; memory is a write.
    c.push(s_store * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_store * curr.col(col::REG_A_WR));
    c.push(s_store * (curr.col(col::REG_B_IDX) - op_b));
    c.push(s_store * curr.col(col::REG_B_WR));
    c.push(s_store * (curr.col(col::MEM_ADDR) - curr.col(col::REG_A_VAL)));
    c.push(s_store * (curr.col(col::MEM_VAL)  - curr.col(col::REG_B_VAL)));

    c
}

fn io_constraints(curr: &TraceView) -> Vec<Ext> {
    let mut c = Vec::new();
    let one = Ext::one();
    let op_a = curr.col(col::OP_A);

    // READ rd: slot C writes rd (= op_a).
    let s_read = curr.sel(opc::READ);
    c.push(s_read * (curr.col(col::REG_C_IDX) - op_a));
    c.push(s_read * (curr.col(col::REG_C_WR) - one));

    // WRITE ra: slot A reads ra (= op_a).
    let s_write = curr.sel(opc::WRITE);
    c.push(s_write * (curr.col(col::REG_A_IDX) - op_a));
    c.push(s_write * curr.col(col::REG_A_WR));

    c
}

// ── permutation accumulators ──────────────────────────────────────────

pub mod permutation {
    use super::*;

    /// Canonical register access time (base field): t = clk*3 + slot.
    fn reg_main_time_base(clk: BabyBear, slot: usize) -> BabyBear {
        clk * BabyBear::from_u32(3) + BabyBear::from_u32(slot as u32)
    }

    /// Compute all 4-channel accumulator columns over the extension field, from
    /// the base-field trace columns. Layout matches `accum::*`.
    pub fn compute_accumulators(
        columns: &[Vec<BabyBear>],
        gammas: &[Ext; 4],
        alphas: &[Ext; 4],
    ) -> Vec<Vec<Ext>> {
        let n = columns[0].len();

        let mut accums: Vec<Vec<Ext>> = (0..NUM_ACCUM_COLS)
            .map(|j| {
                let init = if j < accum::PROG { Ext::one() } else { Ext::zero() };
                let mut col = vec![Ext::zero(); n];
                col[0] = init;
                col
            })
            .collect();

        for ch in 0..NUM_CHANNELS {
            let g = gammas[ch];
            let a = alphas[ch];
            // Compress a tuple of base-field values into Ext using the Ext
            // challenge `a` (Horner in `a`), via cheap base-scalar multiplies.
            let compress = |vals: &[BabyBear]| -> Ext {
                let mut acc = Ext::zero();
                let mut ap = Ext::one();
                for &v in vals { acc = acc + ap.mul_base(v); ap = ap * a; }
                acc
            };

            for i in 0..n - 1 {
                // ── register file (grand product, 3 slots / row) ──
                let clk = columns[col::CLK][i];
                let mut num = Ext::one();
                for (slot, &(b_idx, b_val, b_wr)) in [
                    (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR),
                    (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR),
                    (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR),
                ].iter().enumerate() {
                    let t = compress(&[
                        columns[b_idx][i], columns[b_val][i],
                        reg_main_time_base(clk, slot), columns[b_wr][i],
                    ]);
                    num = num * (t + g);
                }
                let mut den = Ext::one();
                for &base in &[col::SREG_A, col::SREG_B, col::SREG_C] {
                    let t = compress(&[
                        columns[base    ][i], columns[base + 1][i],
                        columns[base + 2][i], columns[base + 3][i],
                    ]);
                    den = den * (t + g);
                }
                accums[accum::REG + ch][i + 1] = accums[accum::REG + ch][i] * num * den.inverse();

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
                accums[accum::MEM + ch][i + 1] = accums[accum::MEM + ch][i]
                    * (m_main + g) * (m_sorted + g).inverse();

                // ── program ROM (LogUp) ──
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
                let exec_term = (exec + g).inverse();
                let rom_term = if mult.is_zero() { Ext::zero() } else { (rom + g).inverse().mul_base(mult) };
                accums[accum::PROG + ch][i + 1] = accums[accum::PROG + ch][i] + exec_term - rom_term;

                // ── public input (LogUp) ──
                let sel_read = columns[col::SEL_START + opc::READ][i];
                let exec_in = compress(&[columns[col::I_IN][i], columns[col::REG_C_VAL][i]]);
                let tab_in = compress(&[columns[col::PUB_IN][i], columns[col::PUB_IN + 1][i]]);
                let tab_in_m = columns[col::PUB_IN + 2][i];
                let et = if sel_read.is_zero() { Ext::zero() } else { (exec_in + g).inverse().mul_base(sel_read) };
                let tt = if tab_in_m.is_zero() { Ext::zero() } else { (tab_in + g).inverse().mul_base(tab_in_m) };
                accums[accum::PUB_IN + ch][i + 1] = accums[accum::PUB_IN + ch][i] + et - tt;

                // ── public output (LogUp) ──
                let sel_write = columns[col::SEL_START + opc::WRITE][i];
                let exec_out = compress(&[columns[col::I_OUT][i], columns[col::REG_A_VAL][i]]);
                let tab_out = compress(&[columns[col::PUB_OUT][i], columns[col::PUB_OUT + 1][i]]);
                let tab_out_m = columns[col::PUB_OUT + 2][i];
                let et = if sel_write.is_zero() { Ext::zero() } else { (exec_out + g).inverse().mul_base(sel_write) };
                let tt = if tab_out_m.is_zero() { Ext::zero() } else { (tab_out + g).inverse().mul_base(tab_out_m) };
                accums[accum::PUB_OUT + ch][i + 1] = accums[accum::PUB_OUT + ch][i] + et - tt;
            }
        }

        accums
    }

    pub fn eval_accum_constraints(
        curr: &TraceView,
        _next: &TraceView,
        curr_acc: &[Ext],
        next_acc: &[Ext],
        gammas: &[Ext; 4],
        alphas: &[Ext; 4],
    ) -> Vec<Ext> {
        let mut c = Vec::new();
        let one = Ext::one();

        for ch in 0..NUM_CHANNELS {
            let g = gammas[ch];
            let a = alphas[ch];
            let compress = |vals: &[Ext]| -> Ext {
                let mut acc = Ext::zero();
                let mut ap = Ext::one();
                for &v in vals { acc = acc + v * ap; ap = ap * a; }
                acc
            };
            // Register access time t = clk*3 + slot, in the extension field.
            let reg_time = |clk: Ext, slot: usize| clk * Ext::from_u32(3) + Ext::from_u32(slot as u32);

            // ── reg-file (GP) ──
            let clk = curr.col(col::CLK);
            let mut num = one;
            for (slot, &(b_idx, b_val, b_wr)) in [
                (col::REG_A_IDX, col::REG_A_VAL, col::REG_A_WR),
                (col::REG_B_IDX, col::REG_B_VAL, col::REG_B_WR),
                (col::REG_C_IDX, col::REG_C_VAL, col::REG_C_WR),
            ].iter().enumerate() {
                let t = compress(&[curr.col(b_idx), curr.col(b_val), reg_time(clk, slot), curr.col(b_wr)]);
                num = num * (t + g);
            }
            let mut den = one;
            for &base in &[col::SREG_A, col::SREG_B, col::SREG_C] {
                let t = compress(&[curr.col(base), curr.col(base + 1), curr.col(base + 2), curr.col(base + 3)]);
                den = den * (t + g);
            }
            c.push(next_acc[accum::REG + ch] * den - curr_acc[accum::REG + ch] * num);

            // ── memory (GP) ──
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
            c.push(next_acc[accum::MEM + ch] * (m_sorted + g) - curr_acc[accum::MEM + ch] * (m_main + g));

            // ── program ROM (LogUp) ──
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
                (next_acc[accum::PROG + ch] - curr_acc[accum::PROG + ch]) * (exec + g) * (rom + g)
                - (rom + g) + mult * (exec + g)
            );

            // ── public input (LogUp) ──
            let sel_read = curr.sel(opc::READ);
            let exec_in = compress(&[curr.col(col::I_IN), curr.col(col::REG_C_VAL)]);
            let tab_in = compress(&[curr.col(col::PUB_IN), curr.col(col::PUB_IN + 1)]);
            let tab_in_m = curr.col(col::PUB_IN + 2);
            c.push(
                (next_acc[accum::PUB_IN + ch] - curr_acc[accum::PUB_IN + ch]) * (exec_in + g) * (tab_in + g)
                - sel_read * (tab_in + g) + tab_in_m * (exec_in + g)
            );

            // ── public output (LogUp) ──
            let sel_write = curr.sel(opc::WRITE);
            let exec_out = compress(&[curr.col(col::I_OUT), curr.col(col::REG_A_VAL)]);
            let tab_out = compress(&[curr.col(col::PUB_OUT), curr.col(col::PUB_OUT + 1)]);
            let tab_out_m = curr.col(col::PUB_OUT + 2);
            c.push(
                (next_acc[accum::PUB_OUT + ch] - curr_acc[accum::PUB_OUT + ch]) * (exec_out + g) * (tab_out + g)
                - sel_write * (tab_out + g) + tab_out_m * (exec_out + g)
            );
        }

        c
    }

    pub fn num_accum_constraints() -> usize { 5 * NUM_CHANNELS }
    pub fn is_wrap_constraint(_j: usize) -> bool { true }
}

/// Convenience for the prover: validate a trace against the AIR before
/// running the proof pipeline. `columns` are base-field; `accum_columns` are
/// extension-field.
pub fn validate_full_trace(
    columns: &[Vec<BabyBear>],
    accum_columns: &[Vec<Ext>],
    gammas: &[Ext; 4],
    alphas: &[Ext; 4],
) -> Result<(), String> {
    let n = columns[0].len();

    // Main transition constraints, with last-row exception.
    for row in 0..n - 1 {
        let curr = TraceView::from_base(&columns.iter().map(|c| c[row]).collect::<Vec<_>>());
        let next = TraceView::from_base(&columns.iter().map(|c| c[row + 1]).collect::<Vec<_>>());
        let cv = eval_transition_constraints(&curr, &next);
        for (j, &v) in cv.iter().enumerate() {
            if !v.is_zero() {
                return Err(format!("transition constraint {} violated at row {}", j, row));
            }
        }
    }

    // Accumulator constraints, all wrap-around.
    for row in 0..n {
        let curr = TraceView::from_base(&columns.iter().map(|c| c[row]).collect::<Vec<_>>());
        let next_row = if row + 1 < n { row + 1 } else { 0 };
        let next = TraceView::from_base(&columns.iter().map(|c| c[next_row]).collect::<Vec<_>>());
        let curr_acc: Vec<Ext> = accum_columns.iter().map(|c| c[row]).collect();
        let next_acc: Vec<Ext> = accum_columns.iter().map(|c| c[next_row]).collect();
        let cv = permutation::eval_accum_constraints(&curr, &next, &curr_acc, &next_acc, gammas, alphas);
        for (j, &v) in cv.iter().enumerate() {
            if !v.is_zero() {
                return Err(format!("accum constraint {} violated at row {}", j, row));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkvm_core::{build_columns, run, Instruction, Opcode};

    // A small program: r1 = 5; write r1; halt. No memory, no input.
    fn honest_columns() -> (Vec<Vec<BabyBear>>, usize) {
        let program = vec![
            Instruction { op: Opcode::Imm,   a: 1, b: 5, c: 0 },
            Instruction { op: Opcode::Write, a: 1, b: 0, c: 0 },
            Instruction { op: Opcode::Halt,  a: 0, b: 0, c: 0 },
        ];
        let (records, outputs) = run(&program, &[], 1 << 20).unwrap();
        build_columns(&records, &program, &[], &outputs)
    }

    fn view(cols: &[Vec<BabyBear>], row: usize) -> TraceView {
        TraceView::from_base(&cols.iter().map(|c| c[row]).collect::<Vec<_>>())
    }

    fn assert_all_zero(cols: &[Vec<BabyBear>]) {
        let n = cols[0].len();
        for row in 0..n - 1 {
            let cv = eval_transition_constraints(&view(cols, row), &view(cols, row + 1));
            for (j, v) in cv.iter().enumerate() {
                assert!(v.is_zero(), "constraint {} nonzero at honest row {}", j, row);
            }
        }
    }

    fn any_violation(cols: &[Vec<BabyBear>], row: usize) -> bool {
        let n = cols[0].len();
        let next = if row + 1 < n { row + 1 } else { 0 };
        eval_transition_constraints(&view(cols, row), &view(cols, next))
            .iter()
            .any(|v| !v.is_zero())
    }

    #[test]
    fn honest_trace_passes() {
        let (cols, n_real) = honest_columns();
        assert_eq!(n_real, 3);
        assert_all_zero(&cols);
    }

    #[test]
    fn post_halt_repeats_halt_is_enforced() {
        let (mut cols, n_real) = honest_columns();
        let p = n_real + 1;
        assert!(!cols[col::HALT][p].is_zero(), "row {} should be halted", p);
        cols[col::SEL_START + opc::HALT][p] = BabyBear::zero();
        cols[col::SEL_START + opc::ADD][p] = BabyBear::one();
        assert!(any_violation(&cols, p), "POST_HALT_REPEATS_HALT not enforced");
    }

    #[test]
    fn inactive_slot_must_be_zeroed() {
        let (mut cols, _) = honest_columns();
        assert!(cols[col::REG_A_ACT][0].is_zero(), "IMM slot A should be inactive");
        cols[col::REG_A_IDX][0] = BabyBear::from_u32(3);
        cols[col::REG_A_INV][0] = BabyBear::from_u32(3).inverse();
        assert!(any_violation(&cols, 0), "SLOT_INACTIVE_ZEROED not enforced");
    }

    #[test]
    fn sorted_r0_pin_is_enforced() {
        let (mut cols, _) = honest_columns();
        assert!(cols[col::SREG_A][0].is_zero(), "first sorted reg entry should be idx 0");
        cols[col::SREG_A + 1][0] = BabyBear::from_u32(42);
        assert!(any_violation(&cols, 0), "SORTED_R0_PIN not enforced");
    }

    #[test]
    fn rom_multiplicity_range_is_enforced() {
        let (mut cols, _) = honest_columns();
        cols[col::PROG + 5][0] = BabyBear::zero() - BabyBear::one();
        assert!(any_violation(&cols, 0), "ROM_MULT_RANGE not enforced");
    }

    #[test]
    fn strict_diff_rejects_equal_sorted_keys() {
        let (mut cols, _) = honest_columns();
        cols[col::SREG_B][0] = cols[col::SREG_A][0];
        cols[col::SREG_B + 2][0] = cols[col::SREG_A + 2][0];
        assert!(any_violation(&cols, 0), "SORTED_STRICT_DIFF not enforced");
    }

    // The phantom-row memory forgery: on a MEM_USED=0 row the prover sets an
    // arbitrary (MEM_ADDR, MEM_VAL). Pre-fix this passed every constraint and
    // the value leaked into the sorted memory table to poison a later read.
    #[test]
    fn unused_row_cannot_carry_mem_addr() {
        let (mut cols, _) = honest_columns();
        assert!(cols[col::MEM_USED][0].is_zero(), "row 0 (IMM) should not use memory");
        cols[col::MEM_ADDR][0] = BabyBear::from_u32(7);
        assert!(any_violation(&cols, 0), "MEM_UNUSED_ZEROED (addr) not enforced");
    }

    #[test]
    fn unused_row_cannot_carry_mem_val() {
        let (mut cols, _) = honest_columns();
        assert!(cols[col::MEM_USED][0].is_zero(), "row 0 (IMM) should not use memory");
        cols[col::MEM_VAL][0] = BabyBear::from_u32(123);
        assert!(any_violation(&cols, 0), "MEM_UNUSED_ZEROED (val) not enforced");
    }

    #[test]
    fn unused_sorted_entry_must_be_zeroed() {
        let (mut cols, _) = honest_columns();
        // Find an unused sorted-memory row and plant a poisoning (addr, val).
        let n = cols[0].len();
        let row = (0..n)
            .find(|&i| cols[col::SMEM + 4][i].is_zero())
            .expect("an unused sorted-memory row should exist");
        cols[col::SMEM][row] = BabyBear::from_u32(9);
        cols[col::SMEM + 1][row] = BabyBear::from_u32(99);
        assert!(any_violation(&cols, row), "SORTED_MEM_UNUSED_ZEROED not enforced");
    }
}

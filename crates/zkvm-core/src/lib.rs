//! Field-native VM for the zkvm project.
//!
//! 11 instructions, 8 registers (`r0` hardwired to 0), single linear memory
//! addressed by field element. Everything is a BabyBear field element; there
//! are no u32 / signed / overflow semantics. See README for the ISA.

use std::collections::HashMap;

use toyni::babybear::BabyBear;

// ── Opcodes ────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum Opcode {
    Add = 1,
    Sub = 2,
    Mul = 3,
    Imm = 4,
    Load = 5,
    Store = 6,
    Jmp = 7,
    Jz = 8,
    Read = 9,
    Write = 10,
    Halt = 11,
}

impl Opcode {
    pub fn from_u32(v: u32) -> Option<Opcode> {
        Some(match v {
            1 => Opcode::Add, 2 => Opcode::Sub, 3 => Opcode::Mul, 4 => Opcode::Imm,
            5 => Opcode::Load, 6 => Opcode::Store, 7 => Opcode::Jmp, 8 => Opcode::Jz,
            9 => Opcode::Read, 10 => Opcode::Write, 11 => Opcode::Halt,
            _ => return None,
        })
    }

    /// Selector index 0..=10 (one-hot column position).
    pub fn sel_index(self) -> usize {
        (self as u32 - 1) as usize
    }
}

pub const NUM_OPCODES: usize = 11;
pub const NUM_REGS: usize = 8;

#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub op: Opcode,
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

// ── BabyBear-on-u32 helpers (so the runtime never overflows) ───────────

pub const P: u32 = 2_013_265_921;

#[inline]
fn bb_add(a: u32, b: u32) -> u32 {
    let s = a as u64 + b as u64;
    let p = P as u64;
    if s >= p { (s - p) as u32 } else { s as u32 }
}
#[inline]
fn bb_sub(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { a + P - b }
}
#[inline]
fn bb_mul(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % P as u64) as u32
}

// ── Execution ─────────────────────────────────────────────────────────

pub struct VmState {
    pub regs: [u32; NUM_REGS],
    pub pc: u32,
    pub mem: HashMap<u32, u32>,
    pub i_in: u32,
    pub i_out: u32,
    pub halted: bool,
}

impl VmState {
    pub fn new() -> Self {
        Self {
            regs: [0; NUM_REGS],
            pc: 0,
            mem: HashMap::new(),
            i_in: 0,
            i_out: 0,
            halted: false,
        }
    }
}

/// What the AIR needs to see for one cycle.
#[derive(Debug, Clone)]
pub struct StepRecord {
    pub clk: u32,
    pub pc: u32,
    pub next_pc: u32,
    pub instr: Instruction,
    pub halt_post: u32,
    pub i_in_pre: u32,
    pub i_in_post: u32,
    pub i_out_pre: u32,
    pub i_out_post: u32,
    /// 3 register-access slots: A, B, C. Each is (idx, val, is_write).
    /// Unused slots are reads of `r0` => (0, 0, 0).
    pub reg: [(u32, u32, u32); 3],
    /// (addr, val, is_write, used) for the (single) memory access this row.
    pub mem: (u32, u32, u32, u32),
}

pub fn run(
    program: &[Instruction],
    public_inputs: &[u32],
    max_steps: usize,
) -> Result<(Vec<StepRecord>, Vec<u32>), String> {
    let mut s = VmState::new();
    let mut trace = Vec::new();
    let mut outputs = Vec::new();

    while !s.halted && trace.len() < max_steps {
        let pc = s.pc;
        let instr = *program.get(pc as usize).ok_or_else(|| {
            format!("PC {} out of program ROM bounds (len={})", pc, program.len())
        })?;
        let clk = trace.len() as u32;
        let i_in_pre = s.i_in;
        let i_out_pre = s.i_out;
        let mut reg = [(0u32, 0u32, 0u32); 3];
        let mut mem = (0u32, 0u32, 0u32, 0u32);
        let mut next_pc = pc + 1;

        let read = |r: u32, regs: &[u32; NUM_REGS]| if r == 0 { 0 } else { regs[r as usize] };
        let write = |r: u32, v: u32, regs: &mut [u32; NUM_REGS]| {
            if r != 0 { regs[r as usize] = v; }
        };

        match instr.op {
            Opcode::Add | Opcode::Sub | Opcode::Mul => {
                let (rd, ra, rb) = (instr.a, instr.b, instr.c);
                let va = read(ra, &s.regs);
                let vb = read(rb, &s.regs);
                let vd = match instr.op {
                    Opcode::Add => bb_add(va, vb),
                    Opcode::Sub => bb_sub(va, vb),
                    Opcode::Mul => bb_mul(va, vb),
                    _ => unreachable!(),
                };
                write(rd, vd, &mut s.regs);
                reg[0] = (ra, va, 0);
                reg[1] = (rb, vb, 0);
                reg[2] = (rd, vd, 1);
            }
            Opcode::Imm => {
                let (rd, k) = (instr.a, instr.b);
                write(rd, k, &mut s.regs);
                reg[2] = (rd, k, 1);
            }
            Opcode::Load => {
                let (rd, ra) = (instr.a, instr.b);
                let addr = read(ra, &s.regs);
                let val = *s.mem.get(&addr).unwrap_or(&0);
                write(rd, val, &mut s.regs);
                reg[0] = (ra, addr, 0);
                reg[2] = (rd, val, 1);
                mem = (addr, val, 0, 1);
            }
            Opcode::Store => {
                let (ra, rb) = (instr.a, instr.b);
                let addr = read(ra, &s.regs);
                let val = read(rb, &s.regs);
                s.mem.insert(addr, val);
                reg[0] = (ra, addr, 0);
                reg[1] = (rb, val, 0);
                mem = (addr, val, 1, 1);
            }
            Opcode::Jmp => { next_pc = instr.a; }
            Opcode::Jz => {
                let (ra, k) = (instr.a, instr.b);
                let va = read(ra, &s.regs);
                reg[0] = (ra, va, 0);
                if va == 0 { next_pc = k; }
            }
            Opcode::Read => {
                let rd = instr.a;
                let val = *public_inputs.get(s.i_in as usize).ok_or_else(|| {
                    format!("READ past end of public_inputs (i_in={})", s.i_in)
                })?;
                write(rd, val, &mut s.regs);
                reg[2] = (rd, val, 1);
                s.i_in += 1;
            }
            Opcode::Write => {
                let ra = instr.a;
                let val = read(ra, &s.regs);
                reg[0] = (ra, val, 0);
                outputs.push(val);
                s.i_out += 1;
            }
            Opcode::Halt => {
                s.halted = true;
                next_pc = pc;
            }
        }

        s.pc = next_pc;

        trace.push(StepRecord {
            clk, pc, next_pc, instr,
            halt_post: s.halted as u32,
            i_in_pre, i_in_post: s.i_in,
            i_out_pre, i_out_post: s.i_out,
            reg, mem,
        });
    }

    if !s.halted {
        return Err(format!("VM did not halt within {} steps", max_steps));
    }
    Ok((trace, outputs))
}

// ── Column layout ─────────────────────────────────────────────────────

pub mod col {
    pub const CLK: usize = 0;
    pub const PC: usize = 1;
    pub const NEXT_PC: usize = 2;

    pub const OPCODE: usize = 3;
    pub const OP_A: usize = 4;
    pub const OP_B: usize = 5;
    pub const OP_C: usize = 6;

    pub const HALT: usize = 7;
    pub const I_IN: usize = 8;       // i_in_pre (cursor BEFORE this row)
    pub const I_OUT: usize = 9;      // i_out_pre

    pub const REG_A_IDX: usize = 10;
    pub const REG_A_VAL: usize = 11;
    pub const REG_A_WR: usize = 12;
    pub const REG_A_INV: usize = 13;
    pub const REG_B_IDX: usize = 14;
    pub const REG_B_VAL: usize = 15;
    pub const REG_B_WR: usize = 16;
    pub const REG_B_INV: usize = 17;
    pub const REG_C_IDX: usize = 18;
    pub const REG_C_VAL: usize = 19;
    pub const REG_C_WR: usize = 20;
    pub const REG_C_INV: usize = 21;

    pub const MEM_ADDR: usize = 22;
    pub const MEM_VAL: usize = 23;
    pub const MEM_WR: usize = 24;
    pub const MEM_USED: usize = 25;

    /// JZ helper: 1 if REG_A_VAL == 0, else 0.
    pub const JZ_IS_ZERO: usize = 26;
    /// JZ helper: inverse of REG_A_VAL when nonzero, else arbitrary (we set 0).
    pub const JZ_VAL_INV: usize = 27;

    /// One-hot opcode selectors (11 columns).
    pub const SEL_START: usize = 28;

    /// Sorted register table: 3 slots × (idx, val, clk, is_write, same_idx, diff_inv).
    pub const SREG_A: usize = 39;
    pub const SREG_B: usize = 45;
    pub const SREG_C: usize = 51;

    /// Sorted memory: (addr, val, clk, is_write, used, same_addr, diff_inv).
    pub const SMEM: usize = 57;

    /// Program ROM table: (addr, opcode, op_a, op_b, op_c, mult).
    pub const PROG: usize = 64;

    /// Public input/output tables: (idx, val, mult).
    pub const PUB_IN: usize = 70;
    pub const PUB_OUT: usize = 73;

    /// Bit decomposition of (sort-diff - 1) for range-checking the sorted
    /// table's ordering. 4 transitions × 16 bits = 64 columns.
    ///   AB: B-vs-A inside the row (sorted register slots)
    ///   BC: C-vs-B inside the row
    ///   CA: A[i+1]-vs-C[i] across rows
    ///   M : sorted memory next-row vs current-row
    pub const DIFF_BITS_AB: usize = 76;
    pub const DIFF_BITS_BC: usize = 92;
    pub const DIFF_BITS_CA: usize = 108;
    pub const DIFF_BITS_M : usize = 124;

    pub const NUM_COLS: usize = 140;
}

pub const NUM_TRACE_COLS: usize = col::NUM_COLS;

/// 5 arguments × 4 channels = 20 accumulator columns.
/// Layout: arg X channel ch lives at index (X_BASE + ch).
pub const NUM_ACCUM_COLS: usize = 20;
pub const NUM_CHANNELS: usize = 4;
pub mod accum {
    pub const REG: usize = 0;       // 0..3 (grand product)
    pub const MEM: usize = 4;       // 4..7 (grand product)
    pub const PROG: usize = 8;      // 8..11 (LogUp)
    pub const PUB_IN: usize = 12;   // 12..15 (LogUp)
    pub const PUB_OUT: usize = 16;  // 16..19 (LogUp)
}

// ── Trace builder ─────────────────────────────────────────────────────

pub fn build_columns(
    records: &[StepRecord],
    program: &[Instruction],
    public_inputs: &[u32],
    public_outputs: &[u32],
) -> (Vec<Vec<BabyBear>>, usize) {
    let n_real = records.len();
    assert!(n_real > 0, "trace cannot be empty");
    assert!(records.last().unwrap().instr.op == Opcode::Halt, "last real row must be HALT");

    let n = n_real.next_power_of_two().max(1 << 8);
    let mut cols: Vec<Vec<BabyBear>> = vec![vec![BabyBear::zero(); n]; NUM_TRACE_COLS];

    let last = &records[n_real - 1];

    // Real rows.
    for (i, r) in records.iter().enumerate() {
        write_main(&mut cols, i, r);
    }
    // Padding rows: replay HALT at the halt PC, leave I/O cursors frozen.
    for i in n_real..n {
        let pad = StepRecord {
            clk: i as u32,
            pc: last.pc,
            next_pc: last.pc,
            instr: Instruction { op: Opcode::Halt, a: 0, b: 0, c: 0 },
            halt_post: 1,
            i_in_pre: last.i_in_post,
            i_in_post: last.i_in_post,
            i_out_pre: last.i_out_post,
            i_out_post: last.i_out_post,
            reg: [(0, 0, 0); 3],
            mem: (0, 0, 0, 0),
        };
        write_main(&mut cols, i, &pad);
    }

    // Sorted register-access table.
    let mut accs: Vec<(u32, u32, u32, u32)> = Vec::with_capacity(3 * n);
    for r in records.iter() {
        for &(idx, val, wr) in &r.reg {
            accs.push((idx, val, r.clk, wr));
        }
    }
    for i in n_real..n {
        for _ in 0..3 { accs.push((0, 0, i as u32, 0)); }
    }
    // Sort by (idx, clk, is_write) so reads come before writes within the
    // same (idx, clk) — this preserves "read sees the old value, then the
    // write commits the new value" semantics.
    accs.sort_by_key(|t| (t.0, t.2, t.3));
    for (i, chunk) in accs.chunks(3).enumerate() {
        write_sreg(&mut cols, i, chunk);
    }

    // Sorted memory table.
    let mut maccs: Vec<(u32, u32, u32, u32, u32)> = Vec::with_capacity(n);
    for r in records.iter() {
        let (addr, val, wr, used) = r.mem;
        maccs.push((addr, val, r.clk, wr, used));
    }
    for i in n_real..n {
        maccs.push((0, 0, i as u32, 0, 0));
    }
    // Unused entries first (used=0), then used entries sorted by (addr, clk).
    maccs.sort_by_key(|e| (e.4, e.0, e.2));
    for (i, e) in maccs.iter().enumerate() {
        write_smem(&mut cols, i, *e);
    }

    // Program ROM table with multiplicities.
    let mut mult: HashMap<u32, u32> = HashMap::new();
    for r in records.iter() {
        *mult.entry(r.pc).or_insert(0) += 1;
    }
    *mult.entry(last.pc).or_insert(0) += (n - n_real) as u32;
    for (i, ins) in program.iter().enumerate() {
        if i >= n { break; }
        let addr = i as u32;
        let m = mult.remove(&addr).unwrap_or(0);
        cols[col::PROG    ][i] = BabyBear::from_u32(addr);
        cols[col::PROG + 1][i] = BabyBear::from_u32(ins.op as u32);
        cols[col::PROG + 2][i] = BabyBear::from_u32(ins.a);
        cols[col::PROG + 3][i] = BabyBear::from_u32(ins.b);
        cols[col::PROG + 4][i] = BabyBear::from_u32(ins.c);
        cols[col::PROG + 5][i] = BabyBear::from_u32(m);
    }
    // Any leftover multiplicities (shouldn't happen for honest provers) are dropped.

    for (j, &v) in public_inputs.iter().enumerate() {
        if j >= n { break; }
        cols[col::PUB_IN    ][j] = BabyBear::from_u32(j as u32);
        cols[col::PUB_IN + 1][j] = BabyBear::from_u32(v);
        cols[col::PUB_IN + 2][j] = BabyBear::one();
    }
    for (j, &v) in public_outputs.iter().enumerate() {
        if j >= n { break; }
        cols[col::PUB_OUT    ][j] = BabyBear::from_u32(j as u32);
        cols[col::PUB_OUT + 1][j] = BabyBear::from_u32(v);
        cols[col::PUB_OUT + 2][j] = BabyBear::one();
    }

    fill_aux(&mut cols);
    (cols, n_real)
}

fn write_main(cols: &mut [Vec<BabyBear>], i: usize, r: &StepRecord) {
    cols[col::CLK    ][i] = BabyBear::from_u32(r.clk);
    cols[col::PC     ][i] = BabyBear::from_u32(r.pc);
    cols[col::NEXT_PC][i] = BabyBear::from_u32(r.next_pc);
    cols[col::OPCODE ][i] = BabyBear::from_u32(r.instr.op as u32);
    cols[col::OP_A   ][i] = BabyBear::from_u32(r.instr.a);
    cols[col::OP_B   ][i] = BabyBear::from_u32(r.instr.b);
    cols[col::OP_C   ][i] = BabyBear::from_u32(r.instr.c);
    cols[col::HALT   ][i] = BabyBear::from_u32(r.halt_post);
    cols[col::I_IN   ][i] = BabyBear::from_u32(r.i_in_pre);
    cols[col::I_OUT  ][i] = BabyBear::from_u32(r.i_out_pre);

    let bases = [col::REG_A_IDX, col::REG_B_IDX, col::REG_C_IDX];
    for (k, &(idx, val, wr)) in r.reg.iter().enumerate() {
        cols[bases[k]    ][i] = BabyBear::from_u32(idx);
        cols[bases[k] + 1][i] = BabyBear::from_u32(val);
        cols[bases[k] + 2][i] = BabyBear::from_u32(wr);
        // INV column: idx == 0 ? 0 : idx^-1
        if idx == 0 {
            cols[bases[k] + 3][i] = BabyBear::zero();
        } else {
            cols[bases[k] + 3][i] = BabyBear::from_u32(idx).inverse();
        }
    }

    let (m_addr, m_val, m_wr, m_used) = r.mem;
    cols[col::MEM_ADDR][i] = BabyBear::from_u32(m_addr);
    cols[col::MEM_VAL ][i] = BabyBear::from_u32(m_val);
    cols[col::MEM_WR  ][i] = BabyBear::from_u32(m_wr);
    cols[col::MEM_USED][i] = BabyBear::from_u32(m_used);

    // JZ helpers (only meaningful when sel_jz=1, but always written so the
    // constraints are well-defined on every row).
    let ra_val = r.reg[0].1;
    if ra_val == 0 {
        cols[col::JZ_IS_ZERO][i] = BabyBear::one();
        cols[col::JZ_VAL_INV][i] = BabyBear::zero();
    } else {
        cols[col::JZ_IS_ZERO][i] = BabyBear::zero();
        cols[col::JZ_VAL_INV][i] = BabyBear::from_u32(ra_val).inverse();
    }

    cols[col::SEL_START + r.instr.op.sel_index()][i] = BabyBear::one();
}

fn write_sreg(cols: &mut [Vec<BabyBear>], i: usize, chunk: &[(u32, u32, u32, u32)]) {
    let bases = [col::SREG_A, col::SREG_B, col::SREG_C];
    for k in 0..3 {
        let (idx, val, clk, wr) = if k < chunk.len() { chunk[k] } else { (0, 0, 0, 0) };
        cols[bases[k]    ][i] = BabyBear::from_u32(idx);
        cols[bases[k] + 1][i] = BabyBear::from_u32(val);
        cols[bases[k] + 2][i] = BabyBear::from_u32(clk);
        cols[bases[k] + 3][i] = BabyBear::from_u32(wr);
    }
}

fn write_smem(cols: &mut [Vec<BabyBear>], i: usize, e: (u32, u32, u32, u32, u32)) {
    let (addr, val, clk, wr, used) = e;
    cols[col::SMEM    ][i] = BabyBear::from_u32(addr);
    cols[col::SMEM + 1][i] = BabyBear::from_u32(val);
    cols[col::SMEM + 2][i] = BabyBear::from_u32(clk);
    cols[col::SMEM + 3][i] = BabyBear::from_u32(wr);
    cols[col::SMEM + 4][i] = BabyBear::from_u32(used);
}

fn fill_aux(cols: &mut [Vec<BabyBear>]) {
    let n = cols[0].len();

    // Sorted-reg cross-slot aux + diff bit decomposition.
    for i in 0..n {
        // B vs A in same row.
        fill_sort_aux_reg(cols, i, col::SREG_A, col::SREG_B, col::SREG_A + 4, col::DIFF_BITS_AB, i + 1 < n);
        // C vs B in same row.
        fill_sort_aux_reg(cols, i, col::SREG_B, col::SREG_C, col::SREG_B + 4, col::DIFF_BITS_BC, i + 1 < n);
        // A[i+1] vs C[i] across rows. The cross-row case looks at row i+1's A.
        let prev_idx = cols[col::SREG_C][i];
        let prev_clk = cols[col::SREG_C + 2][i];
        let (next_idx, next_clk) = if i + 1 < n {
            (cols[col::SREG_A][i + 1], cols[col::SREG_A + 2][i + 1])
        } else {
            (cols[col::SREG_A][0], cols[col::SREG_A + 2][0])
        };
        fill_sort_aux_with_clks(cols, i, col::SREG_C + 4, col::DIFF_BITS_CA,
            prev_idx, prev_clk, next_idx, next_clk, i + 1 < n);
    }

    // Sorted-mem aux + diff bit decomposition.
    for i in 0..n {
        let prev_addr = cols[col::SMEM][i];
        let prev_clk  = cols[col::SMEM + 2][i];
        let (next_addr, next_clk) = if i + 1 < n {
            (cols[col::SMEM][i + 1], cols[col::SMEM + 2][i + 1])
        } else {
            (cols[col::SMEM][0], cols[col::SMEM + 2][0])
        };
        fill_sort_aux_with_clks(cols, i, col::SMEM + 5, col::DIFF_BITS_M,
            prev_addr, prev_clk, next_addr, next_clk, i + 1 < n);
    }
}

/// Fill same_idx + diff_inv aux for a register slot transition WITHIN the same row.
fn fill_sort_aux_reg(
    cols: &mut [Vec<BabyBear>],
    i: usize,
    prev_base: usize,
    next_base: usize,
    aux_base: usize,
    bits_base: usize,
    is_in_trace: bool,
) {
    let prev_idx = cols[prev_base    ][i];
    let prev_clk = cols[prev_base + 2][i];
    let next_idx = cols[next_base    ][i];
    let next_clk = cols[next_base + 2][i];
    fill_sort_aux_with_clks(cols, i, aux_base, bits_base,
        prev_idx, prev_clk, next_idx, next_clk, is_in_trace);
}

/// Common path: fill (same_idx, diff_inv) at aux_base and the 16-bit
/// decomposition of (diff - 1) at bits_base.
///
/// `is_in_trace` is `false` only when this transition is the last-row →
/// first-row wrap; in that case the diff doesn't fit the strict-ordering
/// shape (it's "negative") so we leave the bits at zero. The AIR marks the
/// range-check constraint as a main transition so it's excepted at the
/// last row.
fn fill_sort_aux_with_clks(
    cols: &mut [Vec<BabyBear>],
    i: usize,
    aux_base: usize,
    bits_base: usize,
    prev_idx: BabyBear,
    prev_clk: BabyBear,
    next_idx: BabyBear,
    next_clk: BabyBear,
    is_in_trace: bool,
) {
    let same = prev_idx == next_idx;
    if same {
        cols[aux_base    ][i] = BabyBear::one();
        cols[aux_base + 1][i] = BabyBear::zero();
    } else {
        cols[aux_base    ][i] = BabyBear::zero();
        cols[aux_base + 1][i] = (next_idx - prev_idx).inverse();
    }

    if !is_in_trace {
        // Wrap row: leave bits at zero; the AIR exempts this row.
        return;
    }

    // diff = same ? (next_clk - prev_clk) : (next_idx - prev_idx).
    // Honest sort produces diff ∈ [0, 2^16) (consecutive same-(idx,clk,wr)
    // tuples can repeat with diff=0; differing tuples are monotone with
    // diff > 0). We encode diff directly as 16 boolean bits. A reversed
    // ordering yields diff ≈ 2^31 in the field, which exceeds the 16-bit
    // budget and the bit-recon constraint catches it.
    let v = if same {
        let nc = next_clk.value as i64;
        let pc = prev_clk.value as i64;
        (nc - pc) as u64
    } else {
        let ni = next_idx.value as i64;
        let pi = prev_idx.value as i64;
        (ni - pi) as u64
    };
    for k in 0..16 {
        let bit = ((v >> k) & 1) as u32;
        cols[bits_base + k][i] = BabyBear::from_u32(bit);
    }
}

// ── Program hash (used to bind the ROM) ───────────────────────────────

pub fn hash_program(program: &[Instruction]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    for (i, ins) in program.iter().enumerate() {
        h.update((i as u32).to_le_bytes());
        h.update((ins.op as u32).to_le_bytes());
        h.update(ins.a.to_le_bytes());
        h.update(ins.b.to_le_bytes());
        h.update(ins.c.to_le_bytes());
    }
    h.finalize().into()
}

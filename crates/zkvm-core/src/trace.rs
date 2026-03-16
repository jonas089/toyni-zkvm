/// Execution trace: one row per CPU step, used by the constraint system.

use crate::cpu::OpcodeClass;
use toyni::babybear::BabyBear;

/// A single row of the execution trace.
#[derive(Debug, Clone)]
pub struct TraceRow {
    pub clk: u32,
    pub pc: u32,
    pub instruction: u32,
    pub rs1_idx: u32,
    pub rs2_idx: u32,
    pub rd_idx: u32,
    pub rs1_val: u32,
    pub rs2_val: u32,
    pub rd_val: u32,
    pub imm: u32,
    pub next_pc: u32,
    pub mem_addr: u32,
    pub mem_val: u32,
    pub is_load: bool,
    pub is_store: bool,
    pub branch_taken: bool,
    pub alu_carry: u32,
    pub pc_carry: u32,
    pub bits_a: [u32; 32],
    pub bits_b: [u32; 32],
    pub shift_stages: [u32; 5],
    pub mem_addr_carry: u32,
    pub jalr_bit0: u32,
    pub branch_diff_inv: u32,
    pub shift_carry: [u32; 5],
    pub instr_bits: [u32; 32],
    pub rs1_idx_inv: u32,
    pub rs2_idx_inv: u32,
    pub is_halted: bool,
    pub opcode_class: OpcodeClass,
}

impl TraceRow {
    pub fn nop(clk: u32, pc: u32, next_pc: u32) -> Self {
        Self {
            clk, pc, next_pc,
            instruction: 0x00000013,
            rs1_idx: 0, rs2_idx: 0, rd_idx: 0,
            rs1_val: 0, rs2_val: 0, rd_val: 0,
            imm: 0, mem_addr: 0, mem_val: 0,
            is_load: false, is_store: false, branch_taken: false,
            alu_carry: 0, pc_carry: 0,
            bits_a: [0; 32], bits_b: [0; 32], shift_stages: [0; 5],
            mem_addr_carry: 0, jalr_bit0: 0, branch_diff_inv: 0,
            shift_carry: [0; 5],
            instr_bits: decompose_nop_bits(),
            rs1_idx_inv: 0, rs2_idx_inv: 0,
            is_halted: false,
            opcode_class: OpcodeClass::Addi,
        }
    }
}

/// Decompose NOP instruction (0x00000013 = ADDI x0, x0, 0) into bits.
fn decompose_nop_bits() -> [u32; 32] {
    let w: u32 = 0x00000013;
    let mut bits = [0u32; 32];
    for i in 0..32 {
        bits[i] = (w >> i) & 1;
    }
    bits
}

/// Column indices in the flattened trace.
pub mod col {
    pub const CLK: usize = 0;
    pub const PC: usize = 1;
    pub const INSTRUCTION: usize = 2;
    pub const RS1_IDX: usize = 3;
    pub const RS2_IDX: usize = 4;
    pub const RD_IDX: usize = 5;
    pub const RS1_VAL: usize = 6;
    pub const RS2_VAL: usize = 7;
    pub const RD_VAL: usize = 8;
    pub const IMM: usize = 9;
    pub const NEXT_PC: usize = 10;
    pub const MEM_ADDR: usize = 11;
    pub const MEM_VAL: usize = 12;
    pub const IS_LOAD: usize = 13;
    pub const IS_STORE: usize = 14;
    pub const BRANCH_TAKEN: usize = 15;
    pub const ALU_CARRY: usize = 16;
    pub const PC_CARRY: usize = 17;
    pub const BITS_A_START: usize = 18;
    pub const BITS_B_START: usize = 50;
    pub const SHIFT_STAGE_START: usize = 82;
    // ── Soundness auxiliary columns ──
    pub const MEM_ADDR_CARRY: usize = 87;
    pub const JALR_BIT0: usize = 88;
    pub const BRANCH_DIFF_INV: usize = 89;
    pub const SHIFT_CARRY_START: usize = 90; // 5 columns (90-94)
    // ── Sorted memory table ──
    pub const SORTED_MEM_ADDR: usize = 95;
    pub const SORTED_MEM_VAL: usize = 96;
    pub const SORTED_MEM_CLK: usize = 97;
    pub const SORTED_MEM_IS_WRITE: usize = 98;
    pub const SORTED_MEM_SAME_ADDR: usize = 99;
    pub const SORTED_MEM_DIFF_INV: usize = 100;
    // ── Sorted register table (3 slots per row) ──
    pub const SORTED_REG_A_IDX: usize = 101;
    pub const SORTED_REG_A_VAL: usize = 102;
    pub const SORTED_REG_A_CLK: usize = 103;
    pub const SORTED_REG_A_IS_WRITE: usize = 104;
    pub const SORTED_REG_A_SAME_IDX: usize = 105;
    pub const SORTED_REG_A_DIFF_INV: usize = 106;
    pub const SORTED_REG_B_IDX: usize = 107;
    pub const SORTED_REG_B_VAL: usize = 108;
    pub const SORTED_REG_B_CLK: usize = 109;
    pub const SORTED_REG_B_IS_WRITE: usize = 110;
    pub const SORTED_REG_B_SAME_IDX: usize = 111;
    pub const SORTED_REG_B_DIFF_INV: usize = 112;
    pub const SORTED_REG_C_IDX: usize = 113;
    pub const SORTED_REG_C_VAL: usize = 114;
    pub const SORTED_REG_C_CLK: usize = 115;
    pub const SORTED_REG_C_IS_WRITE: usize = 116;
    pub const SORTED_REG_C_SAME_IDX: usize = 117;
    pub const SORTED_REG_C_DIFF_INV: usize = 118;
    // ── Program table (fixed ROM + multiplicities) ──
    pub const PROG_ADDR: usize = 119;
    pub const PROG_INSTR: usize = 120;
    pub const PROG_MULT: usize = 121;
    // ── Range check limbs (8 values × 2 limbs) ──
    pub const LIMB_START: usize = 122; // 16 columns (122-137)
    pub const RANGE_TABLE_VAL: usize = 138;
    pub const RANGE_MULT: usize = 139;
    // ── Instruction bit decomposition (32 bits) ──
    pub const INSTR_BIT_START: usize = 140; // 32 columns (140-171)
    // ── Register index inverses (for x0 constraints) ──
    pub const RS1_IDX_INV: usize = 172;
    pub const RS2_IDX_INV: usize = 173;
    // ── Ordering diff limbs (sorted table enforcement) ──
    pub const ORDERING_MEM_LO: usize = 174;
    pub const ORDERING_MEM_HI: usize = 175;
    pub const ORDERING_REG_A_LO: usize = 176;
    pub const ORDERING_REG_A_HI: usize = 177;
    pub const ORDERING_REG_B_LO: usize = 178;
    pub const ORDERING_REG_B_HI: usize = 179;
    pub const ORDERING_REG_C_LO: usize = 180;
    pub const ORDERING_REG_C_HI: usize = 181;
    // ── Halting flag ──
    pub const IS_HALTED: usize = 182;
    // ── Output table (addr, val, multiplicity) ──
    pub const OUTPUT_ADDR: usize = 183;
    pub const OUTPUT_VAL: usize = 184;
    pub const OUTPUT_MULT: usize = 185;
    // ── Opcode selectors ──
    pub const OPCODE_SEL_START: usize = 186;
    pub const NUM_FIXED: usize = 186;
}

use crate::cpu::NUM_OPCODE_CLASSES;

/// Total main trace columns.
pub const NUM_TRACE_COLS: usize = col::NUM_FIXED + NUM_OPCODE_CLASSES;

/// Number of accumulator columns (separate commitment phase).
/// 4 parallel runs × 3 arguments (mem, reg, fetch) = 12
/// + 1 LogUp range accumulator + 4 LogUp range helpers = 5
/// + 2 LogUp ordering helpers = 2
/// Total: 19
pub const NUM_ACCUM_COLS: usize = 19;

/// A register access tuple: (idx, val, clk, is_write).
#[derive(Clone, Copy, Debug)]
pub struct RegAccess {
    pub idx: u32,
    pub val: u32,
    pub clk: u32,
    pub is_write: u32,
}

/// Full execution trace with sorted auxiliary tables.
pub struct ExecutionTrace {
    pub rows: Vec<TraceRow>,
    /// Sorted memory access table (one entry per row, sorted by addr then clk).
    pub sorted_mem: Vec<[u32; 4]>, // (addr, val, clk, is_write)
    /// Sorted memory auxiliaries: (same_addr, diff_inv) per row.
    pub sorted_mem_aux: Vec<[u32; 2]>,
    /// Sorted register access table (3 entries per row, sorted by idx then clk).
    pub sorted_reg: Vec<[[u32; 4]; 3]>, // 3 slots of (idx, val, clk, is_write)
    /// Sorted register auxiliaries: (same_idx, diff_inv) per slot × 3 slots per row.
    pub sorted_reg_aux: Vec<[[u32; 2]; 3]>,
    /// Program ROM table: (addr, instr, multiplicity) per row.
    /// Contains fixed ROM entries + padding NOPs + filler.
    pub prog_table: Vec<[u32; 3]>,
    /// Range check limb decompositions: 16 limbs per row (8 values × 2 limbs).
    pub limbs: Vec<[u32; 24]>,
    /// Range table multiplicities per row.
    pub range_mult: Vec<u32>,
    /// Ordering diff limbs: [lo, hi] for memory, [[lo, hi]; 3] for registers.
    pub ordering_mem_limbs: Vec<[u32; 2]>,
    pub ordering_reg_limbs: Vec<[[u32; 2]; 3]>,
    /// Output table: (addr, val, multiplicity) per row.
    pub output_table: Vec<[u32; 3]>,
    /// Number of real execution steps (before padding).
    pub num_real_steps: usize,
}

impl ExecutionTrace {
    pub fn new() -> Self {
        Self {
            rows: Vec::new(),
            sorted_mem: Vec::new(),
            sorted_mem_aux: Vec::new(),
            sorted_reg: Vec::new(),
            sorted_reg_aux: Vec::new(),
            prog_table: Vec::new(),
            limbs: Vec::new(),
            range_mult: Vec::new(),
            ordering_mem_limbs: Vec::new(),
            ordering_reg_limbs: Vec::new(),
            output_table: Vec::new(),
            num_real_steps: 0,
        }
    }

    pub fn push(&mut self, row: TraceRow) {
        self.rows.push(row);
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn pad_to_power_of_two(&mut self) {
        if self.rows.is_empty() {
            return;
        }
        // Record real execution length before padding
        if self.num_real_steps == 0 {
            self.num_real_steps = self.rows.len();
        }
        // Minimum 65536 rows so the range table [0, 2^16) fits in the trace.
        let min_size = 1 << 16;
        let target = self.rows.len().next_power_of_two().max(min_size);
        // All padding NOPs use a synthetic PC that's outside the program's address space.
        // IMPORTANT: Must be < BabyBear field modulus (2013265921) to avoid field reduction.
        // Using 0x70000000 = 1879048192, which is safely in-range and unlikely to collide.
        let padding_pc = 0x70000000u32;
        // Padding rows loop on themselves: NEXT_PC = PC (satisfies PC transition constraint)
        let padding_next_pc = padding_pc;
        while self.rows.len() < target {
            let clk = self.rows.len() as u32;
            let mut row = TraceRow::nop(clk, padding_pc, padding_next_pc);
            // Post-halt padding rows are marked as halted
            row.is_halted = true;
            self.rows.push(row);
        }
    }

    /// Generate sorted auxiliary tables from the execution trace.
    /// Must be called after padding and before to_columns().
    pub fn prepare_sorted_tables(&mut self, _program: &[(u32, u32)]) {
        let n = self.rows.len();

        // ── Sorted memory table ──────────────────────────────────────
        let mut mem_entries: Vec<[u32; 4]> = self.rows.iter().map(|row| {
            if row.is_load || row.is_store {
                [row.mem_addr, row.mem_val, row.clk, row.is_store as u32]
            } else {
                [0, 0, row.clk, 0]
            }
        }).collect();
        mem_entries.sort_by_key(|e| (e[0], e[2]));
        self.sorted_mem = mem_entries;

        // Compute memory auxiliaries: same_addr, diff_inv
        self.sorted_mem_aux = vec![[0u32; 2]; n];
        for i in 1..n {
            let curr_addr = self.sorted_mem[i][0];
            let prev_addr = self.sorted_mem[i - 1][0];
            if curr_addr == prev_addr {
                self.sorted_mem_aux[i][0] = 1; // same_addr = 1
                self.sorted_mem_aux[i][1] = 0; // diff_inv = 0
            } else {
                self.sorted_mem_aux[i][0] = 0; // same_addr = 0
                let diff = BabyBear::from_u32(curr_addr) - BabyBear::from_u32(prev_addr);
                self.sorted_mem_aux[i][1] = diff.inverse().value as u32;
            }
        }

        // ── Sorted register table ────────────────────────────────────
        let mut reg_entries: Vec<[u32; 4]> = Vec::with_capacity(3 * n);
        for row in &self.rows {
            reg_entries.push([row.rs1_idx, row.rs1_val, row.clk, 0]);
            reg_entries.push([row.rs2_idx, row.rs2_val, row.clk, 0]);
            reg_entries.push([row.rd_idx, row.rd_val, row.clk, 1]);
        }
        reg_entries.sort_by_key(|e| (e[0], e[2], e[3]));

        self.sorted_reg = Vec::with_capacity(n);
        for chunk in reg_entries.chunks(3) {
            self.sorted_reg.push([chunk[0], chunk[1], chunk[2]]);
        }

        // Compute register auxiliaries for cross-slot transitions.
        // The sorted order is: A[0], B[0], C[0], A[1], B[1], C[1], ...
        // Slot A aux: B[i] vs A[i] (within row)
        // Slot B aux: C[i] vs B[i] (within row)
        // Slot C aux: A[i+1] vs C[i] (across row boundary)
        self.sorted_reg_aux = vec![[[0u32; 2]; 3]; n];
        for i in 0..n {
            // Slot A aux: compare B[i] vs A[i]
            {
                let curr = self.sorted_reg[i][0][0]; // A idx
                let next = self.sorted_reg[i][1][0]; // B idx
                if next == curr {
                    self.sorted_reg_aux[i][0] = [1, 0];
                } else {
                    let diff = BabyBear::from_u32(next) - BabyBear::from_u32(curr);
                    self.sorted_reg_aux[i][0] = [0, diff.inverse().value as u32];
                }
            }
            // Slot B aux: compare C[i] vs B[i]
            {
                let curr = self.sorted_reg[i][1][0]; // B idx
                let next = self.sorted_reg[i][2][0]; // C idx
                if next == curr {
                    self.sorted_reg_aux[i][1] = [1, 0];
                } else {
                    let diff = BabyBear::from_u32(next) - BabyBear::from_u32(curr);
                    self.sorted_reg_aux[i][1] = [0, diff.inverse().value as u32];
                }
            }
            // Slot C aux: compare A[i+1] vs C[i]
            if i + 1 < n {
                let curr = self.sorted_reg[i][2][0]; // C idx
                let next = self.sorted_reg[i + 1][0][0]; // A[i+1] idx
                if next == curr {
                    self.sorted_reg_aux[i][2] = [1, 0];
                } else {
                    let diff = BabyBear::from_u32(next) - BabyBear::from_u32(curr);
                    self.sorted_reg_aux[i][2] = [0, diff.inverse().value as u32];
                }
            }
        }

        // ── Program table (fixed ROM + padding + filler) ────────────
        // Build a fixed ROM table from the actual program, with multiplicities.
        let mut rom: Vec<(u32, u32)> = _program.to_vec();
        rom.sort_by_key(|&(a, _)| a);
        rom.dedup_by_key(|e| e.0);
        let m = rom.len();

        // Count execution multiplicities (how many times each address was fetched)
        // Only count real execution steps - padding is handled separately
        let mut mult_map = std::collections::HashMap::new();
        for i in 0..self.num_real_steps {
            *mult_map.entry(self.rows[i].pc).or_insert(0u32) += 1;
        }

        let padding_count = n - self.num_real_steps;

        // Padding uses synthetic PC (0xFFFFFFF0) that's guaranteed not in ROM
        let padding_pc = if padding_count > 0 {
            self.rows[self.num_real_steps].pc
        } else {
            0
        };
        let padding_nop = 0x00000013u32;

        // Program table construction: we need exactly n entries, one per row.
        // Strategy: Place ROM entries first, then padding entry (at index m),
        // then fillers for remaining rows.
        self.prog_table = vec![[0u32, 0x00000013, 0]; n]; // Initialize all as fillers

        // 1. Place ROM entries with multiplicities (indices 0 to m-1)
        for (i, &(addr, instr)) in rom.iter().enumerate() {
            if i < n {
                let mult = *mult_map.get(&addr).unwrap_or(&0);
                self.prog_table[i] = [addr, instr, mult];
            }
        }

        // 2. Place padding entry right after ROM entries (at index m) to avoid collision
        if padding_count > 0 && m < n {
            self.prog_table[m] = [padding_pc, padding_nop, padding_count as u32];
        }

        // (Remaining entries are already fillers from initialization)

        // ── Ordering diff limbs (sorted table enforcement) ─────────
        // For each consecutive pair in sorted tables, compute the ordering
        // difference and decompose into 16-bit limbs for range checking.
        // Memory: diff = same*(next_clk - curr_clk) + (1-same)*(next_addr - curr_addr)
        // Registers: same pattern per slot transition.
        self.ordering_mem_limbs = vec![[0u32; 2]; n];
        for i in 0..n - 1 {
            let same = self.sorted_mem_aux[i + 1][0]; // same_addr flag of NEXT row
            let diff_u32 = if same == 1 {
                // Same address: clock ordering diff
                self.sorted_mem[i + 1][2].wrapping_sub(self.sorted_mem[i][2])
            } else {
                // Different address: address ordering diff
                self.sorted_mem[i + 1][0].wrapping_sub(self.sorted_mem[i][0])
            };
            self.ordering_mem_limbs[i] = [diff_u32 & 0xFFFF, diff_u32 >> 16];
        }

        self.ordering_reg_limbs = vec![[[0u32; 2]; 3]; n];
        for i in 0..n {
            // Slot A: B[i] vs A[i]
            {
                let same = self.sorted_reg_aux[i][0][0];
                let diff_u32 = if same == 1 {
                    self.sorted_reg[i][1][2].wrapping_sub(self.sorted_reg[i][0][2])
                } else {
                    self.sorted_reg[i][1][0].wrapping_sub(self.sorted_reg[i][0][0])
                };
                self.ordering_reg_limbs[i][0] = [diff_u32 & 0xFFFF, diff_u32 >> 16];
            }
            // Slot B: C[i] vs B[i]
            {
                let same = self.sorted_reg_aux[i][1][0];
                let diff_u32 = if same == 1 {
                    self.sorted_reg[i][2][2].wrapping_sub(self.sorted_reg[i][1][2])
                } else {
                    self.sorted_reg[i][2][0].wrapping_sub(self.sorted_reg[i][1][0])
                };
                self.ordering_reg_limbs[i][1] = [diff_u32 & 0xFFFF, diff_u32 >> 16];
            }
            // Slot C: A[i+1] vs C[i]
            if i + 1 < n {
                let same = self.sorted_reg_aux[i][2][0];
                let diff_u32 = if same == 1 {
                    self.sorted_reg[i + 1][0][2].wrapping_sub(self.sorted_reg[i][2][2])
                } else {
                    self.sorted_reg[i + 1][0][0].wrapping_sub(self.sorted_reg[i][2][0])
                };
                self.ordering_reg_limbs[i][2] = [diff_u32 & 0xFFFF, diff_u32 >> 16];
            }
        }

        // ── Output table ─────────────────────────────────────────────
        // Build output entries from public outputs written to memory.
        let outputs = crate::cpu::read_outputs_from_trace(&self.rows, self.num_real_steps);
        let num_outputs = outputs.len();
        self.output_table = Vec::with_capacity(n);
        // Entry 0: count word at OUTPUT_TAPE_ADDR
        self.output_table.push([crate::cpu::OUTPUT_TAPE_ADDR, num_outputs as u32, 1]);
        // Entries 1..num_outputs: output values
        for (j, &val) in outputs.iter().enumerate() {
            let addr = crate::cpu::OUTPUT_TAPE_ADDR + 4 + 4 * j as u32;
            self.output_table.push([addr, val, 1]);
        }
        // Pad to trace_len with filler
        while self.output_table.len() < n {
            self.output_table.push([0, 0, 0]);
        }

        // ── Range check limbs + multiplicities ───────────────────────
        // Split 8 values into 16-bit limbs + 8 ordering diff limbs; build multiplicity table.
        let mut mult_table = vec![0u64; 1 << 16];
        self.limbs = Vec::with_capacity(n);
        for (i, row) in self.rows.iter().enumerate() {
            let vals = [
                row.rs1_val, row.rs2_val, row.rd_val, row.imm,
                row.mem_addr, row.mem_val, row.next_pc, row.pc,
            ];
            let mut row_limbs = [0u32; 24]; // 16 value limbs + 8 ordering limbs
            for (j, &v) in vals.iter().enumerate() {
                let lo = v & 0xFFFF;
                let hi = v >> 16;
                row_limbs[j * 2] = lo;
                row_limbs[j * 2 + 1] = hi;
                mult_table[lo as usize] += 1;
                mult_table[hi as usize] += 1;
            }
            // Ordering limbs (indices 16-23)
            let om = &self.ordering_mem_limbs[i];
            row_limbs[16] = om[0];
            row_limbs[17] = om[1];
            mult_table[om[0] as usize] += 1;
            mult_table[om[1] as usize] += 1;
            let or = &self.ordering_reg_limbs[i];
            for s in 0..3 {
                row_limbs[18 + s * 2] = or[s][0];
                row_limbs[18 + s * 2 + 1] = or[s][1];
                mult_table[or[s][0] as usize] += 1;
                mult_table[or[s][1] as usize] += 1;
            }
            self.limbs.push(row_limbs);
        }

        // Range table value at row i = i % 2^16. Multiplicities indexed by value.
        self.range_mult = Vec::with_capacity(n);
        for i in 0..n {
            let table_val = (i % (1 << 16)) as usize;
            self.range_mult.push(mult_table[table_val] as u32);
        }
    }

    /// Flatten into column-major BabyBear field elements.
    /// Returns `NUM_TRACE_COLS` columns. Call prepare_sorted_tables() first.
    pub fn to_columns(&self) -> Vec<Vec<BabyBear>> {
        let n = self.rows.len();
        let mut columns = vec![vec![BabyBear::zero(); n]; NUM_TRACE_COLS];

        for (i, row) in self.rows.iter().enumerate() {
            columns[col::CLK][i] = BabyBear::from_u32(row.clk);
            columns[col::PC][i] = BabyBear::from_u32(row.pc);
            columns[col::INSTRUCTION][i] = BabyBear::from_u32(row.instruction);
            columns[col::RS1_IDX][i] = BabyBear::from_u32(row.rs1_idx);
            columns[col::RS2_IDX][i] = BabyBear::from_u32(row.rs2_idx);
            columns[col::RD_IDX][i] = BabyBear::from_u32(row.rd_idx);
            columns[col::RS1_VAL][i] = BabyBear::from_u32(row.rs1_val);
            columns[col::RS2_VAL][i] = BabyBear::from_u32(row.rs2_val);
            columns[col::RD_VAL][i] = BabyBear::from_u32(row.rd_val);
            columns[col::IMM][i] = BabyBear::from_u32(row.imm);
            columns[col::NEXT_PC][i] = BabyBear::from_u32(row.next_pc);
            columns[col::MEM_ADDR][i] = BabyBear::from_u32(row.mem_addr);
            columns[col::MEM_VAL][i] = BabyBear::from_u32(row.mem_val);
            columns[col::IS_LOAD][i] = BabyBear::from_u32(row.is_load as u32);
            columns[col::IS_STORE][i] = BabyBear::from_u32(row.is_store as u32);
            columns[col::BRANCH_TAKEN][i] = BabyBear::from_u32(row.branch_taken as u32);
            columns[col::ALU_CARRY][i] = BabyBear::from_u32(row.alu_carry);
            columns[col::PC_CARRY][i] = BabyBear::from_u32(row.pc_carry);

            for b in 0..32 {
                columns[col::BITS_A_START + b][i] = BabyBear::from_u32(row.bits_a[b]);
                columns[col::BITS_B_START + b][i] = BabyBear::from_u32(row.bits_b[b]);
            }
            for s in 0..5 {
                columns[col::SHIFT_STAGE_START + s][i] = BabyBear::from_u32(row.shift_stages[s]);
            }

            // Soundness auxiliary columns
            columns[col::MEM_ADDR_CARRY][i] = BabyBear::from_u32(row.mem_addr_carry);
            columns[col::JALR_BIT0][i] = BabyBear::from_u32(row.jalr_bit0);
            columns[col::BRANCH_DIFF_INV][i] = BabyBear::from_u32(row.branch_diff_inv);
            for s in 0..5 {
                columns[col::SHIFT_CARRY_START + s][i] = BabyBear::from_u32(row.shift_carry[s]);
            }

            // Sorted memory + auxiliaries
            if !self.sorted_mem.is_empty() {
                let m = &self.sorted_mem[i];
                columns[col::SORTED_MEM_ADDR][i] = BabyBear::from_u32(m[0]);
                columns[col::SORTED_MEM_VAL][i] = BabyBear::from_u32(m[1]);
                columns[col::SORTED_MEM_CLK][i] = BabyBear::from_u32(m[2]);
                columns[col::SORTED_MEM_IS_WRITE][i] = BabyBear::from_u32(m[3]);
                let ma = &self.sorted_mem_aux[i];
                columns[col::SORTED_MEM_SAME_ADDR][i] = BabyBear::from_u32(ma[0]);
                columns[col::SORTED_MEM_DIFF_INV][i] = BabyBear::from_u32(ma[1]);
            }

            // Sorted registers (3 slots) + auxiliaries
            if !self.sorted_reg.is_empty() {
                let r = &self.sorted_reg[i];
                let ra = &self.sorted_reg_aux[i];
                for (slot, base, aux_same, aux_inv) in [
                    (0, col::SORTED_REG_A_IDX, col::SORTED_REG_A_SAME_IDX, col::SORTED_REG_A_DIFF_INV),
                    (1, col::SORTED_REG_B_IDX, col::SORTED_REG_B_SAME_IDX, col::SORTED_REG_B_DIFF_INV),
                    (2, col::SORTED_REG_C_IDX, col::SORTED_REG_C_SAME_IDX, col::SORTED_REG_C_DIFF_INV),
                ] {
                    columns[base][i] = BabyBear::from_u32(r[slot][0]);
                    columns[base + 1][i] = BabyBear::from_u32(r[slot][1]);
                    columns[base + 2][i] = BabyBear::from_u32(r[slot][2]);
                    columns[base + 3][i] = BabyBear::from_u32(r[slot][3]);
                    columns[aux_same][i] = BabyBear::from_u32(ra[slot][0]);
                    columns[aux_inv][i] = BabyBear::from_u32(ra[slot][1]);
                }
            }

            // Program table (ROM + multiplicities)
            if !self.prog_table.is_empty() {
                let p = &self.prog_table[i];
                columns[col::PROG_ADDR][i] = BabyBear::from_u32(p[0]);
                columns[col::PROG_INSTR][i] = BabyBear::from_u32(p[1]);
                columns[col::PROG_MULT][i] = BabyBear::from_u32(p[2]);
            }

            // Instruction bit decomposition
            for b in 0..32 {
                columns[col::INSTR_BIT_START + b][i] = BabyBear::from_u32(row.instr_bits[b]);
            }

            // Register index inverses
            columns[col::RS1_IDX_INV][i] = BabyBear::from_u32(row.rs1_idx_inv);
            columns[col::RS2_IDX_INV][i] = BabyBear::from_u32(row.rs2_idx_inv);

            // Range check limbs (16 value limbs)
            if !self.limbs.is_empty() {
                let l = &self.limbs[i];
                for k in 0..16 {
                    columns[col::LIMB_START + k][i] = BabyBear::from_u32(l[k]);
                }
                columns[col::RANGE_TABLE_VAL][i] = BabyBear::from_u32((i % (1 << 16)) as u32);
                columns[col::RANGE_MULT][i] = BabyBear::from_u32(self.range_mult[i]);

                // Ordering diff limbs (from limbs[16..24])
                columns[col::ORDERING_MEM_LO][i] = BabyBear::from_u32(l[16]);
                columns[col::ORDERING_MEM_HI][i] = BabyBear::from_u32(l[17]);
                columns[col::ORDERING_REG_A_LO][i] = BabyBear::from_u32(l[18]);
                columns[col::ORDERING_REG_A_HI][i] = BabyBear::from_u32(l[19]);
                columns[col::ORDERING_REG_B_LO][i] = BabyBear::from_u32(l[20]);
                columns[col::ORDERING_REG_B_HI][i] = BabyBear::from_u32(l[21]);
                columns[col::ORDERING_REG_C_LO][i] = BabyBear::from_u32(l[22]);
                columns[col::ORDERING_REG_C_HI][i] = BabyBear::from_u32(l[23]);
            }

            // IS_HALTED flag
            columns[col::IS_HALTED][i] = BabyBear::from_u32(row.is_halted as u32);

            // Output table
            if !self.output_table.is_empty() {
                let o = &self.output_table[i];
                columns[col::OUTPUT_ADDR][i] = BabyBear::from_u32(o[0]);
                columns[col::OUTPUT_VAL][i] = BabyBear::from_u32(o[1]);
                columns[col::OUTPUT_MULT][i] = BabyBear::from_u32(o[2]);
            }

            // One-hot opcode selectors
            let class_idx = row.opcode_class as usize;
            columns[col::OPCODE_SEL_START + class_idx][i] = BabyBear::one();
        }

        columns
    }
}

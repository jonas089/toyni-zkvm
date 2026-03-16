/// Deterministic RV32I CPU with trace generation.

use crate::decode::{self, Instruction};
use crate::memory::Memory;
use crate::trace::{ExecutionTrace, TraceRow};
use toyni::babybear::BabyBear;

/// Memory layout constants.
pub const INPUT_TAPE_ADDR: u32 = 0x0020_0000; // 2 MiB
pub const OUTPUT_TAPE_ADDR: u32 = 0x0030_0000; // 3 MiB
pub const STACK_TOP: u32 = 0x00F0_0000; // 15 MiB (grows downward)

/// Halt reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HaltReason {
    Ecall,
    Ebreak,
    InvalidInstruction(u32),
    CycleLimitReached,
}

/// CPU state: 32 registers + PC.
pub struct Cpu {
    pub regs: [u32; 32],
    pub pc: u32,
    pub cycle: u32,
    pub halted: bool,
    pub halt_reason: Option<HaltReason>,
}

impl Cpu {
    pub fn new(entry_pc: u32) -> Self {
        let mut regs = [0u32; 32];
        regs[2] = STACK_TOP; // sp
        Self {
            regs,
            pc: entry_pc,
            cycle: 0,
            halted: false,
            halt_reason: None,
        }
    }

    /// Read register (x0 always returns 0).
    #[inline]
    fn reg(&self, idx: u32) -> u32 {
        if idx == 0 { 0 } else { self.regs[idx as usize] }
    }

    /// Write register (writes to x0 are discarded).
    #[inline]
    fn set_reg(&mut self, idx: u32, val: u32) {
        if idx != 0 {
            self.regs[idx as usize] = val;
        }
    }

    /// Execute a program until halt or cycle limit. Returns the execution trace.
    pub fn run(&mut self, mem: &mut Memory, cycle_limit: u32) -> ExecutionTrace {
        let mut trace = ExecutionTrace::new();

        while !self.halted && self.cycle < cycle_limit {
            let row = self.step(mem);
            trace.push(row);

            if self.halted {
                break;
            }
        }

        if !self.halted && self.cycle >= cycle_limit {
            self.halted = true;
            self.halt_reason = Some(HaltReason::CycleLimitReached);
        }

        trace
    }

    /// Execute one instruction. Returns a trace row capturing the full step.
    pub fn step(&mut self, mem: &mut Memory) -> TraceRow {
        let pc = self.pc;
        let clk = self.cycle;
        let word = mem.peek_word(pc);
        let instr = decode::decode(word);

        // Capture pre-state for trace
        let (rs1_idx, rs2_idx, rd_idx) = instr_regs(&instr);
        let rs1_val = self.reg(rs1_idx);
        let rs2_val = self.reg(rs2_idx);

        let mut next_pc = pc.wrapping_add(4);
        let mut rd_val: u32 = 0;
        let mut mem_addr: u32 = 0;
        let mut mem_val: u32 = 0;
        let mut is_load = false;
        let mut is_store = false;
        let mut branch_taken = false;
        let mut alu_carry: u32 = 0;
        let mut pc_carry: u32 = 0;
        let mut bits_a: [u32; 32] = [0; 32];
        let mut bits_b: [u32; 32] = [0; 32];
        let mut shift_stages: [u32; 5] = [0; 5];
        let mut mem_addr_carry: u32 = 0;
        let mut jalr_bit0: u32 = 0;
        let mut branch_diff_inv: u32 = 0;
        let mut shift_carry: [u32; 5] = [0; 5];

        match instr {
            // --- U-type ---
            Instruction::Lui { rd, imm } => {
                rd_val = imm;
                self.set_reg(rd, rd_val);
            }
            Instruction::Auipc { rd, imm } => {
                rd_val = pc.wrapping_add(imm);
                alu_carry = if (pc as u64 + imm as u64) >= (1u64 << 32) { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }

            // --- J-type ---
            Instruction::Jal { rd, imm } => {
                rd_val = pc.wrapping_add(4);
                alu_carry = if (pc as u64 + 4u64) >= (1u64 << 32) { 1 } else { 0 };
                self.set_reg(rd, rd_val);
                next_pc = pc.wrapping_add(imm as u32);
                pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
            }

            // --- I-type JALR ---
            Instruction::Jalr { rd, rs1, imm } => {
                rd_val = pc.wrapping_add(4);
                alu_carry = if (pc as u64 + 4u64) >= (1u64 << 32) { 1 } else { 0 };
                let base = self.reg(rs1);
                let imm_u32 = imm as u32;
                let raw = base.wrapping_add(imm_u32);
                jalr_bit0 = raw & 1;
                next_pc = raw & !1;
                pc_carry = if (base as u64 + imm_u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }

            // --- B-type ---
            Instruction::Beq { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                let diff = a.wrapping_sub(b);
                if diff != 0 {
                    branch_diff_inv = BabyBear::from_u32(diff).inverse().value as u32;
                }
                if a == b {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }
            Instruction::Bne { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                let diff = a.wrapping_sub(b);
                if diff != 0 {
                    branch_diff_inv = BabyBear::from_u32(diff).inverse().value as u32;
                }
                if a != b {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }
            Instruction::Blt { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                // Decompose (a - b + 2^31) for signed comparison
                let sdiff = (a as u64).wrapping_sub(b as u64).wrapping_add(1u64 << 31) as u32;
                bits_a = decompose_bits(sdiff);
                if (a as i32) < (b as i32) {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }
            Instruction::Bge { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                let sdiff = (a as u64).wrapping_sub(b as u64).wrapping_add(1u64 << 31) as u32;
                bits_a = decompose_bits(sdiff);
                if (a as i32) >= (b as i32) {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }
            Instruction::Bltu { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                alu_carry = if a < b { 1 } else { 0 };
                if a < b {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }
            Instruction::Bgeu { rs1, rs2, imm } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                alu_carry = if a < b { 1 } else { 0 };
                if a >= b {
                    next_pc = pc.wrapping_add(imm as u32);
                    branch_taken = true;
                    pc_carry = if (pc as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                }
            }

            // --- Loads ---
            Instruction::Lb { rd, rs1, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                let byte = mem.read_byte(mem_addr, clk);
                rd_val = ((byte as i8) as i32) as u32;
                mem_val = byte as u32;
                is_load = true;
                self.set_reg(rd, rd_val);
            }
            Instruction::Lh { rd, rs1, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                let half = mem.read_half(mem_addr, clk);
                rd_val = ((half as i16) as i32) as u32;
                mem_val = half as u32;
                is_load = true;
                self.set_reg(rd, rd_val);
            }
            Instruction::Lw { rd, rs1, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                rd_val = mem.read_word(mem_addr, clk);
                mem_val = rd_val;
                is_load = true;
                self.set_reg(rd, rd_val);
            }
            Instruction::Lbu { rd, rs1, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                let byte = mem.read_byte(mem_addr, clk);
                rd_val = byte as u32;
                mem_val = byte as u32;
                is_load = true;
                self.set_reg(rd, rd_val);
            }
            Instruction::Lhu { rd, rs1, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                let half = mem.read_half(mem_addr, clk);
                rd_val = half as u32;
                mem_val = half as u32;
                is_load = true;
                self.set_reg(rd, rd_val);
            }

            // --- Stores ---
            Instruction::Sb { rs1, rs2, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                mem_val = self.reg(rs2) & 0xff;
                mem.write_byte(mem_addr, mem_val as u8, clk);
                is_store = true;
            }
            Instruction::Sh { rs1, rs2, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                mem_val = self.reg(rs2) & 0xffff;
                mem.write_half(mem_addr, mem_val as u16, clk);
                is_store = true;
            }
            Instruction::Sw { rs1, rs2, imm } => {
                let base = self.reg(rs1);
                mem_addr = base.wrapping_add(imm as u32);
                mem_addr_carry = if (base as u64 + imm as u32 as u64) >= (1u64 << 32) { 1 } else { 0 };
                mem_val = self.reg(rs2);
                mem.write_word(mem_addr, mem_val, clk);
                is_store = true;
            }

            // --- ALU immediate ---
            Instruction::Addi { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = a.wrapping_add(b);
                alu_carry = if (a as u64 + b as u64) >= (1u64 << 32) { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }
            Instruction::Slti { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = if (a as i32) < imm { 1 } else { 0 };
                // Decompose (a - b + 2^31) to extract sign
                let diff = (a as u64).wrapping_sub(b as u64).wrapping_add(1u64 << 31) as u32;
                bits_a = decompose_bits(diff);
                self.set_reg(rd, rd_val);
            }
            Instruction::Sltiu { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = if a < b { 1 } else { 0 };
                // For unsigned: carry from a - b tells us a < b
                alu_carry = if a < b { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }
            Instruction::Xori { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = a ^ b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }
            Instruction::Ori { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = a | b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }
            Instruction::Andi { rd, rs1, imm } => {
                let a = self.reg(rs1);
                let b = imm as u32;
                rd_val = a & b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }
            Instruction::Slli { rd, rs1, shamt } => {
                let a = self.reg(rs1);
                rd_val = a << shamt;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_left_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }
            Instruction::Srli { rd, rs1, shamt } => {
                let a = self.reg(rs1);
                rd_val = a >> shamt;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_right_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }
            Instruction::Srai { rd, rs1, shamt } => {
                let a = self.reg(rs1);
                rd_val = ((a as i32) >> shamt) as u32;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_right_arith_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }

            // --- ALU register ---
            Instruction::Add { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = a.wrapping_add(b);
                alu_carry = if (a as u64 + b as u64) >= (1u64 << 32) { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = a.wrapping_sub(b);
                alu_carry = if a < b { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }
            Instruction::Sll { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let shamt = self.reg(rs2) & 0x1f;
                rd_val = a << shamt;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_left_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }
            Instruction::Slt { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = if (a as i32) < (b as i32) { 1 } else { 0 };
                let diff = (a as u64).wrapping_sub(b as u64).wrapping_add(1u64 << 31) as u32;
                bits_a = decompose_bits(diff);
                self.set_reg(rd, rd_val);
            }
            Instruction::Sltu { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = if a < b { 1 } else { 0 };
                alu_carry = if a < b { 1 } else { 0 };
                self.set_reg(rd, rd_val);
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = a ^ b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }
            Instruction::Srl { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let shamt = self.reg(rs2) & 0x1f;
                rd_val = a >> shamt;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_right_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }
            Instruction::Sra { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let shamt = self.reg(rs2) & 0x1f;
                rd_val = ((a as i32) >> shamt) as u32;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(shamt);
                let (stages, carries) = barrel_shift_right_arith_with_carry(a, shamt);
                shift_stages = stages;
                shift_carry = carries;
                self.set_reg(rd, rd_val);
            }
            Instruction::Or { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = a | b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }
            Instruction::And { rd, rs1, rs2 } => {
                let a = self.reg(rs1);
                let b = self.reg(rs2);
                rd_val = a & b;
                bits_a = decompose_bits(a);
                bits_b = decompose_bits(b);
                self.set_reg(rd, rd_val);
            }

            // --- System ---
            Instruction::Ecall => {
                self.halted = true;
                self.halt_reason = Some(HaltReason::Ecall);
            }
            Instruction::Ebreak => {
                self.halted = true;
                self.halt_reason = Some(HaltReason::Ebreak);
            }

            Instruction::Invalid(w) => {
                self.halted = true;
                self.halt_reason = Some(HaltReason::InvalidInstruction(w));
            }
        }

        // Instruction bit decomposition
        let instr_bits = decompose_bits(word);

        // Register index inverses (for x0 constraints)
        let rs1_idx_inv = if rs1_idx != 0 {
            BabyBear::from_u32(rs1_idx).inverse().value as u32
        } else {
            0
        };
        let rs2_idx_inv = if rs2_idx != 0 {
            BabyBear::from_u32(rs2_idx).inverse().value as u32
        } else {
            0
        };

        self.pc = next_pc;
        self.cycle += 1;

        TraceRow {
            clk,
            pc,
            instruction: word,
            rs1_idx,
            rs2_idx,
            rd_idx,
            rs1_val,
            rs2_val,
            rd_val,
            imm: instr_imm(&instr),
            next_pc,
            mem_addr,
            mem_val,
            is_load,
            is_store,
            branch_taken,
            alu_carry,
            pc_carry,
            bits_a,
            bits_b,
            shift_stages,
            mem_addr_carry,
            jalr_bit0,
            branch_diff_inv,
            shift_carry,
            instr_bits,
            rs1_idx_inv,
            rs2_idx_inv,
            is_halted: self.halted,
            opcode_class: opcode_class(&instr),
        }
    }
}

/// Read outputs from the execution trace by scanning memory writes to the output tape.
/// Returns the output values (not including the count word).
pub fn read_outputs_from_trace(rows: &[TraceRow], num_real_steps: usize) -> Vec<u32> {
    // Find the last store to OUTPUT_TAPE_ADDR (the count word)
    let mut count: Option<u32> = None;
    let mut output_vals: std::collections::BTreeMap<u32, u32> = std::collections::BTreeMap::new();

    for row in rows[..num_real_steps].iter() {
        if row.is_store && row.mem_addr == OUTPUT_TAPE_ADDR {
            count = Some(row.mem_val);
        }
        if row.is_store && row.mem_addr > OUTPUT_TAPE_ADDR && row.mem_addr < OUTPUT_TAPE_ADDR + 0x10_0000 {
            output_vals.insert(row.mem_addr, row.mem_val);
        }
    }

    let n = count.unwrap_or(0) as usize;
    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        let addr = OUTPUT_TAPE_ADDR + 4 + 4 * i as u32;
        result.push(*output_vals.get(&addr).unwrap_or(&0));
    }
    result
}

/// Opcode class for selector polynomials.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum OpcodeClass {
    Add = 0,
    Sub = 1,
    And = 2,
    Or = 3,
    Xor = 4,
    Sll = 5,
    Srl = 6,
    Sra = 7,
    Slt = 8,
    Sltu = 9,
    Addi = 10,
    Andi = 11,
    Ori = 12,
    Xori = 13,
    Slti = 14,
    Sltiu = 15,
    Slli = 16,
    Srli = 17,
    Srai = 18,
    Lw = 19,
    Lh = 20,
    Lb = 21,
    Lhu = 22,
    Lbu = 23,
    Sw = 24,
    Sh = 25,
    Sb = 26,
    Beq = 27,
    Bne = 28,
    Blt = 29,
    Bge = 30,
    Bltu = 31,
    Bgeu = 32,
    Jal = 33,
    Jalr = 34,
    Lui = 35,
    Auipc = 36,
    Ecall = 37,
    Ebreak = 38,
    Invalid = 39,
}

pub const NUM_OPCODE_CLASSES: usize = 40;

fn opcode_class(instr: &Instruction) -> OpcodeClass {
    match instr {
        Instruction::Add { .. } => OpcodeClass::Add,
        Instruction::Sub { .. } => OpcodeClass::Sub,
        Instruction::And { .. } => OpcodeClass::And,
        Instruction::Or { .. } => OpcodeClass::Or,
        Instruction::Xor { .. } => OpcodeClass::Xor,
        Instruction::Sll { .. } => OpcodeClass::Sll,
        Instruction::Srl { .. } => OpcodeClass::Srl,
        Instruction::Sra { .. } => OpcodeClass::Sra,
        Instruction::Slt { .. } => OpcodeClass::Slt,
        Instruction::Sltu { .. } => OpcodeClass::Sltu,
        Instruction::Addi { .. } => OpcodeClass::Addi,
        Instruction::Andi { .. } => OpcodeClass::Andi,
        Instruction::Ori { .. } => OpcodeClass::Ori,
        Instruction::Xori { .. } => OpcodeClass::Xori,
        Instruction::Slti { .. } => OpcodeClass::Slti,
        Instruction::Sltiu { .. } => OpcodeClass::Sltiu,
        Instruction::Slli { .. } => OpcodeClass::Slli,
        Instruction::Srli { .. } => OpcodeClass::Srli,
        Instruction::Srai { .. } => OpcodeClass::Srai,
        Instruction::Lw { .. } => OpcodeClass::Lw,
        Instruction::Lh { .. } => OpcodeClass::Lh,
        Instruction::Lb { .. } => OpcodeClass::Lb,
        Instruction::Lhu { .. } => OpcodeClass::Lhu,
        Instruction::Lbu { .. } => OpcodeClass::Lbu,
        Instruction::Sw { .. } => OpcodeClass::Sw,
        Instruction::Sh { .. } => OpcodeClass::Sh,
        Instruction::Sb { .. } => OpcodeClass::Sb,
        Instruction::Beq { .. } => OpcodeClass::Beq,
        Instruction::Bne { .. } => OpcodeClass::Bne,
        Instruction::Blt { .. } => OpcodeClass::Blt,
        Instruction::Bge { .. } => OpcodeClass::Bge,
        Instruction::Bltu { .. } => OpcodeClass::Bltu,
        Instruction::Bgeu { .. } => OpcodeClass::Bgeu,
        Instruction::Jal { .. } => OpcodeClass::Jal,
        Instruction::Jalr { .. } => OpcodeClass::Jalr,
        Instruction::Lui { .. } => OpcodeClass::Lui,
        Instruction::Auipc { .. } => OpcodeClass::Auipc,
        Instruction::Ecall => OpcodeClass::Ecall,
        Instruction::Ebreak => OpcodeClass::Ebreak,
        Instruction::Invalid(_) => OpcodeClass::Invalid,
    }
}

/// Decompose a u32 into 32 bits (LSB first).
fn decompose_bits(val: u32) -> [u32; 32] {
    let mut bits = [0u32; 32];
    for i in 0..32 {
        bits[i] = (val >> i) & 1;
    }
    bits
}

/// Compute barrel shifter stages for left shift, returning both stages and carries.
/// stage[k] = result after applying shift stage k (truncated to u32).
/// carry[k] = overflow bits from stage k transition.
fn barrel_shift_left_with_carry(val: u32, shamt: u32) -> ([u32; 5], [u32; 5]) {
    let mut stages = [0u32; 5];
    let mut carries = [0u32; 5];
    let mut cur = val as u64;
    for k in 0..5 {
        if (shamt >> k) & 1 == 1 {
            cur <<= 1 << k;
        }
        carries[k] = (cur >> 32) as u32;
        cur &= 0xFFFF_FFFF; // truncate to u32
        stages[k] = cur as u32;
    }
    (stages, carries)
}

/// Compute barrel shifter stages for logical right shift with carries.
/// For right shifts, carry[k] captures the bits shifted out from the bottom.
fn barrel_shift_right_with_carry(val: u32, shamt: u32) -> ([u32; 5], [u32; 5]) {
    let mut stages = [0u32; 5];
    let mut carries = [0u32; 5];
    let mut cur = val;
    for k in 0..5 {
        if (shamt >> k) & 1 == 1 {
            let shift_amt = 1 << k;
            carries[k] = cur & ((1u32 << shift_amt) - 1);
            cur >>= shift_amt;
        }
        stages[k] = cur;
    }
    (stages, carries)
}

/// Compute barrel shifter stages for arithmetic right shift with carries.
fn barrel_shift_right_arith_with_carry(val: u32, shamt: u32) -> ([u32; 5], [u32; 5]) {
    let mut stages = [0u32; 5];
    let mut carries = [0u32; 5];
    let mut cur = val as i32;
    for k in 0..5 {
        if (shamt >> k) & 1 == 1 {
            let shift_amt = 1 << k;
            carries[k] = (cur as u32) & ((1u32 << shift_amt) - 1);
            cur >>= shift_amt;
        }
        stages[k] = cur as u32;
    }
    (stages, carries)
}

/// Extract register indices from an instruction.
fn instr_regs(instr: &Instruction) -> (u32, u32, u32) {
    match *instr {
        // R-type
        Instruction::Add { rd, rs1, rs2 }
        | Instruction::Sub { rd, rs1, rs2 }
        | Instruction::Sll { rd, rs1, rs2 }
        | Instruction::Slt { rd, rs1, rs2 }
        | Instruction::Sltu { rd, rs1, rs2 }
        | Instruction::Xor { rd, rs1, rs2 }
        | Instruction::Srl { rd, rs1, rs2 }
        | Instruction::Sra { rd, rs1, rs2 }
        | Instruction::Or { rd, rs1, rs2 }
        | Instruction::And { rd, rs1, rs2 } => (rs1, rs2, rd),

        // I-type ALU
        Instruction::Addi { rd, rs1, .. }
        | Instruction::Slti { rd, rs1, .. }
        | Instruction::Sltiu { rd, rs1, .. }
        | Instruction::Xori { rd, rs1, .. }
        | Instruction::Ori { rd, rs1, .. }
        | Instruction::Andi { rd, rs1, .. }
        | Instruction::Slli { rd, rs1, .. }
        | Instruction::Srli { rd, rs1, .. }
        | Instruction::Srai { rd, rs1, .. } => (rs1, 0, rd),

        // Loads
        Instruction::Lb { rd, rs1, .. }
        | Instruction::Lh { rd, rs1, .. }
        | Instruction::Lw { rd, rs1, .. }
        | Instruction::Lbu { rd, rs1, .. }
        | Instruction::Lhu { rd, rs1, .. } => (rs1, 0, rd),

        // Stores
        Instruction::Sb { rs1, rs2, .. }
        | Instruction::Sh { rs1, rs2, .. }
        | Instruction::Sw { rs1, rs2, .. } => (rs1, rs2, 0),

        // Branches
        Instruction::Beq { rs1, rs2, .. }
        | Instruction::Bne { rs1, rs2, .. }
        | Instruction::Blt { rs1, rs2, .. }
        | Instruction::Bge { rs1, rs2, .. }
        | Instruction::Bltu { rs1, rs2, .. }
        | Instruction::Bgeu { rs1, rs2, .. } => (rs1, rs2, 0),

        // JALR
        Instruction::Jalr { rd, rs1, .. } => (rs1, 0, rd),

        // JAL
        Instruction::Jal { rd, .. } => (0, 0, rd),

        // U-type
        Instruction::Lui { rd, .. } | Instruction::Auipc { rd, .. } => (0, 0, rd),

        // System
        Instruction::Ecall | Instruction::Ebreak | Instruction::Invalid(_) => (0, 0, 0),
    }
}

/// Extract the immediate value as a u32 for the trace.
fn instr_imm(instr: &Instruction) -> u32 {
    match *instr {
        Instruction::Lui { imm, .. } | Instruction::Auipc { imm, .. } => imm,
        Instruction::Jal { imm, .. } => imm as u32,
        Instruction::Jalr { imm, .. } => imm as u32,
        Instruction::Beq { imm, .. }
        | Instruction::Bne { imm, .. }
        | Instruction::Blt { imm, .. }
        | Instruction::Bge { imm, .. }
        | Instruction::Bltu { imm, .. }
        | Instruction::Bgeu { imm, .. } => imm as u32,
        Instruction::Lb { imm, .. }
        | Instruction::Lh { imm, .. }
        | Instruction::Lw { imm, .. }
        | Instruction::Lbu { imm, .. }
        | Instruction::Lhu { imm, .. } => imm as u32,
        Instruction::Sb { imm, .. }
        | Instruction::Sh { imm, .. }
        | Instruction::Sw { imm, .. } => imm as u32,
        Instruction::Addi { imm, .. }
        | Instruction::Slti { imm, .. }
        | Instruction::Sltiu { imm, .. }
        | Instruction::Xori { imm, .. }
        | Instruction::Ori { imm, .. }
        | Instruction::Andi { imm, .. } => imm as u32,
        Instruction::Slli { shamt, .. }
        | Instruction::Srli { shamt, .. }
        | Instruction::Srai { shamt, .. } => shamt,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::Memory;

    /// Helper to assemble a small program and run it.
    fn run_program(instructions: &[u32], cycle_limit: u32) -> (Cpu, Memory, ExecutionTrace) {
        let mut mem = Memory::new(1 << 20);
        let base = 0x1000u32;
        for (i, &instr) in instructions.iter().enumerate() {
            let addr = base + (i as u32) * 4;
            let bytes = instr.to_le_bytes();
            mem.write_bytes_no_log(addr, &bytes);
        }
        let mut cpu = Cpu::new(base);
        let trace = cpu.run(&mut mem, cycle_limit);
        (cpu, mem, trace)
    }

    #[test]
    fn test_addi_sequence() {
        let program = [
            0x00500093, // addi x1, x0, 5
            0x00308113, // addi x2, x1, 3
            0x00000073, // ecall (halt)
        ];
        let (cpu, _, trace) = run_program(&program, 100);
        assert_eq!(cpu.regs[1], 5);
        assert_eq!(cpu.regs[2], 8);
        assert_eq!(trace.rows.len(), 3);
        assert!(cpu.halted);
    }

    #[test]
    fn test_add_sub() {
        let program = [
            0x00a00093, // addi x1, x0, 10
            0x00300113, // addi x2, x0, 3
            0x002081b3, // add  x3, x1, x2
            0x40208233, // sub  x4, x1, x2
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[3], 13);
        assert_eq!(cpu.regs[4], 7);
    }

    #[test]
    fn test_branch_beq() {
        let program = [
            0x00500093, // addi x1, x0, 5
            0x00500113, // addi x2, x0, 5
            0x00208463, // beq  x1, x2, +8  (skip next instruction)
            0x00100193, // addi x3, x0, 1    (should be skipped)
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[3], 0); // x3 not written — branch was taken
    }

    #[test]
    fn test_lui_auipc() {
        let program = [
            0x123450b7, // lui x1, 0x12345
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[1], 0x12345000);
    }

    #[test]
    fn test_load_store_word() {
        let program = [
            0x0ff00093, // addi x1, x0, 255
            0x00102023, // sw   x1, 0(x0)    -- store 255 at addr 0
            0x00002103, // lw   x2, 0(x0)    -- load from addr 0
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[2], 255);
    }

    #[test]
    fn test_jal_jalr() {
        let program = [
            0x008000ef, // jal x1, 8         -- jump to pc+8 (0x1008), link in x1
            0x00000013, // addi x0, x0, 0    -- nop (skipped)
            0x00000013, // addi x0, x0, 0    -- nop (landed here)
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[1], 0x1004); // return address
    }

    #[test]
    fn test_shift_operations() {
        let program = [
            0x00800093, // addi x1, x0, 8
            0x00209113, // slli x2, x1, 2    -- 8 << 2 = 32
            0x0020d193, // srli x3, x1, 2    -- 8 >> 2 = 2
            0x00000073, // ecall
        ];
        let (cpu, _, _) = run_program(&program, 100);
        assert_eq!(cpu.regs[2], 32);
        assert_eq!(cpu.regs[3], 2);
    }

    #[test]
    fn test_fibonacci_loop() {
        // Compute fib(10) = 55 using a loop.
        // x1 = a = 1, x2 = b = 1, x3 = counter = 8
        // loop: x4 = a + b; a = b; b = x4; counter--; if counter != 0 goto loop
        //
        // bne x3, x0, -16: B-type encoding with offset -16
        // -16 as 13-bit signed = 0x1FF0, bit[12]=1 bit[11]=1 bits[10:5]=111111 bits[4:1]=1000
        // Encoding: [1|111111|00000|00011|001|1000|1|1100011] = 0xFE0198E3
        let program = [
            0x00100093u32, // addi x1, x0, 1      -- a = 1
            0x00100113,    // addi x2, x0, 1      -- b = 1
            0x00800193,    // addi x3, x0, 8      -- counter = 8
            0x00208233,    // add  x4, x1, x2     -- x4 = a + b
            0x00010093,    // addi x1, x2, 0      -- a = b
            0x00020113,    // addi x2, x4, 0      -- b = x4
            0xfff18193,    // addi x3, x3, -1     -- counter--
            0xfe0198e3,    // bne  x3, x0, -16    -- branch to loop (instr[3])
            0x00000073,    // ecall
        ];

        let (cpu, _, _) = run_program(&program, 200);
        assert!(cpu.halted);
        // After 8 iterations: fib sequence 1,1,2,3,5,8,13,21,34,55
        // x2 (b) should be fib(10) = 55
        assert_eq!(cpu.regs[2], 55, "Expected fib(10) = 55, got {}", cpu.regs[2]);
    }
}

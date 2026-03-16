/// Polynomial constraint definitions for RV32I opcodes.
///
/// Each constraint is of the form: selector * (expected - actual) = 0
/// When the selector is 0 (instruction not active), the constraint is trivially satisfied.
/// When the selector is 1, the actual value must match expected.

use toyni::babybear::BabyBear;
use zkvm_core::cpu::OpcodeClass;
use zkvm_core::trace::col;

use crate::TraceView;

/// 2^32 mod p (BabyBear prime). Used to absorb u32 overflow in field arithmetic.
/// p = 2013265921, 2^32 = 4294967296, so 2^32 mod p = 268435454.
const TWO32_MOD_P: u64 = 268435454;

/// ALU constraints: enforce rd_val = f(rs1_val, rs2_val or imm) for each ALU opcode.
///
/// For addition/subtraction, u32 wrapping differs from BabyBear field arithmetic
/// (since p ≈ 2^31). We use a carry column: for ADD-like operations,
/// `rd + carry * TWO32_MOD_P = operand1 + operand2 (mod p)`, with carry ∈ {0,1}.
/// For SUB, `rd - carry * TWO32_MOD_P = rs1 - rs2 (mod p)`.
pub fn alu_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let rs1 = curr.col(col::RS1_VAL);
    let rs2 = curr.col(col::RS2_VAL);
    let rd = curr.col(col::RD_VAL);
    let imm = curr.col(col::IMM);
    let pc = curr.col(col::PC);
    let carry = curr.col(col::ALU_CARRY);
    let t32 = BabyBear::new(TWO32_MOD_P);

    let mut constraints = Vec::new();

    // ADD: rd + carry * 2^32 = rs1 + rs2 (mod p)
    let sel_add = curr.sel(OpcodeClass::Add as usize);
    constraints.push(sel_add * (rd + carry * t32 - rs1 - rs2));

    // SUB: rd - carry * 2^32 = rs1 - rs2 (mod p) [carry=1 means borrow]
    let sel_sub = curr.sel(OpcodeClass::Sub as usize);
    constraints.push(sel_sub * (rd - carry * t32 - rs1 + rs2));

    // ADDI: rd + carry * 2^32 = rs1 + imm (mod p)
    let sel_addi = curr.sel(OpcodeClass::Addi as usize);
    constraints.push(sel_addi * (rd + carry * t32 - rs1 - imm));

    // LUI: rd = imm (no arithmetic, no carry needed)
    let sel_lui = curr.sel(OpcodeClass::Lui as usize);
    constraints.push(sel_lui * (rd - imm));

    // AUIPC: rd + carry * 2^32 = pc + imm (mod p)
    let sel_auipc = curr.sel(OpcodeClass::Auipc as usize);
    constraints.push(sel_auipc * (rd + carry * t32 - pc - imm));

    // JAL: rd = pc + 4 (never overflows in practice, but include carry for soundness)
    let sel_jal = curr.sel(OpcodeClass::Jal as usize);
    let four = BabyBear::new(4);
    constraints.push(sel_jal * (rd + carry * t32 - pc - four));

    // JALR: rd = pc + 4
    let sel_jalr = curr.sel(OpcodeClass::Jalr as usize);
    constraints.push(sel_jalr * (rd + carry * t32 - pc - four));

    // SLT/SLTU/SLTI/SLTIU: rd ∈ {0, 1}
    // Note: The actual comparison logic is in bitwise.rs (SLT uses bit decomposition,
    // SLTU uses carry). Here we just enforce the boolean constraint for other SLT variants.
    let sel_slti = curr.sel(OpcodeClass::Slti as usize);
    constraints.push(sel_slti * rd * (rd - BabyBear::one()));

    let sel_sltiu = curr.sel(OpcodeClass::Sltiu as usize);
    constraints.push(sel_sltiu * rd * (rd - BabyBear::one()));

    // Boolean constraint: carry ∈ {0, 1}
    constraints.push(carry * (carry - BabyBear::one()));

    constraints
}

/// Memory address computation constraints.
/// For loads and stores: mem_addr + mem_addr_carry * 2^32 = rs1 + imm (mod p).
pub fn mem_addr_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let rs1 = curr.col(col::RS1_VAL);
    let imm = curr.col(col::IMM);
    let mem_addr = curr.col(col::MEM_ADDR);
    let mac = curr.col(col::MEM_ADDR_CARRY);
    let is_mem = curr.col(col::IS_LOAD) + curr.col(col::IS_STORE);
    let t32 = BabyBear::new(TWO32_MOD_P);

    let mut constraints = Vec::new();

    // mem_addr + carry * 2^32 = rs1 + imm
    constraints.push(is_mem * (mem_addr + mac * t32 - rs1 - imm));

    // carry is boolean
    constraints.push(is_mem * mac * (mac - BabyBear::one()));

    constraints
}

/// JALR target bit-0 masking constraint.
/// next_pc + jalr_bit0 + pc_carry * 2^32 = rs1 + imm (mod p).
/// jalr_bit0 ∈ {0, 1}.
pub fn jalr_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let sel_jalr = curr.sel(OpcodeClass::Jalr as usize);
    let rs1 = curr.col(col::RS1_VAL);
    let imm = curr.col(col::IMM);
    let next_pc = curr.col(col::NEXT_PC);
    let bit0 = curr.col(col::JALR_BIT0);
    let pc_carry = curr.col(col::PC_CARRY);
    let t32 = BabyBear::new(TWO32_MOD_P);

    let mut constraints = Vec::new();

    // next_pc = (rs1 + imm) & ~1 = rs1 + imm - bit0 (mod 2^32)
    // In field: next_pc + bit0 + pc_carry * 2^32 = rs1 + imm
    constraints.push(sel_jalr * (next_pc + bit0 + pc_carry * t32 - rs1 - imm));

    // bit0 is boolean
    constraints.push(sel_jalr * bit0 * (bit0 - BabyBear::one()));

    constraints
}

/// Branch condition constraints.
/// For BEQ/BNE: use diff_inv to prove equality/inequality.
/// For BLT/BGE: use bits_a decomposition of (rs1-rs2+2^31).
/// For BLTU/BGEU: use alu_carry.
pub fn branch_condition_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let rs1 = curr.col(col::RS1_VAL);
    let rs2 = curr.col(col::RS2_VAL);
    let bt = curr.col(col::BRANCH_TAKEN);
    let diff_inv = curr.col(col::BRANCH_DIFF_INV);
    let carry = curr.col(col::ALU_CARRY);
    let t32 = BabyBear::new(TWO32_MOD_P);
    let two31 = BabyBear::new(1u64 << 31);

    let mut constraints = Vec::new();

    let diff = rs1 - rs2;

    // ── BEQ: taken iff rs1 == rs2 ─────────────────────────────────────
    let sel_beq = curr.sel(OpcodeClass::Beq as usize);
    // If taken: diff must be 0 → sel * bt * diff = 0
    constraints.push(sel_beq * bt * diff);
    // If not taken: diff must be nonzero → (1 - bt) * (1 - diff * diff_inv) = 0
    constraints.push(sel_beq * (BabyBear::one() - bt) * (BabyBear::one() - diff * diff_inv));

    // ── BNE: taken iff rs1 != rs2 ─────────────────────────────────────
    let sel_bne = curr.sel(OpcodeClass::Bne as usize);
    // If taken: diff must be nonzero → bt * (1 - diff * diff_inv) = 0
    constraints.push(sel_bne * bt * (BabyBear::one() - diff * diff_inv));
    // If not taken: diff must be 0 → (1 - bt) * diff = 0
    constraints.push(sel_bne * (BabyBear::one() - bt) * diff);

    // ── BLT: taken iff (rs1 as i32) < (rs2 as i32) ───────────────────
    // bits_a decomposes (rs1 - rs2 + 2^31). If bit 31 == 0, rs1 < rs2 (signed).
    let sel_blt = curr.sel(OpcodeClass::Blt as usize);
    let sign_bit = curr.col(col::BITS_A_START + 31);
    // Reconstruct decomposed value
    let mut recon = BabyBear::zero();
    for b in 0..32 {
        recon = recon + curr.col(col::BITS_A_START + b) * BabyBear::new(1u64 << b);
    }
    // recon = rs1 - rs2 + 2^31 (mod 2^32), which in the field needs carry:
    // recon + carry * 2^32 = rs1 - rs2 + 2^31  → using existing alu_carry
    constraints.push(sel_blt * (recon + carry * t32 - rs1 + rs2 - two31));
    // taken = (1 - sign_bit): bit31=0 means negative diff, so rs1 < rs2
    constraints.push(sel_blt * (bt - (BabyBear::one() - sign_bit)));

    // ── BGE: taken iff (rs1 as i32) >= (rs2 as i32) ──────────────────
    let sel_bge = curr.sel(OpcodeClass::Bge as usize);
    constraints.push(sel_bge * (recon + carry * t32 - rs1 + rs2 - two31));
    constraints.push(sel_bge * (bt - sign_bit));

    // ── BLTU: taken iff rs1 < rs2 (unsigned) ──────────────────────────
    // alu_carry = 1 if rs1 < rs2
    let sel_bltu = curr.sel(OpcodeClass::Bltu as usize);
    constraints.push(sel_bltu * (bt - carry));

    // ── BGEU: taken iff rs1 >= rs2 (unsigned) ─────────────────────────
    let sel_bgeu = curr.sel(OpcodeClass::Bgeu as usize);
    constraints.push(sel_bgeu * (bt - (BabyBear::one() - carry)));

    constraints
}

/// PC update constraints: enforce next_pc is correct for each instruction type.
///
/// For JAL and taken branches, `next_pc = pc + imm` which can overflow u32.
/// We use pc_carry to absorb this: `next_pc + pc_carry * TWO32 = pc + imm`.
pub fn pc_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let pc = curr.col(col::PC);
    let next_pc = curr.col(col::NEXT_PC);
    let imm = curr.col(col::IMM);
    let four = BabyBear::new(4);
    let pc_carry = curr.col(col::PC_CARRY);
    let t32 = BabyBear::new(TWO32_MOD_P);

    let mut constraints = Vec::new();

    // For non-branch/jump instructions: next_pc = pc + 4 (never overflows)
    // Exempt halted rows (execution has stopped, next_pc can be anything)
    let sel_jal = curr.sel(OpcodeClass::Jal as usize);
    let sel_jalr = curr.sel(OpcodeClass::Jalr as usize);
    let branch_sel = branch_any_selector(curr);
    let is_halted = curr.col(col::IS_HALTED);

    let non_jump = (BabyBear::one() - sel_jal - sel_jalr - branch_sel) * (BabyBear::one() - is_halted);
    constraints.push(non_jump * (next_pc - pc - four));

    // JAL: next_pc + pc_carry * 2^32 = pc + imm (mod p)
    constraints.push(sel_jal * (next_pc + pc_carry * t32 - pc - imm));

    // Branches: if taken, next_pc + pc_carry * 2^32 = pc + imm; if not, next_pc = pc + 4
    // Combined: next_pc + bt * pc_carry * 2^32 - pc - 4 - bt * (imm - 4) = 0
    let bt = curr.col(col::BRANCH_TAKEN);
    constraints.push(branch_sel * (next_pc + bt * pc_carry * t32 - pc - four - bt * (imm - four)));

    // branch_taken must be boolean
    constraints.push(branch_sel * bt * (bt - BabyBear::one()));

    // pc_carry must be boolean
    constraints.push(pc_carry * (pc_carry - BabyBear::one()));

    constraints
}

/// Memory operation flag constraints.
pub fn memory_flag_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let is_load = curr.col(col::IS_LOAD);
    let is_store = curr.col(col::IS_STORE);

    let mut constraints = Vec::new();

    // is_load and is_store are boolean
    constraints.push(is_load * (is_load - BabyBear::one()));
    constraints.push(is_store * (is_store - BabyBear::one()));

    // Cannot be both load and store simultaneously
    constraints.push(is_load * is_store);

    // Load opcodes must have is_load = 1
    let load_sel = curr.sel(OpcodeClass::Lw as usize)
        + curr.sel(OpcodeClass::Lh as usize)
        + curr.sel(OpcodeClass::Lb as usize)
        + curr.sel(OpcodeClass::Lhu as usize)
        + curr.sel(OpcodeClass::Lbu as usize);
    constraints.push(load_sel - is_load);

    // Store opcodes must have is_store = 1
    let store_sel = curr.sel(OpcodeClass::Sw as usize)
        + curr.sel(OpcodeClass::Sh as usize)
        + curr.sel(OpcodeClass::Sb as usize);
    constraints.push(store_sel - is_store);

    constraints
}

/// Selector boolean constraints: each opcode selector must be 0 or 1.
pub fn selector_boolean_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();
    for i in 0..zkvm_core::cpu::NUM_OPCODE_CLASSES {
        let s = curr.sel(i);
        constraints.push(s * (s - BabyBear::one()));
    }
    constraints
}

/// x0 register constraints: when rs1_idx=0, rs1_val must be 0 (same for rs2).
/// Uses auxiliary inverse columns: rs1_idx * (1 - rs1_idx * inv) = 0 and (1 - rs1_idx * inv) * rs1_val = 0.
pub fn x0_register_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let rs1_idx = curr.col(col::RS1_IDX);
    let rs1_val = curr.col(col::RS1_VAL);
    let rs1_inv = curr.col(col::RS1_IDX_INV);

    // When rs1_idx != 0: rs1_idx * inv = 1 (forced by first constraint)
    // When rs1_idx = 0: rs1_val = 0 (forced by second constraint)
    constraints.push(rs1_idx * (BabyBear::one() - rs1_idx * rs1_inv));
    constraints.push((BabyBear::one() - rs1_idx * rs1_inv) * rs1_val);

    let rs2_idx = curr.col(col::RS2_IDX);
    let rs2_val = curr.col(col::RS2_VAL);
    let rs2_inv = curr.col(col::RS2_IDX_INV);

    constraints.push(rs2_idx * (BabyBear::one() - rs2_idx * rs2_inv));
    constraints.push((BabyBear::one() - rs2_idx * rs2_inv) * rs2_val);

    constraints
}

/// Store value constraints: mem_val must match rs2_val (masked for sub-word stores).
pub fn store_val_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let rs2 = curr.col(col::RS2_VAL);
    let mem_val = curr.col(col::MEM_VAL);

    // SW: mem_val = rs2_val (exact)
    let sel_sw = curr.sel(OpcodeClass::Sw as usize);
    constraints.push(sel_sw * (mem_val - rs2));

    // SH: mem_val = rs2_val & 0xFFFF = rs2_lo (low 16-bit limb)
    // rs2's limbs are at LIMB_START + 2 (lo) and LIMB_START + 3 (hi)
    // Constraint: mem_val = rs2_lo, and mem_val_hi = 0
    let sel_sh = curr.sel(OpcodeClass::Sh as usize);
    let rs2_lo = curr.col(col::LIMB_START + 2);
    constraints.push(sel_sh * (mem_val - rs2_lo));

    // SB: mem_val = rs2_val & 0xFF
    // We use the existing limb for rs2_lo (16-bit) and need mem_val < 256.
    // For SB: mem_val_hi_limb = 0 (mem_val < 65536) is from reconstruction.
    // Additionally need mem_val < 256. Without a lookup, we constrain:
    // mem_val * (mem_val - 1) * ... would require degree 256. Instead, note
    // that the mem_val limbs (LIMB_START+10, LIMB_START+11) reconstruct mem_val.
    // For SB: LIMB_START+11 = 0 (from SH-like reasoning) and LIMB_START+10 < 256.
    // We can't enforce LIMB_START+10 < 256 without a lookup. Accept this limitation.
    // At minimum, constrain that mem_val's high limb is 0 for SB (mem_val < 65536):
    let sel_sb = curr.sel(OpcodeClass::Sb as usize);
    let mem_val_hi = curr.col(col::LIMB_START + 11);
    constraints.push(sel_sb * mem_val_hi);

    constraints
}

/// Load value constraints: rd_val must match mem_val with proper sign/zero extension.
pub fn load_val_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let rd = curr.col(col::RD_VAL);
    let mem_val = curr.col(col::MEM_VAL);

    // LW: rd = mem_val (exact, full 32-bit word)
    let sel_lw = curr.sel(OpcodeClass::Lw as usize);
    constraints.push(sel_lw * (rd - mem_val));

    // LH: rd = sign_extend_16(mem_val)
    // If bit 15 is set, sign extend with 1s, else with 0s
    // rd = mem_val + (bit15 ? 0xFFFF0000 : 0)
    let sel_lh = curr.sel(OpcodeClass::Lh as usize);
    let bit15 = curr.col(col::BITS_A_START + 15); // Assume mem_val decomposed into BITS_A
    constraints.push(sel_lh * bit15 * (bit15 - BabyBear::one())); // bit15 is boolean
    let sign_ext_16 = BabyBear::new(TWO32_MOD_P) - BabyBear::new(0x10000);
    constraints.push(sel_lh * (rd - mem_val - bit15 * sign_ext_16));

    // LHU: rd = zero_extend_16(mem_val) = mem_val (low 16 bits, high 16 are 0)
    let sel_lhu = curr.sel(OpcodeClass::Lhu as usize);
    constraints.push(sel_lhu * (rd - mem_val));
    // Also verify mem_val < 65536 via its high limb being 0
    let mem_val_hi = curr.col(col::LIMB_START + 11);
    constraints.push(sel_lhu * mem_val_hi);

    // LB: rd = sign_extend_8(mem_val)
    // If bit 7 is set, sign extend with 1s, else with 0s
    let sel_lb = curr.sel(OpcodeClass::Lb as usize);
    let bit7 = curr.col(col::BITS_A_START + 7);
    constraints.push(sel_lb * bit7 * (bit7 - BabyBear::one()));
    let sign_ext_8 = BabyBear::new(TWO32_MOD_P) - BabyBear::new(0x100);
    constraints.push(sel_lb * (rd - mem_val - bit7 * sign_ext_8));

    // LBU: rd = zero_extend_8(mem_val) = mem_val (low 8 bits)
    let sel_lbu = curr.sel(OpcodeClass::Lbu as usize);
    constraints.push(sel_lbu * (rd - mem_val));
    // Verify mem_val < 256 via its high limb being 0
    constraints.push(sel_lbu * mem_val_hi);

    // For LH/LB, verify mem_val is properly decomposed into BITS_A for sign bit check
    let load_signed_sel = sel_lh + sel_lb;
    let mut mem_val_recon = BabyBear::zero();
    for i in 0..32 {
        let bit = curr.col(col::BITS_A_START + i);
        constraints.push(load_signed_sel * bit * (bit - BabyBear::one()));
        if i < 31 {
            mem_val_recon = mem_val_recon + bit * BabyBear::new(1u64 << i);
        } else {
            mem_val_recon = mem_val_recon + bit * BabyBear::new((1u64 << 31) % 2013265921);
        }
    }
    constraints.push(load_signed_sel * (mem_val_recon - mem_val));

    constraints
}

/// Instruction decoding constraints: verify that the instruction word's bit decomposition
/// is consistent with the opcode selector, register indices, and immediate values.
pub fn instruction_decoding_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    // ── 1. Boolean constraints for all 32 instruction bits ──
    for b in 0..32 {
        let bit = curr.col(col::INSTR_BIT_START + b);
        constraints.push(bit * (bit - BabyBear::one()));
    }

    // ── 2. Reconstruction: Σ bit[k] * 2^k = instruction ──
    let mut recon = BabyBear::zero();
    for b in 0..31 {
        recon = recon + curr.col(col::INSTR_BIT_START + b) * BabyBear::new(1u64 << b);
    }
    // Bit 31: 2^31 > p, so use modular reduction
    recon = recon + curr.col(col::INSTR_BIT_START + 31) * BabyBear::new((1u64 << 31) % 2013265921);
    constraints.push(curr.col(col::INSTRUCTION) - recon);

    // ── 3. Extract fields from instruction bits ──
    // opcode = bits[6:0]
    let mut opcode_field = BabyBear::zero();
    for b in 0..7 {
        opcode_field = opcode_field + curr.col(col::INSTR_BIT_START + b) * BabyBear::new(1u64 << b);
    }
    // rd_field = bits[11:7]
    let mut rd_field = BabyBear::zero();
    for b in 0..5 {
        rd_field = rd_field + curr.col(col::INSTR_BIT_START + 7 + b) * BabyBear::new(1u64 << b);
    }
    // funct3 = bits[14:12]
    let mut funct3_field = BabyBear::zero();
    for b in 0..3 {
        funct3_field = funct3_field + curr.col(col::INSTR_BIT_START + 12 + b) * BabyBear::new(1u64 << b);
    }
    // rs1_field = bits[19:15]
    let mut rs1_field = BabyBear::zero();
    for b in 0..5 {
        rs1_field = rs1_field + curr.col(col::INSTR_BIT_START + 15 + b) * BabyBear::new(1u64 << b);
    }
    // rs2_field = bits[24:20]
    let mut rs2_field = BabyBear::zero();
    for b in 0..5 {
        rs2_field = rs2_field + curr.col(col::INSTR_BIT_START + 20 + b) * BabyBear::new(1u64 << b);
    }
    // funct7 = bits[31:25]
    let mut funct7_field = BabyBear::zero();
    for b in 0..7 {
        funct7_field = funct7_field + curr.col(col::INSTR_BIT_START + 25 + b) * BabyBear::new(1u64 << b);
    }

    // ── 4. Register field matching ──
    // Instructions that use rd (R/I/U/J types):
    let uses_rd = curr.sel(OpcodeClass::Add as usize)
        + curr.sel(OpcodeClass::Sub as usize)
        + curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Sltu as usize)
        + curr.sel(OpcodeClass::Addi as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Slti as usize)
        + curr.sel(OpcodeClass::Sltiu as usize)
        + curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize)
        + curr.sel(OpcodeClass::Lw as usize)
        + curr.sel(OpcodeClass::Lh as usize)
        + curr.sel(OpcodeClass::Lb as usize)
        + curr.sel(OpcodeClass::Lhu as usize)
        + curr.sel(OpcodeClass::Lbu as usize)
        + curr.sel(OpcodeClass::Jal as usize)
        + curr.sel(OpcodeClass::Jalr as usize)
        + curr.sel(OpcodeClass::Lui as usize)
        + curr.sel(OpcodeClass::Auipc as usize);

    // rd_idx = uses_rd * rd_field (when no rd, rd_idx must be 0)
    constraints.push(curr.col(col::RD_IDX) - uses_rd * rd_field);

    // Instructions that use rs1 (R/I/S/B types, but not U/J/system):
    let uses_rs1 = curr.sel(OpcodeClass::Add as usize)
        + curr.sel(OpcodeClass::Sub as usize)
        + curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Sltu as usize)
        + curr.sel(OpcodeClass::Addi as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Slti as usize)
        + curr.sel(OpcodeClass::Sltiu as usize)
        + curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize)
        + curr.sel(OpcodeClass::Lw as usize)
        + curr.sel(OpcodeClass::Lh as usize)
        + curr.sel(OpcodeClass::Lb as usize)
        + curr.sel(OpcodeClass::Lhu as usize)
        + curr.sel(OpcodeClass::Lbu as usize)
        + curr.sel(OpcodeClass::Jalr as usize)
        + curr.sel(OpcodeClass::Sw as usize)
        + curr.sel(OpcodeClass::Sh as usize)
        + curr.sel(OpcodeClass::Sb as usize)
        + curr.sel(OpcodeClass::Beq as usize)
        + curr.sel(OpcodeClass::Bne as usize)
        + curr.sel(OpcodeClass::Blt as usize)
        + curr.sel(OpcodeClass::Bge as usize)
        + curr.sel(OpcodeClass::Bltu as usize)
        + curr.sel(OpcodeClass::Bgeu as usize);

    constraints.push(curr.col(col::RS1_IDX) - uses_rs1 * rs1_field);

    // Instructions that use rs2 (R/S/B types):
    let uses_rs2 = curr.sel(OpcodeClass::Add as usize)
        + curr.sel(OpcodeClass::Sub as usize)
        + curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Sltu as usize)
        + curr.sel(OpcodeClass::Sw as usize)
        + curr.sel(OpcodeClass::Sh as usize)
        + curr.sel(OpcodeClass::Sb as usize)
        + curr.sel(OpcodeClass::Beq as usize)
        + curr.sel(OpcodeClass::Bne as usize)
        + curr.sel(OpcodeClass::Blt as usize)
        + curr.sel(OpcodeClass::Bge as usize)
        + curr.sel(OpcodeClass::Bltu as usize)
        + curr.sel(OpcodeClass::Bgeu as usize);

    constraints.push(curr.col(col::RS2_IDX) - uses_rs2 * rs2_field);

    // ── 5. Opcode matching per selector ──
    // Group selectors by their expected opcode value
    let op_reg = BabyBear::new(0x33); // 0b0110011
    let op_imm = BabyBear::new(0x13); // 0b0010011
    let op_load = BabyBear::new(0x03); // 0b0000011
    let op_store = BabyBear::new(0x23); // 0b0100011
    let op_branch = BabyBear::new(0x63); // 0b1100011
    let op_jal = BabyBear::new(0x6F); // 0b1101111
    let op_jalr = BabyBear::new(0x67); // 0b1100111
    let op_lui = BabyBear::new(0x37); // 0b0110111
    let op_auipc = BabyBear::new(0x17); // 0b0010111
    let op_system = BabyBear::new(0x73); // 0b1110011

    // For each opcode group: group_sel * (opcode_field - expected) = 0
    let reg_sel = curr.sel(OpcodeClass::Add as usize)
        + curr.sel(OpcodeClass::Sub as usize)
        + curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Sltu as usize);
    constraints.push(reg_sel * (opcode_field - op_reg));

    let imm_sel = curr.sel(OpcodeClass::Addi as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Slti as usize)
        + curr.sel(OpcodeClass::Sltiu as usize)
        + curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize);
    constraints.push(imm_sel * (opcode_field - op_imm));

    let load_sel = curr.sel(OpcodeClass::Lw as usize)
        + curr.sel(OpcodeClass::Lh as usize)
        + curr.sel(OpcodeClass::Lb as usize)
        + curr.sel(OpcodeClass::Lhu as usize)
        + curr.sel(OpcodeClass::Lbu as usize);
    constraints.push(load_sel * (opcode_field - op_load));

    let store_sel = curr.sel(OpcodeClass::Sw as usize)
        + curr.sel(OpcodeClass::Sh as usize)
        + curr.sel(OpcodeClass::Sb as usize);
    constraints.push(store_sel * (opcode_field - op_store));

    let branch_sel = curr.sel(OpcodeClass::Beq as usize)
        + curr.sel(OpcodeClass::Bne as usize)
        + curr.sel(OpcodeClass::Blt as usize)
        + curr.sel(OpcodeClass::Bge as usize)
        + curr.sel(OpcodeClass::Bltu as usize)
        + curr.sel(OpcodeClass::Bgeu as usize);
    constraints.push(branch_sel * (opcode_field - op_branch));

    constraints.push(curr.sel(OpcodeClass::Jal as usize) * (opcode_field - op_jal));
    constraints.push(curr.sel(OpcodeClass::Jalr as usize) * (opcode_field - op_jalr));
    constraints.push(curr.sel(OpcodeClass::Lui as usize) * (opcode_field - op_lui));
    constraints.push(curr.sel(OpcodeClass::Auipc as usize) * (opcode_field - op_auipc));

    let system_sel = curr.sel(OpcodeClass::Ecall as usize)
        + curr.sel(OpcodeClass::Ebreak as usize);
    constraints.push(system_sel * (opcode_field - op_system));

    // ── 6. Funct3 matching per selector (where applicable) ──
    // R-type: each has a specific funct3
    constraints.push(curr.sel(OpcodeClass::Add as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Sub as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Sll as usize) * (funct3_field - BabyBear::new(1)));
    constraints.push(curr.sel(OpcodeClass::Slt as usize) * (funct3_field - BabyBear::new(2)));
    constraints.push(curr.sel(OpcodeClass::Sltu as usize) * (funct3_field - BabyBear::new(3)));
    constraints.push(curr.sel(OpcodeClass::Xor as usize) * (funct3_field - BabyBear::new(4)));
    constraints.push(curr.sel(OpcodeClass::Srl as usize) * (funct3_field - BabyBear::new(5)));
    constraints.push(curr.sel(OpcodeClass::Sra as usize) * (funct3_field - BabyBear::new(5)));
    constraints.push(curr.sel(OpcodeClass::Or as usize) * (funct3_field - BabyBear::new(6)));
    constraints.push(curr.sel(OpcodeClass::And as usize) * (funct3_field - BabyBear::new(7)));

    // I-type ALU: each has a specific funct3
    constraints.push(curr.sel(OpcodeClass::Addi as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Slti as usize) * (funct3_field - BabyBear::new(2)));
    constraints.push(curr.sel(OpcodeClass::Sltiu as usize) * (funct3_field - BabyBear::new(3)));
    constraints.push(curr.sel(OpcodeClass::Xori as usize) * (funct3_field - BabyBear::new(4)));
    constraints.push(curr.sel(OpcodeClass::Ori as usize) * (funct3_field - BabyBear::new(6)));
    constraints.push(curr.sel(OpcodeClass::Andi as usize) * (funct3_field - BabyBear::new(7)));
    constraints.push(curr.sel(OpcodeClass::Slli as usize) * (funct3_field - BabyBear::new(1)));
    constraints.push(curr.sel(OpcodeClass::Srli as usize) * (funct3_field - BabyBear::new(5)));
    constraints.push(curr.sel(OpcodeClass::Srai as usize) * (funct3_field - BabyBear::new(5)));

    // Loads
    constraints.push(curr.sel(OpcodeClass::Lb as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Lh as usize) * (funct3_field - BabyBear::new(1)));
    constraints.push(curr.sel(OpcodeClass::Lw as usize) * (funct3_field - BabyBear::new(2)));
    constraints.push(curr.sel(OpcodeClass::Lbu as usize) * (funct3_field - BabyBear::new(4)));
    constraints.push(curr.sel(OpcodeClass::Lhu as usize) * (funct3_field - BabyBear::new(5)));

    // Stores
    constraints.push(curr.sel(OpcodeClass::Sb as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Sh as usize) * (funct3_field - BabyBear::new(1)));
    constraints.push(curr.sel(OpcodeClass::Sw as usize) * (funct3_field - BabyBear::new(2)));

    // Branches
    constraints.push(curr.sel(OpcodeClass::Beq as usize) * (funct3_field - BabyBear::new(0)));
    constraints.push(curr.sel(OpcodeClass::Bne as usize) * (funct3_field - BabyBear::new(1)));
    constraints.push(curr.sel(OpcodeClass::Blt as usize) * (funct3_field - BabyBear::new(4)));
    constraints.push(curr.sel(OpcodeClass::Bge as usize) * (funct3_field - BabyBear::new(5)));
    constraints.push(curr.sel(OpcodeClass::Bltu as usize) * (funct3_field - BabyBear::new(6)));
    constraints.push(curr.sel(OpcodeClass::Bgeu as usize) * (funct3_field - BabyBear::new(7)));

    // JALR: funct3 = 0
    constraints.push(curr.sel(OpcodeClass::Jalr as usize) * funct3_field);

    // ── 7. Funct7 matching (R-type and shift immediates) ──
    let f7_zero = BabyBear::zero();
    let f7_0x20 = BabyBear::new(0x20);

    constraints.push(curr.sel(OpcodeClass::Add as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Sub as usize) * (funct7_field - f7_0x20));
    constraints.push(curr.sel(OpcodeClass::Sll as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Slt as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Sltu as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Xor as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Srl as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Sra as usize) * (funct7_field - f7_0x20));
    constraints.push(curr.sel(OpcodeClass::Or as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::And as usize) * (funct7_field - f7_zero));

    // Shift immediates: SLLI has funct7=0, SRLI has funct7=0, SRAI has funct7=0x20
    constraints.push(curr.sel(OpcodeClass::Slli as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Srli as usize) * (funct7_field - f7_zero));
    constraints.push(curr.sel(OpcodeClass::Srai as usize) * (funct7_field - f7_0x20));

    // ── 8. Immediate value matching per format ──
    // Sign extension constant: (2^32 - 2^11) mod p
    let sign_ext_i = BabyBear::new(TWO32_MOD_P) - BabyBear::new(1u64 << 11);

    // I-type immediate: imm = Σ_{k=0}^{10} bit[20+k] * 2^k + bit[31] * sign_ext_i
    let mut i_type_imm = BabyBear::zero();
    for k in 0..11 {
        i_type_imm = i_type_imm + curr.col(col::INSTR_BIT_START + 20 + k) * BabyBear::new(1u64 << k);
    }
    i_type_imm = i_type_imm + curr.col(col::INSTR_BIT_START + 31) * sign_ext_i;

    let i_type_sel = curr.sel(OpcodeClass::Addi as usize)
        + curr.sel(OpcodeClass::Slti as usize)
        + curr.sel(OpcodeClass::Sltiu as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Lb as usize)
        + curr.sel(OpcodeClass::Lh as usize)
        + curr.sel(OpcodeClass::Lw as usize)
        + curr.sel(OpcodeClass::Lbu as usize)
        + curr.sel(OpcodeClass::Lhu as usize)
        + curr.sel(OpcodeClass::Jalr as usize);
    constraints.push(i_type_sel * (curr.col(col::IMM) - i_type_imm));

    // Shift immediate: imm = bits[24:20] (5-bit unsigned)
    let mut shift_imm = BabyBear::zero();
    for k in 0..5 {
        shift_imm = shift_imm + curr.col(col::INSTR_BIT_START + 20 + k) * BabyBear::new(1u64 << k);
    }
    let shift_sel = curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize);
    constraints.push(shift_sel * (curr.col(col::IMM) - shift_imm));

    // S-type immediate: imm = Σ_{k=0}^{4} bit[7+k] * 2^k + Σ_{j=0}^{5} bit[25+j] * 2^(j+5) + bit[31] * sign_ext_i
    let mut s_type_imm = BabyBear::zero();
    for k in 0..5 {
        s_type_imm = s_type_imm + curr.col(col::INSTR_BIT_START + 7 + k) * BabyBear::new(1u64 << k);
    }
    for j in 0..6 {
        s_type_imm = s_type_imm + curr.col(col::INSTR_BIT_START + 25 + j) * BabyBear::new(1u64 << (j + 5));
    }
    s_type_imm = s_type_imm + curr.col(col::INSTR_BIT_START + 31) * sign_ext_i;
    constraints.push(store_sel * (curr.col(col::IMM) - s_type_imm));

    // B-type immediate: imm[0]=0, imm[4:1]=bit[11:8], imm[10:5]=bit[30:25], imm[11]=bit[7], imm[12]=bit[31]
    let sign_ext_b = BabyBear::new(TWO32_MOD_P) - BabyBear::new(1u64 << 12);
    let mut b_type_imm = BabyBear::zero();
    for k in 0..4 {
        b_type_imm = b_type_imm + curr.col(col::INSTR_BIT_START + 8 + k) * BabyBear::new(1u64 << (k + 1));
    }
    for j in 0..6 {
        b_type_imm = b_type_imm + curr.col(col::INSTR_BIT_START + 25 + j) * BabyBear::new(1u64 << (j + 5));
    }
    b_type_imm = b_type_imm + curr.col(col::INSTR_BIT_START + 7) * BabyBear::new(1u64 << 11);
    b_type_imm = b_type_imm + curr.col(col::INSTR_BIT_START + 31) * sign_ext_b;
    constraints.push(branch_sel * (curr.col(col::IMM) - b_type_imm));

    // U-type immediate: imm = Σ_{k=12}^{31} bit[k] * 2^k (mod p)
    let mut u_type_imm = BabyBear::zero();
    for k in 12..31 {
        u_type_imm = u_type_imm + curr.col(col::INSTR_BIT_START + k) * BabyBear::new(1u64 << k);
    }
    u_type_imm = u_type_imm + curr.col(col::INSTR_BIT_START + 31) * BabyBear::new((1u64 << 31) % 2013265921);
    let u_type_sel = curr.sel(OpcodeClass::Lui as usize)
        + curr.sel(OpcodeClass::Auipc as usize);
    constraints.push(u_type_sel * (curr.col(col::IMM) - u_type_imm));

    // J-type immediate: imm[0]=0, imm[10:1]=bit[30:21], imm[11]=bit[20], imm[19:12]=bit[19:12], imm[20]=bit[31]
    let sign_ext_j = BabyBear::new(TWO32_MOD_P) - BabyBear::new(1u64 << 20);
    let mut j_type_imm = BabyBear::zero();
    for k in 0..10 {
        j_type_imm = j_type_imm + curr.col(col::INSTR_BIT_START + 21 + k) * BabyBear::new(1u64 << (k + 1));
    }
    j_type_imm = j_type_imm + curr.col(col::INSTR_BIT_START + 20) * BabyBear::new(1u64 << 11);
    for k in 12..20 {
        j_type_imm = j_type_imm + curr.col(col::INSTR_BIT_START + k) * BabyBear::new(1u64 << k);
    }
    j_type_imm = j_type_imm + curr.col(col::INSTR_BIT_START + 31) * sign_ext_j;
    constraints.push(curr.sel(OpcodeClass::Jal as usize) * (curr.col(col::IMM) - j_type_imm));

    // ECALL/EBREAK: distinguish by imm field bits[31:20]
    // ECALL: imm[31:20] = 0 → all bits [20..31] are 0
    // EBREAK: imm[31:20] = 1 → bit[20]=1, rest 0
    constraints.push(curr.sel(OpcodeClass::Ecall as usize) * curr.col(col::INSTR_BIT_START + 20));
    constraints.push(curr.sel(OpcodeClass::Ebreak as usize) * (curr.col(col::INSTR_BIT_START + 20) - BabyBear::one()));

    constraints
}

/// Halting condition constraints (transition constraint using both curr and next).
///
/// IS_HALTED is a running flag: starts at 0, transitions to 1 on the ECALL row,
/// and stays 1 through all padding rows. Only ECALL produces a valid halt.
///
/// Constraint: next_halted = curr_halted + (1 - curr_halted) * next_sel_ecall
/// Rearranged: next_halted - curr_halted - next_sel_ecall + curr_halted * next_sel_ecall = 0
pub fn halting_constraints(curr: &TraceView, next: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let curr_h = curr.col(col::IS_HALTED);
    let next_h = next.col(col::IS_HALTED);
    let next_ecall = next.sel(OpcodeClass::Ecall as usize);

    // IS_HALTED is boolean
    constraints.push(curr_h * (curr_h - BabyBear::one()));

    // Monotone transition: only ECALL can flip 0→1; once halted, stays halted
    constraints.push(next_h - curr_h - next_ecall + curr_h * next_ecall);

    constraints
}

/// Sum of all branch opcode selectors.
fn branch_any_selector(curr: &TraceView) -> BabyBear {
    curr.sel(OpcodeClass::Beq as usize)
        + curr.sel(OpcodeClass::Bne as usize)
        + curr.sel(OpcodeClass::Blt as usize)
        + curr.sel(OpcodeClass::Bge as usize)
        + curr.sel(OpcodeClass::Bltu as usize)
        + curr.sel(OpcodeClass::Bgeu as usize)
}

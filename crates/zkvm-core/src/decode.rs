/// RISC-V RV32I instruction decoder.

/// Opcode field values (bits [6:0]).
pub const OP_LUI: u32 = 0b0110111;
pub const OP_AUIPC: u32 = 0b0010111;
pub const OP_JAL: u32 = 0b1101111;
pub const OP_JALR: u32 = 0b1100111;
pub const OP_BRANCH: u32 = 0b1100011;
pub const OP_LOAD: u32 = 0b0000011;
pub const OP_STORE: u32 = 0b0100011;
pub const OP_IMM: u32 = 0b0010011;
pub const OP_REG: u32 = 0b0110011;
pub const OP_SYSTEM: u32 = 0b1110011;

/// Funct3 values for branch instructions.
pub const F3_BEQ: u32 = 0b000;
pub const F3_BNE: u32 = 0b001;
pub const F3_BLT: u32 = 0b100;
pub const F3_BGE: u32 = 0b101;
pub const F3_BLTU: u32 = 0b110;
pub const F3_BGEU: u32 = 0b111;

/// Funct3 values for load instructions.
pub const F3_LB: u32 = 0b000;
pub const F3_LH: u32 = 0b001;
pub const F3_LW: u32 = 0b010;
pub const F3_LBU: u32 = 0b100;
pub const F3_LHU: u32 = 0b101;

/// Funct3 values for store instructions.
pub const F3_SB: u32 = 0b000;
pub const F3_SH: u32 = 0b001;
pub const F3_SW: u32 = 0b010;

/// Funct3 values for ALU immediate.
pub const F3_ADDI: u32 = 0b000;
pub const F3_SLTI: u32 = 0b010;
pub const F3_SLTIU: u32 = 0b011;
pub const F3_XORI: u32 = 0b100;
pub const F3_ORI: u32 = 0b110;
pub const F3_ANDI: u32 = 0b111;
pub const F3_SLLI: u32 = 0b001;
pub const F3_SRLI_SRAI: u32 = 0b101;

/// Funct3 values for ALU register.
pub const F3_ADD_SUB: u32 = 0b000;
pub const F3_SLL: u32 = 0b001;
pub const F3_SLT: u32 = 0b010;
pub const F3_SLTU: u32 = 0b011;
pub const F3_XOR: u32 = 0b100;
pub const F3_SRL_SRA: u32 = 0b101;
pub const F3_OR: u32 = 0b110;
pub const F3_AND: u32 = 0b111;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    // U-type
    Lui { rd: u32, imm: u32 },
    Auipc { rd: u32, imm: u32 },

    // J-type
    Jal { rd: u32, imm: i32 },

    // I-type (JALR)
    Jalr { rd: u32, rs1: u32, imm: i32 },

    // B-type
    Beq { rs1: u32, rs2: u32, imm: i32 },
    Bne { rs1: u32, rs2: u32, imm: i32 },
    Blt { rs1: u32, rs2: u32, imm: i32 },
    Bge { rs1: u32, rs2: u32, imm: i32 },
    Bltu { rs1: u32, rs2: u32, imm: i32 },
    Bgeu { rs1: u32, rs2: u32, imm: i32 },

    // I-type (loads)
    Lb { rd: u32, rs1: u32, imm: i32 },
    Lh { rd: u32, rs1: u32, imm: i32 },
    Lw { rd: u32, rs1: u32, imm: i32 },
    Lbu { rd: u32, rs1: u32, imm: i32 },
    Lhu { rd: u32, rs1: u32, imm: i32 },

    // S-type (stores)
    Sb { rs1: u32, rs2: u32, imm: i32 },
    Sh { rs1: u32, rs2: u32, imm: i32 },
    Sw { rs1: u32, rs2: u32, imm: i32 },

    // I-type (ALU immediate)
    Addi { rd: u32, rs1: u32, imm: i32 },
    Slti { rd: u32, rs1: u32, imm: i32 },
    Sltiu { rd: u32, rs1: u32, imm: i32 },
    Xori { rd: u32, rs1: u32, imm: i32 },
    Ori { rd: u32, rs1: u32, imm: i32 },
    Andi { rd: u32, rs1: u32, imm: i32 },
    Slli { rd: u32, rs1: u32, shamt: u32 },
    Srli { rd: u32, rs1: u32, shamt: u32 },
    Srai { rd: u32, rs1: u32, shamt: u32 },

    // R-type (ALU register)
    Add { rd: u32, rs1: u32, rs2: u32 },
    Sub { rd: u32, rs1: u32, rs2: u32 },
    Sll { rd: u32, rs1: u32, rs2: u32 },
    Slt { rd: u32, rs1: u32, rs2: u32 },
    Sltu { rd: u32, rs1: u32, rs2: u32 },
    Xor { rd: u32, rs1: u32, rs2: u32 },
    Srl { rd: u32, rs1: u32, rs2: u32 },
    Sra { rd: u32, rs1: u32, rs2: u32 },
    Or { rd: u32, rs1: u32, rs2: u32 },
    And { rd: u32, rs1: u32, rs2: u32 },

    // System
    Ecall,
    Ebreak,

    // Pseudo-instruction for unrecognized encodings
    Invalid(u32),
}

/// Extract fields from an instruction word.
#[inline]
fn opcode(w: u32) -> u32 {
    w & 0x7f
}
#[inline]
fn rd(w: u32) -> u32 {
    (w >> 7) & 0x1f
}
#[inline]
fn funct3(w: u32) -> u32 {
    (w >> 12) & 0x7
}
#[inline]
fn rs1(w: u32) -> u32 {
    (w >> 15) & 0x1f
}
#[inline]
fn rs2(w: u32) -> u32 {
    (w >> 20) & 0x1f
}
#[inline]
fn funct7(w: u32) -> u32 {
    (w >> 25) & 0x7f
}

/// Sign-extend a value from `bits` width to i32.
#[inline]
fn sign_extend(val: u32, bits: u32) -> i32 {
    let shift = 32 - bits;
    ((val << shift) as i32) >> shift
}

/// I-type immediate: bits [31:20], sign-extended.
fn imm_i(w: u32) -> i32 {
    sign_extend(w >> 20, 12)
}

/// S-type immediate: bits [31:25] | [11:7], sign-extended.
fn imm_s(w: u32) -> i32 {
    let hi = (w >> 25) & 0x7f;
    let lo = (w >> 7) & 0x1f;
    sign_extend((hi << 5) | lo, 12)
}

/// B-type immediate: bits [31|7|30:25|11:8] << 1, sign-extended.
fn imm_b(w: u32) -> i32 {
    let bit12 = (w >> 31) & 1;
    let bit11 = (w >> 7) & 1;
    let bits10_5 = (w >> 25) & 0x3f;
    let bits4_1 = (w >> 8) & 0xf;
    let val = (bit12 << 12) | (bit11 << 11) | (bits10_5 << 5) | (bits4_1 << 1);
    sign_extend(val, 13)
}

/// U-type immediate: bits [31:12] << 12.
fn imm_u(w: u32) -> u32 {
    w & 0xfffff000
}

/// J-type immediate: bits [31|19:12|20|30:21] << 1, sign-extended.
fn imm_j(w: u32) -> i32 {
    let bit20 = (w >> 31) & 1;
    let bits10_1 = (w >> 21) & 0x3ff;
    let bit11 = (w >> 20) & 1;
    let bits19_12 = (w >> 12) & 0xff;
    let val = (bit20 << 20) | (bits19_12 << 12) | (bit11 << 11) | (bits10_1 << 1);
    sign_extend(val, 21)
}

/// Decode a 32-bit RISC-V instruction word into a structured `Instruction`.
pub fn decode(w: u32) -> Instruction {
    match opcode(w) {
        OP_LUI => Instruction::Lui {
            rd: rd(w),
            imm: imm_u(w),
        },
        OP_AUIPC => Instruction::Auipc {
            rd: rd(w),
            imm: imm_u(w),
        },
        OP_JAL => Instruction::Jal {
            rd: rd(w),
            imm: imm_j(w),
        },
        OP_JALR => Instruction::Jalr {
            rd: rd(w),
            rs1: rs1(w),
            imm: imm_i(w),
        },
        OP_BRANCH => {
            let r1 = rs1(w);
            let r2 = rs2(w);
            let imm = imm_b(w);
            match funct3(w) {
                F3_BEQ => Instruction::Beq { rs1: r1, rs2: r2, imm },
                F3_BNE => Instruction::Bne { rs1: r1, rs2: r2, imm },
                F3_BLT => Instruction::Blt { rs1: r1, rs2: r2, imm },
                F3_BGE => Instruction::Bge { rs1: r1, rs2: r2, imm },
                F3_BLTU => Instruction::Bltu { rs1: r1, rs2: r2, imm },
                F3_BGEU => Instruction::Bgeu { rs1: r1, rs2: r2, imm },
                _ => Instruction::Invalid(w),
            }
        }
        OP_LOAD => {
            let d = rd(w);
            let r1 = rs1(w);
            let imm = imm_i(w);
            match funct3(w) {
                F3_LB => Instruction::Lb { rd: d, rs1: r1, imm },
                F3_LH => Instruction::Lh { rd: d, rs1: r1, imm },
                F3_LW => Instruction::Lw { rd: d, rs1: r1, imm },
                F3_LBU => Instruction::Lbu { rd: d, rs1: r1, imm },
                F3_LHU => Instruction::Lhu { rd: d, rs1: r1, imm },
                _ => Instruction::Invalid(w),
            }
        }
        OP_STORE => {
            let r1 = rs1(w);
            let r2 = rs2(w);
            let imm = imm_s(w);
            match funct3(w) {
                F3_SB => Instruction::Sb { rs1: r1, rs2: r2, imm },
                F3_SH => Instruction::Sh { rs1: r1, rs2: r2, imm },
                F3_SW => Instruction::Sw { rs1: r1, rs2: r2, imm },
                _ => Instruction::Invalid(w),
            }
        }
        OP_IMM => {
            let d = rd(w);
            let r1 = rs1(w);
            let imm = imm_i(w);
            match funct3(w) {
                F3_ADDI => Instruction::Addi { rd: d, rs1: r1, imm },
                F3_SLTI => Instruction::Slti { rd: d, rs1: r1, imm },
                F3_SLTIU => Instruction::Sltiu { rd: d, rs1: r1, imm },
                F3_XORI => Instruction::Xori { rd: d, rs1: r1, imm },
                F3_ORI => Instruction::Ori { rd: d, rs1: r1, imm },
                F3_ANDI => Instruction::Andi { rd: d, rs1: r1, imm },
                F3_SLLI => Instruction::Slli {
                    rd: d,
                    rs1: r1,
                    shamt: (w >> 20) & 0x1f,
                },
                F3_SRLI_SRAI => {
                    if funct7(w) & 0x20 != 0 {
                        Instruction::Srai {
                            rd: d,
                            rs1: r1,
                            shamt: (w >> 20) & 0x1f,
                        }
                    } else {
                        Instruction::Srli {
                            rd: d,
                            rs1: r1,
                            shamt: (w >> 20) & 0x1f,
                        }
                    }
                }
                _ => Instruction::Invalid(w),
            }
        }
        OP_REG => {
            let d = rd(w);
            let r1 = rs1(w);
            let r2 = rs2(w);
            let f7 = funct7(w);
            match funct3(w) {
                F3_ADD_SUB => {
                    if f7 == 0x20 {
                        Instruction::Sub { rd: d, rs1: r1, rs2: r2 }
                    } else {
                        Instruction::Add { rd: d, rs1: r1, rs2: r2 }
                    }
                }
                F3_SLL => Instruction::Sll { rd: d, rs1: r1, rs2: r2 },
                F3_SLT => Instruction::Slt { rd: d, rs1: r1, rs2: r2 },
                F3_SLTU => Instruction::Sltu { rd: d, rs1: r1, rs2: r2 },
                F3_XOR => Instruction::Xor { rd: d, rs1: r1, rs2: r2 },
                F3_SRL_SRA => {
                    if f7 == 0x20 {
                        Instruction::Sra { rd: d, rs1: r1, rs2: r2 }
                    } else {
                        Instruction::Srl { rd: d, rs1: r1, rs2: r2 }
                    }
                }
                F3_OR => Instruction::Or { rd: d, rs1: r1, rs2: r2 },
                F3_AND => Instruction::And { rd: d, rs1: r1, rs2: r2 },
                _ => Instruction::Invalid(w),
            }
        }
        OP_SYSTEM => {
            let imm = (w >> 20) & 0xfff;
            match imm {
                0 => Instruction::Ecall,
                1 => Instruction::Ebreak,
                _ => Instruction::Invalid(w),
            }
        }
        _ => Instruction::Invalid(w),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_addi() {
        // addi x1, x0, 42  →  0x02a00093
        let w = 0x02a00093;
        let instr = decode(w);
        assert_eq!(instr, Instruction::Addi { rd: 1, rs1: 0, imm: 42 });
    }

    #[test]
    fn test_decode_add() {
        // add x3, x1, x2  →  0x002080b3 (funct7=0, rs2=2, rs1=1, funct3=0, rd=3, op=0x33 -> wrong)
        // Correct: add x3, x1, x2 → 0x002081b3
        let w = 0x002081b3;
        let instr = decode(w);
        assert_eq!(instr, Instruction::Add { rd: 3, rs1: 1, rs2: 2 });
    }

    #[test]
    fn test_decode_lui() {
        // lui x5, 0x12345  →  0x123452b7
        let w = 0x123452b7;
        let instr = decode(w);
        assert_eq!(instr, Instruction::Lui { rd: 5, imm: 0x12345000 });
    }

    #[test]
    fn test_decode_jal() {
        // jal x1, 8 → offset=8, rd=1
        // Encoding: imm[20|10:1|11|19:12] | rd | 1101111
        // offset 8 = 0b1000
        // bits10_1 = 0b0000000100, bit11=0, bits19_12=0, bit20=0
        // [0|0000000100|0|00000000] | 00001 | 1101111
        let w = 0x008000ef;
        let instr = decode(w);
        assert_eq!(instr, Instruction::Jal { rd: 1, imm: 8 });
    }

    #[test]
    fn test_sign_extend() {
        assert_eq!(sign_extend(0xfff, 12), -1);
        assert_eq!(sign_extend(0x7ff, 12), 2047);
        assert_eq!(sign_extend(0x800, 12), -2048);
    }
}

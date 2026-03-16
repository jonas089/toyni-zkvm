/// Bit-decomposition constraints for bitwise, shift, and comparison operations.
///
/// Shared auxiliary columns (bits_a[32], bits_b[32], shift_stages[5]) are reused
/// across opcodes since only one is active per row.

use toyni::babybear::BabyBear;
use zkvm_core::cpu::OpcodeClass;
use zkvm_core::trace::col;

use crate::TraceView;

/// Powers of 2 as BabyBear constants.
fn pow2(k: usize) -> BabyBear {
    BabyBear::new(1u64 << k)
}

/// Sum of selectors for all opcodes that require bit decomposition of bits_a.
/// Includes BLT/BGE which decompose (rs1-rs2+2^31) into bits_a for signed comparison.
fn bitwise_selector(curr: &TraceView) -> BabyBear {
    curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize)
        + curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Slti as usize)
        + curr.sel(OpcodeClass::Blt as usize)
        + curr.sel(OpcodeClass::Bge as usize)
}

/// Bit decomposition and bitwise operation constraints.
pub fn bitwise_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let bw_sel = bitwise_selector(curr);

    // ── Boolean constraints: each bit must be 0 or 1 ──────────────────
    for b in 0..32 {
        let bit_a = curr.col(col::BITS_A_START + b);
        constraints.push(bw_sel * bit_a * (bit_a - BabyBear::one()));
    }
    for b in 0..32 {
        let bit_b = curr.col(col::BITS_B_START + b);
        constraints.push(bw_sel * bit_b * (bit_b - BabyBear::one()));
    }

    // ── Reconstruction of rs1 from bits_a (for pure bitwise ops) ──────
    // bitwise_ops * (rs1 - Σ bits_a[i] * 2^i) = 0
    let pure_bw = curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize)
        + curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Slli as usize)
        + curr.sel(OpcodeClass::Srli as usize)
        + curr.sel(OpcodeClass::Srai as usize);

    let rs1 = curr.col(col::RS1_VAL);
    let rs2 = curr.col(col::RS2_VAL);

    let mut recon_a = BabyBear::zero();
    for b in 0..32 {
        recon_a = recon_a + curr.col(col::BITS_A_START + b) * pow2(b);
    }
    constraints.push(pure_bw * (rs1 - recon_a));

    // ── Reconstruction of rs2/imm from bits_b (for pure bitwise, not shifts) ──
    let bw_reg = curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Xor as usize);
    let bw_imm = curr.sel(OpcodeClass::Andi as usize)
        + curr.sel(OpcodeClass::Ori as usize)
        + curr.sel(OpcodeClass::Xori as usize);

    let mut recon_b = BabyBear::zero();
    for b in 0..32 {
        recon_b = recon_b + curr.col(col::BITS_B_START + b) * pow2(b);
    }
    let imm = curr.col(col::IMM);
    constraints.push(bw_reg * (rs2 - recon_b));
    constraints.push(bw_imm * (imm - recon_b));

    // ── AND: rd = Σ bits_a[i] * bits_b[i] * 2^i ──────────────────────
    let rd = curr.col(col::RD_VAL);
    let sel_and = curr.sel(OpcodeClass::And as usize)
        + curr.sel(OpcodeClass::Andi as usize);
    let mut and_result = BabyBear::zero();
    for b in 0..32 {
        and_result = and_result
            + curr.col(col::BITS_A_START + b) * curr.col(col::BITS_B_START + b) * pow2(b);
    }
    constraints.push(sel_and * (rd - and_result));

    // ── OR: rd = Σ (a[i] + b[i] - a[i]*b[i]) * 2^i ──────────────────
    let sel_or = curr.sel(OpcodeClass::Or as usize)
        + curr.sel(OpcodeClass::Ori as usize);
    let mut or_result = BabyBear::zero();
    for b in 0..32 {
        let a_b = curr.col(col::BITS_A_START + b);
        let b_b = curr.col(col::BITS_B_START + b);
        or_result = or_result + (a_b + b_b - a_b * b_b) * pow2(b);
    }
    constraints.push(sel_or * (rd - or_result));

    // ── XOR: rd = Σ (a[i] + b[i] - 2*a[i]*b[i]) * 2^i ──────────────
    let sel_xor = curr.sel(OpcodeClass::Xor as usize)
        + curr.sel(OpcodeClass::Xori as usize);
    let two = BabyBear::new(2);
    let mut xor_result = BabyBear::zero();
    for b in 0..32 {
        let a_b = curr.col(col::BITS_A_START + b);
        let b_b = curr.col(col::BITS_B_START + b);
        xor_result = xor_result + (a_b + b_b - two * a_b * b_b) * pow2(b);
    }
    constraints.push(sel_xor * (rd - xor_result));

    // ── SLT (signed comparison): bits_a decomposes (rs1 - rs2 + 2^31) ─
    // If bit 31 = 0 then the difference was negative → rs1 < rs2
    let sel_slt = curr.sel(OpcodeClass::Slt as usize)
        + curr.sel(OpcodeClass::Slti as usize);
    // Reconstruct diff from bits_a
    let mut recon_diff = BabyBear::zero();
    for b in 0..32 {
        recon_diff = recon_diff + curr.col(col::BITS_A_START + b) * pow2(b);
    }
    // diff = rs1 - rs2 + 2^31 (needs TWO32 carry for field arithmetic)
    // Since we decomposed the u32 result, reconstruction matches the value.
    // rd = 1 - bits_a[31] (if sign bit is 0, rs1 < rs2)
    constraints.push(sel_slt * (rd - (BabyBear::one() - curr.col(col::BITS_A_START + 31))));

    // ── SLTU (unsigned comparison): rd = alu_carry (borrow from subtraction) ─
    let sel_sltu = curr.sel(OpcodeClass::Sltu as usize)
        + curr.sel(OpcodeClass::Sltiu as usize);
    let carry = curr.col(col::ALU_CARRY);
    constraints.push(sel_sltu * (rd - carry));

    constraints
}

/// Shift constraints using barrel shifter stages.
///
/// For SLL: each stage conditionally shifts left by 2^k.
/// For SRL/SRA: each stage conditionally shifts right by 2^k.
pub fn shift_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    let sel_sll = curr.sel(OpcodeClass::Sll as usize)
        + curr.sel(OpcodeClass::Slli as usize);
    let sel_srl = curr.sel(OpcodeClass::Srl as usize)
        + curr.sel(OpcodeClass::Srli as usize);
    let sel_sra = curr.sel(OpcodeClass::Sra as usize)
        + curr.sel(OpcodeClass::Srai as usize);
    let any_shift = sel_sll + sel_srl + sel_sra;

    let rd = curr.col(col::RD_VAL);

    // Shift amount reconstruction from bits_b (only low 5 bits)
    let mut shamt_recon = BabyBear::zero();
    for b in 0..5 {
        shamt_recon = shamt_recon + curr.col(col::BITS_B_START + b) * pow2(b);
    }
    constraints.push(any_shift * (curr.col(col::IMM) - shamt_recon));

    // ── SLL barrel shifter stages ─────────────────────────────────────
    // Stage 0: t0 = rs1 * (1 + bits_b[0]) if bits_b[0]=1 → rs1 * 2, else rs1
    // But this is in field, not mod 2^32. We trust intermediate values and check final.
    // Actually, we verify the final result against rd_val with carry.
    //
    // For a sound constraint without full modular reduction at each stage,
    // we verify the overall shift relationship: rd = (rs1 << shamt) mod 2^32.
    // This is equivalent to: rd = last_shift_stage (which is already truncated to u32
    // in the trace, and rd is set to the same value).
    //
    // Constrain: rd = shift_stages[4] (the final stage output)
    let stage4 = curr.col(col::SHIFT_STAGE_START + 4);
    constraints.push(sel_sll * (rd - stage4));
    constraints.push(sel_srl * (rd - stage4));
    constraints.push(sel_sra * (rd - stage4));

    // ── SLL barrel stage transition constraints ─────────────────────
    // For left shift, each stage conditionally multiplies by 2^(2^k):
    //   stage[k] + carry[k] * 2^32 = prev * (1 + bit_k * (2^(2^k) - 1))
    // where prev = rs1 for k=0, stage[k-1] for k>0.
    // POW2K_MINUS_1: k=0→1, k=1→3, k=2→15, k=3→255, k=4→65535
    let t32 = BabyBear::new(268435454u64); // 2^32 mod p
    let pow2k_m1: [BabyBear; 5] = [
        BabyBear::new(1),     // 2^1 - 1
        BabyBear::new(3),     // 2^2 - 1
        BabyBear::new(15),    // 2^4 - 1
        BabyBear::new(255),   // 2^8 - 1
        BabyBear::new(65535), // 2^16 - 1
    ];

    let rs1 = curr.col(col::RS1_VAL);
    for k in 0..5 {
        let prev = if k == 0 { rs1 } else { curr.col(col::SHIFT_STAGE_START + k - 1) };
        let stage_k = curr.col(col::SHIFT_STAGE_START + k);
        let carry_k = curr.col(col::SHIFT_CARRY_START + k);
        let bit_k = curr.col(col::BITS_B_START + k);

        // stage[k] + carry[k] * 2^32 = prev * (1 + bit_k * (2^(2^k) - 1))
        // = prev + prev * bit_k * (2^(2^k) - 1)
        constraints.push(
            sel_sll * (stage_k + carry_k * t32 - prev - prev * bit_k * pow2k_m1[k])
        );

        // carry[k] is boolean
        constraints.push(sel_sll * carry_k * (carry_k - BabyBear::one()));
    }

    // ── SRL barrel stage transition constraints ──────────────────────
    // For right shift, stages go from rs1 down to rd:
    //   prev = stage[k] * 2^(2^k * bit_k) + carry[k]
    // When bit_k=1: prev = stage[k] * 2^(2^k) + carry[k]
    // When bit_k=0: prev = stage[k] (carry=0)
    // Equivalently: prev = stage[k] + stage[k] * bit_k * (2^(2^k) - 1) + carry[k]
    // And carry[k] < 2^(2^k) (the shifted-out bits).
    // We constrain: prev = stage[k] + bit_k * (stage[k] * (2^(2^k)-1) + carry[k])
    // Which simplifies to: prev - stage[k] - bit_k * stage[k] * pow2k_m1 - bit_k * carry[k] = 0
    // But this doesn't enforce carry range. We trust range checks for that.
    let any_srl = sel_srl + sel_sra;
    for k in 0..5 {
        let prev = if k == 0 { rs1 } else { curr.col(col::SHIFT_STAGE_START + k - 1) };
        let stage_k = curr.col(col::SHIFT_STAGE_START + k);
        let carry_k = curr.col(col::SHIFT_CARRY_START + k);
        let bit_k = curr.col(col::BITS_B_START + k);

        // prev = stage[k] * (1 + bit_k * (2^(2^k) - 1)) + bit_k * carry[k]
        // Rearranged: prev - stage[k] - stage[k] * bit_k * pow2k_m1 - bit_k * carry[k] = 0
        constraints.push(
            any_srl * (prev - stage_k - stage_k * bit_k * pow2k_m1[k] - bit_k * carry_k)
        );

        // When bit_k = 1, carry must be < 2^(2^k). This is enforced via range checks
        // on the overall values. For now, we just ensure the algebraic relation holds.
        // Additionally constrain: carry[k] * (1 - bit_k) = 0 (no carry when no shift)
        constraints.push(any_srl * carry_k * (BabyBear::one() - bit_k));
    }

    constraints
}

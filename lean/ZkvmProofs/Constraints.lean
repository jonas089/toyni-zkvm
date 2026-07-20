/-
# The zkvm trace row and its transition constraints, transcribed 1:1

This file is the **trusted transcription boundary**: `TransitionConstraints`
mirrors `zkvm-air/src/lib.rs::eval_transition_constraints` equation for
equation, in the same order, under the same names (each field's docstring
carries the Rust constraint name). Everything downstream is proven; if this
file matches the Rust, the theorems apply to the real AIR.

Modeling notes:

* Rows are BabyBear-valued (`BB`). The Rust evaluates over the quartic
  extension, but every committed value is base-field and every equation has
  base coefficients, so satisfaction is equivalent (the base field embeds).
* Only the columns that appear in transition constraints are modeled as
  named fields (the Rust indexes a flat array; names follow
  `zkvm-core::col`).
* One-hot selectors are `sel : Fin 11 → BB`, indexed per `zkvm-air::opc`.
* The sorted register table's three per-row entries and the sorted memory
  entry are sub-structures; their *transition* packs
  (`reg_slot_transition`, `mem_slot_transition`) are transcribed as
  parameterized predicates, instantiated exactly like the Rust: A→B and
  B→C within a row, C→A and mem across rows.
-/
import ZkvmProofs.Field

namespace Zkvm

/-- Opcode selector indices, per `zkvm-air::opc`. -/
def oADD : Fin 11 := 0
def oSUB : Fin 11 := 1
def oMUL : Fin 11 := 2
def oIMM : Fin 11 := 3
def oLOAD : Fin 11 := 4
def oSTORE : Fin 11 := 5
def oJMP : Fin 11 := 6
def oJZ : Fin 11 := 7
def oREAD : Fin 11 := 8
def oWRITE : Fin 11 := 9
def oHALT : Fin 11 := 10

/-- One register-access slot: `(idx, val, wr, inv, act)`. -/
structure Slot where
  idx : BB
  val : BB
  wr : BB
  inv : BB
  act : BB

/-- One sorted register-table entry:
`(idx, val, t, wr, idx_inv, same_idx, diff_inv)` plus its diff-bit block. -/
structure SEntry where
  idx : BB
  val : BB
  t : BB
  wr : BB
  idxInv : BB
  sameIdx : BB
  diffInv : BB
  diffBits : Fin 16 → BB

/-- The sorted memory entry:
`(addr, val, clk, is_write, used, same_addr, diff_inv)` + diff bits. -/
structure SMem where
  addr : BB
  val : BB
  clk : BB
  wr : BB
  used : BB
  sameAddr : BB
  diffInv : BB
  diffBits : Fin 16 → BB

/-- Program-ROM table row: `(addr, opcode, op_a, op_b, op_c, mult, real)`
plus the multiplicity range-check bits. -/
structure Rom where
  addr : BB
  opcode : BB
  opA : BB
  opB : BB
  opC : BB
  mult : BB
  real : BB
  multBits : Fin 16 → BB

/-- One trace row (the transition-constraint-relevant columns of
`zkvm-core::col`). -/
structure Row where
  clk : BB
  pc : BB
  nextPc : BB
  opcode : BB
  opA : BB
  opB : BB
  opC : BB
  halt : BB
  iIn : BB
  iOut : BB
  slotA : Slot
  slotB : Slot
  slotC : Slot
  memAddr : BB
  memVal : BB
  memWr : BB
  memUsed : BB
  jzIsZero : BB
  jzValInv : BB
  sel : Fin 11 → BB
  sregA : SEntry
  sregB : SEntry
  sregC : SEntry
  smem : SMem
  rom : Rom

namespace Row

/-- `s_alu = s_add + s_sub + s_mul` (Rust local). -/
noncomputable def sAlu (r : Row) : BB := r.sel oADD + r.sel oSUB + r.sel oMUL

end Row

/-- Slot well-formedness pack (Rust: the `REG_SLOTS` loop). -/
structure SlotWf (s : Slot) : Prop where
  /-- SLOT_ACTIVE_BOOLEAN -/
  act_boolean : s.act * (s.act - 1) = 0
  /-- SLOT_INACTIVE_ZEROED (idx) -/
  inactive_idx : (1 - s.act) * s.idx = 0
  /-- SLOT_INACTIVE_ZEROED (val) -/
  inactive_val : (1 - s.act) * s.val = 0
  /-- SLOT_INACTIVE_ZEROED (wr) -/
  inactive_wr : (1 - s.act) * s.wr = 0
  /-- SLOT_WR_BOOLEAN -/
  wr_boolean : s.wr * (s.wr - 1) = 0
  /-- R0_IDX_INV -/
  r0_idx_inv : s.idx * (1 - s.idx * s.inv) = 0
  /-- R0_VAL_ZERO -/
  r0_val_zero : (1 - s.idx * s.inv) * s.val = 0

/-- Sorted register-slot transition pack (Rust: `reg_slot_transition`),
between entry `p` (prev) and `q` (next); `sameIdx`, `diffInv` and the diff
bits live on `p`'s aux/bits block exactly as in Rust. -/
structure SRegTrans (p q : SEntry) : Prop where
  /-- SORTED_R0_PIN (inverse part, on prev) -/
  r0_pin_inv : p.idx * (1 - p.idx * p.idxInv) = 0
  /-- SORTED_R0_PIN (value part, on prev) -/
  r0_pin_val : (1 - p.idx * p.idxInv) * p.val = 0
  /-- SORTED_SAME_KEY_BOOLEAN -/
  same_boolean : p.sameIdx * (p.sameIdx - 1) = 0
  /-- SORTED_SAME_KEY_MATCH -/
  same_match : p.sameIdx * (q.idx - p.idx) = 0
  /-- SORTED_DIFF_KEY_INV -/
  diff_key_inv : (1 - p.sameIdx) * (1 - (q.idx - p.idx) * p.diffInv) = 0
  /-- SORTED_RAW: same key + next reads ⇒ value carries over -/
  raw : p.sameIdx * (1 - q.wr) * (q.val - p.val) = 0
  /-- Init binding: fresh key + read ⇒ value 0 -/
  init : (1 - p.sameIdx) * (1 - q.wr) * q.val = 0
  /-- SORTED_STRICT_DIFF bit booleanity -/
  bits_boolean : ∀ k : Fin 16, p.diffBits k * (p.diffBits k - 1) = 0
  /-- SORTED_STRICT_DIFF reconstruction: diff = 1 + Σ bit·2^k -/
  strict_diff :
    p.sameIdx * (q.t - p.t) + (1 - p.sameIdx) * (q.idx - p.idx) =
      1 + ∑ k : Fin 16, p.diffBits k * ((2 ^ (k : ℕ) : ℕ) : BB)

/-- Sorted memory transition pack (Rust: `mem_slot_transition`). -/
structure SMemTrans (p q : SMem) : Prop where
  same_boolean : p.sameAddr * (p.sameAddr - 1) = 0
  same_match : p.sameAddr * (q.addr - p.addr) = 0
  diff_key_inv : (1 - p.sameAddr) * (1 - (q.addr - p.addr) * p.diffInv) = 0
  /-- R-A-W (gated on the next access being used and a read) -/
  raw : q.used * p.sameAddr * (1 - q.wr) * (q.val - p.val) = 0
  /-- Init binding -/
  init : q.used * (1 - p.sameAddr) * (1 - q.wr) * q.val = 0
  bits_boolean : ∀ k : Fin 16, p.diffBits k * (p.diffBits k - 1) = 0
  strict_diff :
    p.sameAddr * (q.clk - p.clk) + (1 - p.sameAddr) * (q.addr - p.addr) =
      1 + ∑ k : Fin 16, p.diffBits k * ((2 ^ (k : ℕ) : ℕ) : BB)
  /-- SORTED_MEM_UNUSED_ZEROED (addr) -/
  unused_addr : (1 - p.used) * p.addr = 0
  /-- SORTED_MEM_UNUSED_ZEROED (val) -/
  unused_val : (1 - p.used) * p.val = 0

/-- **The transition constraint set** (Rust:
`eval_transition_constraints(curr, next)`), one named field per pushed
equation. -/
structure TransitionConstraints (c n : Row) : Prop where
  /-- CLK_INCREMENT -/
  clk_increment : n.clk - c.clk - 1 = 0
  /-- PC_CONTINUITY -/
  pc_continuity : (1 - c.halt) * (n.pc - c.nextPc) = 0
  /-- SEL_BOOLEAN -/
  sel_boolean : ∀ k : Fin 11, c.sel k * (c.sel k - 1) = 0
  /-- SEL_SUM_ONE -/
  sel_sum_one : (∑ k : Fin 11, c.sel k) - 1 = 0
  /-- OPCODE_RECON -/
  opcode_recon :
    c.opcode - ∑ k : Fin 11, c.sel k * (((k : ℕ) + 1 : ℕ) : BB) = 0
  /-- HALT_BOOLEAN -/
  halt_boolean : c.halt * (c.halt - 1) = 0
  /-- HALT_MONOTONE -/
  halt_monotone :
    n.halt - c.halt - n.sel oHALT + c.halt * n.sel oHALT = 0
  /-- POST_HALT_REPEATS_HALT -/
  post_halt : c.halt * (1 - c.sel oHALT) = 0
  /-- I/O cursors -/
  i_in_adv : n.iIn - c.iIn - c.sel oREAD = 0
  i_out_adv : n.iOut - c.iOut - c.sel oWRITE = 0
  /-- Register-slot well-formedness, three slots -/
  slotA_wf : SlotWf c.slotA
  slotB_wf : SlotWf c.slotB
  slotC_wf : SlotWf c.slotC
  /-- OPCODE_SLOT_ACTIVITY -/
  actA : c.slotA.act -
    (c.sAlu + c.sel oLOAD + c.sel oSTORE + c.sel oJZ + c.sel oWRITE) = 0
  actB : c.slotB.act - (c.sAlu + c.sel oSTORE) = 0
  actC : c.slotC.act -
    (c.sAlu + c.sel oIMM + c.sel oLOAD + c.sel oREAD) = 0
  /-- MEM_WIRING -/
  mem_used_wiring : c.memUsed - c.sel oLOAD - c.sel oSTORE = 0
  mem_wr_wiring : c.memWr - c.sel oSTORE = 0
  /-- MEM_UNUSED_ZEROED -/
  mem_unused_addr : (1 - c.memUsed) * c.memAddr = 0
  mem_unused_val : (1 - c.memUsed) * c.memVal = 0
  /-- JZ_ZERO_BOOLEAN / JZ_ZERO_KILL / JZ_NONZERO_INV -/
  jz_boolean : c.jzIsZero * (c.jzIsZero - 1) = 0
  jz_kill : c.jzIsZero * c.slotA.val = 0
  jz_inv : (1 - c.jzIsZero) - c.slotA.val * c.jzValInv = 0
  /-- arith_constraints -/
  alu_a_idx : c.sAlu * (c.slotA.idx - c.opB) = 0
  alu_b_idx : c.sAlu * (c.slotB.idx - c.opC) = 0
  alu_c_idx : c.sAlu * (c.slotC.idx - c.opA) = 0
  alu_a_read : c.sAlu * c.slotA.wr = 0
  alu_b_read : c.sAlu * c.slotB.wr = 0
  alu_c_write : c.sAlu * (c.slotC.wr - 1) = 0
  add_result : c.sel oADD * (c.slotC.val - c.slotA.val - c.slotB.val) = 0
  sub_result : c.sel oSUB * (c.slotC.val - c.slotA.val + c.slotB.val) = 0
  mul_result : c.sel oMUL * (c.slotC.val - c.slotA.val * c.slotB.val) = 0
  imm_c_idx : c.sel oIMM * (c.slotC.idx - c.opA) = 0
  imm_c_val : c.sel oIMM * (c.slotC.val - c.opB) = 0
  imm_c_write : c.sel oIMM * (c.slotC.wr - 1) = 0
  /-- jump_constraints -/
  default_next_pc :
    (1 - (c.sel oJMP + c.sel oJZ + c.sel oHALT)) * (c.nextPc - c.pc - 1) = 0
  jmp_next_pc : c.sel oJMP * (c.nextPc - c.opA) = 0
  halt_next_pc : c.sel oHALT * (c.nextPc - c.pc) = 0
  jz_a_idx : c.sel oJZ * (c.slotA.idx - c.opA) = 0
  jz_a_read : c.sel oJZ * c.slotA.wr = 0
  jz_taken : c.sel oJZ * c.jzIsZero * (c.nextPc - c.opB) = 0
  jz_not_taken : c.sel oJZ * (1 - c.jzIsZero) * (c.nextPc - c.pc - 1) = 0
  /-- memory_op_constraints -/
  load_a_idx : c.sel oLOAD * (c.slotA.idx - c.opB) = 0
  load_a_read : c.sel oLOAD * c.slotA.wr = 0
  load_addr : c.sel oLOAD * (c.memAddr - c.slotA.val) = 0
  load_c_idx : c.sel oLOAD * (c.slotC.idx - c.opA) = 0
  load_c_val : c.sel oLOAD * (c.slotC.val - c.memVal) = 0
  load_c_write : c.sel oLOAD * (c.slotC.wr - 1) = 0
  store_a_idx : c.sel oSTORE * (c.slotA.idx - c.opA) = 0
  store_a_read : c.sel oSTORE * c.slotA.wr = 0
  store_b_idx : c.sel oSTORE * (c.slotB.idx - c.opB) = 0
  store_b_read : c.sel oSTORE * c.slotB.wr = 0
  store_addr : c.sel oSTORE * (c.memAddr - c.slotA.val) = 0
  store_val : c.sel oSTORE * (c.memVal - c.slotB.val) = 0
  /-- io_constraints -/
  read_c_idx : c.sel oREAD * (c.slotC.idx - c.opA) = 0
  read_c_write : c.sel oREAD * (c.slotC.wr - 1) = 0
  write_a_idx : c.sel oWRITE * (c.slotA.idx - c.opA) = 0
  write_a_read : c.sel oWRITE * c.slotA.wr = 0
  /-- rom_constraints -/
  rom_real_boolean : c.rom.real * (c.rom.real - 1) = 0
  rom_real_prefix : n.rom.real * (1 - c.rom.real) = 0
  rom_addr_step : n.rom.real * (n.rom.addr - c.rom.addr - 1) = 0
  rom_mult_bits : ∀ k : Fin 16, c.rom.multBits k * (c.rom.multBits k - 1) = 0
  rom_mult_recon :
    c.rom.mult - ∑ k : Fin 16, c.rom.multBits k * ((2 ^ (k : ℕ) : ℕ) : BB) = 0
  /-- Sorted-table transitions (A→B, B→C within the row; C→A′, mem across) -/
  sreg_ab : SRegTrans c.sregA c.sregB
  sreg_bc : SRegTrans c.sregB c.sregC
  sreg_ca : SRegTrans c.sregC n.sregA
  smem_trans : SMemTrans c.smem n.smem

end Zkvm

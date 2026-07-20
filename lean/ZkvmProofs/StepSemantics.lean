/-
# Per-opcode step determinism

For every opcode `k`, the transition constraints pin the *entire* visible
behaviour of a row on which selector `k` fires: slot roles and indices as
functions of the instruction operands, result values as functions of the
read values, the next program counter, the memory lane, and the I/O
cursors. Together with the sorted-table arguments (which pin the read
values themselves, `SortedTable.lean`) and the ROM/tape lookups
(`Axioms.lean`), this is the "fully constrained" property: the prover has
no remaining freedom in any column of a satisfying row.

Each `*Spec` structure below is the row-level image of the corresponding
arm of `zkvm-core::run`; each theorem derives it from
`TransitionConstraints` alone.
-/
import ZkvmProofs.Constraints

namespace Zkvm

open Row

/-! ## Generic consequences of the constraint set -/

/-- Gated equation helper: a constraint `s·e = 0` with `s = 1` yields `e = 0`. -/
theorem gated {s e : BB} (hs : s = 1) (h : s * e = 0) : e = 0 := by
  rw [hs, one_mul] at h
  exact h

/-- The selector environment on a row where selector `k` fires: every other
selector is 0 (booleanity + sum-to-one + char > 11). -/
theorem sel_env {c n : Row} (tc : TransitionConstraints c n) {k : Fin 11}
    (hk : c.sel k = 1) : ∀ j, j ≠ k → c.sel j = 0 := by
  obtain ⟨k', hk', hothers⟩ :=
    exactly_one_selector tc.sel_boolean (by linear_combination tc.sel_sum_one)
  have hkk' : k = k' := by
    by_contra hne
    have := hothers k hne
    rw [hk] at this
    exact one_ne_zero this
  subst hkk'
  exact hothers

/-- Any slot: the r0 hardwiring — index 0 always carries value 0. -/
theorem slot_r0 {s : Slot} (wf : SlotWf s) (h : s.idx = 0) : s.val = 0 :=
  kill_gadget wf.r0_idx_inv wf.r0_val_zero h

/-- A fully-zeroed (inactive) slot. -/
def SlotZero (s : Slot) : Prop := s.act = 0 ∧ s.idx = 0 ∧ s.val = 0 ∧ s.wr = 0

/-- Any slot: inactive slots are fully zeroed. -/
theorem slot_inactive {s : Slot} (wf : SlotWf s) (h : s.act = 0) : SlotZero s := by
  refine ⟨h, ?_, ?_, ?_⟩
  · have hz := wf.inactive_idx
    rw [h] at hz
    simpa using hz
  · have hz := wf.inactive_val
    rw [h] at hz
    simpa using hz
  · have hz := wf.inactive_wr
    rw [h] at hz
    simpa using hz

/-- Bookkeeping shared by every row: I/O cursor advancement and the memory
wiring flags, in solved form. -/
structure CommonSpec (c n : Row) : Prop where
  i_in : n.iIn = c.iIn + c.sel oREAD
  i_out : n.iOut = c.iOut + c.sel oWRITE
  mem_used : c.memUsed = c.sel oLOAD + c.sel oSTORE
  mem_wr : c.memWr = c.sel oSTORE
  clk : n.clk = c.clk + 1

theorem common_spec {c n : Row} (tc : TransitionConstraints c n) :
    CommonSpec c n where
  i_in := by linear_combination tc.i_in_adv
  i_out := by linear_combination tc.i_out_adv
  mem_used := by linear_combination tc.mem_used_wiring
  mem_wr := by linear_combination tc.mem_wr_wiring
  clk := by linear_combination tc.clk_increment

/-- Rows whose opcode touches no memory carry a zeroed memory lane. -/
theorem mem_lane_zero {c n : Row} (tc : TransitionConstraints c n)
    (hload : c.sel oLOAD = 0) (hstore : c.sel oSTORE = 0) :
    c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0 := by
  have hused : c.memUsed = 0 := by linear_combination tc.mem_used_wiring + hload + hstore
  refine ⟨hused, ?_, ?_⟩
  · have hz := tc.mem_unused_addr
    rw [hused] at hz
    simpa using hz
  · have hz := tc.mem_unused_val
    rw [hused] at hz
    simpa using hz

/-- Straight-line control flow: no JMP/JZ/HALT firing ⇒ `next_pc = pc + 1`. -/
theorem default_pc {c n : Row} (tc : TransitionConstraints c n)
    (hjmp : c.sel oJMP = 0) (hjz : c.sel oJZ = 0) (hhalt : c.sel oHALT = 0) :
    c.nextPc = c.pc + 1 := by
  have hgate : (1 - (c.sel oJMP + c.sel oJZ + c.sel oHALT)) = 1 := by
    rw [hjmp, hjz, hhalt]; ring
  have := tc.default_next_pc
  rw [hgate, one_mul] at this
  linear_combination this

/-! ## ALU opcodes -/

/-- The visible state of an ALU row (`Add`/`Sub`/`Mul`), with the result
formula abstracted. Mirrors the ALU arm of `zkvm-core::run`. -/
structure AluSpec (c : Row) (opResult : BB → BB → BB) : Prop where
  a_idx : c.slotA.idx = c.opB
  b_idx : c.slotB.idx = c.opC
  c_idx : c.slotC.idx = c.opA
  a_read : c.slotA.wr = 0
  b_read : c.slotB.wr = 0
  c_write : c.slotC.wr = 1
  result : c.slotC.val = opResult c.slotA.val c.slotB.val
  next_pc : c.nextPc = c.pc + 1
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

/-- Everything but the result formula, shared by the three ALU opcodes. -/
theorem alu_frame {c n : Row} (tc : TransitionConstraints c n) {k : Fin 11}
    (hk : c.sel k = 1) (halu : c.sAlu = 1)
    (hload : c.sel oLOAD = 0) (hstore : c.sel oSTORE = 0)
    (hjmp : c.sel oJMP = 0) (hjz : c.sel oJZ = 0) (hhalt : c.sel oHALT = 0) :
    c.slotA.idx = c.opB ∧ c.slotB.idx = c.opC ∧ c.slotC.idx = c.opA ∧
    c.slotA.wr = 0 ∧ c.slotB.wr = 0 ∧ c.slotC.wr = 1 ∧
    c.nextPc = c.pc + 1 ∧
    (c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination gated halu tc.alu_a_idx
  · linear_combination gated halu tc.alu_b_idx
  · linear_combination gated halu tc.alu_c_idx
  · linear_combination gated halu tc.alu_a_read
  · linear_combination gated halu tc.alu_b_read
  · linear_combination gated halu tc.alu_c_write
  · exact default_pc tc hjmp hjz hhalt
  · exact mem_lane_zero tc hload hstore

private theorem alu_env {c n : Row} (tc : TransitionConstraints c n)
    {k : Fin 11} (hk : c.sel k = 1) (hkalu : k = oADD ∨ k = oSUB ∨ k = oMUL) :
    c.sAlu = 1 ∧ c.sel oLOAD = 0 ∧ c.sel oSTORE = 0 ∧
    c.sel oJMP = 0 ∧ c.sel oJZ = 0 ∧ c.sel oHALT = 0 := by
  have hothers := sel_env tc hk
  have hne : ∀ j : Fin 11, j ≠ k → c.sel j = 0 := hothers
  rcases hkalu with h | h | h <;> subst h <;>
  · refine ⟨?_, hne oLOAD (by decide), hne oSTORE (by decide),
      hne oJMP (by decide), hne oJZ (by decide), hne oHALT (by decide)⟩
    unfold Row.sAlu
    first
      | (rw [hk, hne oSUB (by decide), hne oMUL (by decide)]; ring)
      | (rw [hk, hne oADD (by decide), hne oMUL (by decide)]; ring)
      | (rw [hk, hne oADD (by decide), hne oSUB (by decide)]; ring)

/-- **ADD is fully constrained**: `slotC.val = slotA.val + slotB.val`, with
all wiring pinned. -/
theorem add_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oADD = 1) : AluSpec c (· + ·) := by
  obtain ⟨halu, hl, hs, hj, hz, hh⟩ := alu_env tc hk (Or.inl rfl)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := alu_frame tc hk halu hl hs hj hz hh
  exact ⟨h1, h2, h3, h4, h5, h6, by linear_combination gated hk tc.add_result,
    h7, h8⟩

/-- **SUB is fully constrained**: `slotC.val = slotA.val − slotB.val`. -/
theorem sub_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oSUB = 1) : AluSpec c (· - ·) := by
  obtain ⟨halu, hl, hs, hj, hz, hh⟩ := alu_env tc hk (Or.inr (Or.inl rfl))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := alu_frame tc hk halu hl hs hj hz hh
  exact ⟨h1, h2, h3, h4, h5, h6, by linear_combination gated hk tc.sub_result,
    h7, h8⟩

/-- **MUL is fully constrained**: `slotC.val = slotA.val · slotB.val`. -/
theorem mul_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oMUL = 1) : AluSpec c (· * ·) := by
  obtain ⟨halu, hl, hs, hj, hz, hh⟩ := alu_env tc hk (Or.inr (Or.inr rfl))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := alu_frame tc hk halu hl hs hj hz hh
  exact ⟨h1, h2, h3, h4, h5, h6, by linear_combination gated hk tc.mul_result,
    h7, h8⟩

/-! ## IMM -/

structure ImmSpec (c : Row) : Prop where
  c_idx : c.slotC.idx = c.opA
  c_val : c.slotC.val = c.opB
  c_write : c.slotC.wr = 1
  a_zero : SlotZero c.slotA
  b_zero : SlotZero c.slotB
  next_pc : c.nextPc = c.pc + 1
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

/-- **IMM is fully constrained**: writes the literal, everything else inert. -/
theorem imm_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oIMM = 1) : ImmSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactA : c.slotA.act = 0 := by
    linear_combination tc.actA + halu + hne oLOAD (by decide) +
      hne oSTORE (by decide) + hne oJZ (by decide) + hne oWRITE (by decide)
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  exact {
    c_idx := by linear_combination gated hk tc.imm_c_idx
    c_val := by linear_combination gated hk tc.imm_c_val
    c_write := by linear_combination gated hk tc.imm_c_write
    a_zero := slot_inactive tc.slotA_wf hactA
    b_zero := slot_inactive tc.slotB_wf hactB
    next_pc := default_pc tc (hne oJMP (by decide)) (hne oJZ (by decide))
      (hne oHALT (by decide))
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

/-! ## LOAD / STORE -/

structure LoadSpec (c : Row) : Prop where
  a_idx : c.slotA.idx = c.opB
  a_read : c.slotA.wr = 0
  addr : c.memAddr = c.slotA.val
  c_idx : c.slotC.idx = c.opA
  c_val : c.slotC.val = c.memVal
  c_write : c.slotC.wr = 1
  b_zero : SlotZero c.slotB
  mem_used : c.memUsed = 1
  mem_read : c.memWr = 0
  next_pc : c.nextPc = c.pc + 1

theorem load_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oLOAD = 1) : LoadSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  exact {
    a_idx := by linear_combination gated hk tc.load_a_idx
    a_read := by linear_combination gated hk tc.load_a_read
    addr := by linear_combination gated hk tc.load_addr
    c_idx := by linear_combination gated hk tc.load_c_idx
    c_val := by linear_combination gated hk tc.load_c_val
    c_write := by linear_combination gated hk tc.load_c_write
    b_zero := slot_inactive tc.slotB_wf hactB
    mem_used := by
      linear_combination tc.mem_used_wiring + hk + hne oSTORE (by decide)
    mem_read := by linear_combination tc.mem_wr_wiring + hne oSTORE (by decide)
    next_pc := default_pc tc (hne oJMP (by decide)) (hne oJZ (by decide))
      (hne oHALT (by decide)) }

structure StoreSpec (c : Row) : Prop where
  a_idx : c.slotA.idx = c.opA
  a_read : c.slotA.wr = 0
  b_idx : c.slotB.idx = c.opB
  b_read : c.slotB.wr = 0
  addr : c.memAddr = c.slotA.val
  val : c.memVal = c.slotB.val
  c_zero : SlotZero c.slotC
  mem_used : c.memUsed = 1
  mem_write : c.memWr = 1
  next_pc : c.nextPc = c.pc + 1

theorem store_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oSTORE = 1) : StoreSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactC : c.slotC.act = 0 := by
    linear_combination tc.actC + halu + hne oIMM (by decide) +
      hne oLOAD (by decide) + hne oREAD (by decide)
  exact {
    a_idx := by linear_combination gated hk tc.store_a_idx
    a_read := by linear_combination gated hk tc.store_a_read
    b_idx := by linear_combination gated hk tc.store_b_idx
    b_read := by linear_combination gated hk tc.store_b_read
    addr := by linear_combination gated hk tc.store_addr
    val := by linear_combination gated hk tc.store_val
    c_zero := slot_inactive tc.slotC_wf hactC
    mem_used := by
      linear_combination tc.mem_used_wiring + hne oLOAD (by decide) + hk
    mem_write := by linear_combination tc.mem_wr_wiring + hk
    next_pc := default_pc tc (hne oJMP (by decide)) (hne oJZ (by decide))
      (hne oHALT (by decide)) }

/-! ## Control flow: JMP / JZ / HALT -/

structure JmpSpec (c : Row) : Prop where
  next_pc : c.nextPc = c.opA
  a_zero : SlotZero c.slotA
  b_zero : SlotZero c.slotB
  c_zero : SlotZero c.slotC
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

theorem jmp_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oJMP = 1) : JmpSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactA : c.slotA.act = 0 := by
    linear_combination tc.actA + halu + hne oLOAD (by decide) +
      hne oSTORE (by decide) + hne oJZ (by decide) + hne oWRITE (by decide)
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  have hactC : c.slotC.act = 0 := by
    linear_combination tc.actC + halu + hne oIMM (by decide) +
      hne oLOAD (by decide) + hne oREAD (by decide)
  exact {
    next_pc := by linear_combination gated hk tc.jmp_next_pc
    a_zero := slot_inactive tc.slotA_wf hactA
    b_zero := slot_inactive tc.slotB_wf hactB
    c_zero := slot_inactive tc.slotC_wf hactC
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

/-- JZ: the branch is decided *exactly* by whether the read value is zero —
the helper flag has no freedom (`iszero_gadget`). -/
structure JzSpec (c : Row) : Prop where
  a_idx : c.slotA.idx = c.opA
  a_read : c.slotA.wr = 0
  taken : c.slotA.val = 0 → c.nextPc = c.opB
  not_taken : c.slotA.val ≠ 0 → c.nextPc = c.pc + 1
  b_zero : SlotZero c.slotB
  c_zero : SlotZero c.slotC
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

theorem jz_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oJZ = 1) : JzSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  have hactC : c.slotC.act = 0 := by
    linear_combination tc.actC + halu + hne oIMM (by decide) +
      hne oLOAD (by decide) + hne oREAD (by decide)
  have hflag := iszero_gadget tc.jz_boolean tc.jz_kill tc.jz_inv
  exact {
    a_idx := by linear_combination gated hk tc.jz_a_idx
    a_read := by linear_combination gated hk tc.jz_a_read
    taken := by
      intro hv
      rcases hflag with ⟨hz, _⟩ | ⟨_, hvne⟩
      · have := tc.jz_taken
        rw [hk, hz, one_mul, one_mul] at this
        linear_combination this
      · exact absurd hv hvne
    not_taken := by
      intro hv
      rcases hflag with ⟨_, hv0⟩ | ⟨hz, _⟩
      · exact absurd hv0 hv
      · have := tc.jz_not_taken
        rw [hk, hz, one_mul] at this
        simp only [sub_zero, one_mul] at this
        linear_combination this
    b_zero := slot_inactive tc.slotB_wf hactB
    c_zero := slot_inactive tc.slotC_wf hactC
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

structure HaltSpec (c : Row) : Prop where
  next_pc : c.nextPc = c.pc
  a_zero : SlotZero c.slotA
  b_zero : SlotZero c.slotB
  c_zero : SlotZero c.slotC
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

theorem halt_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oHALT = 1) : HaltSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactA : c.slotA.act = 0 := by
    linear_combination tc.actA + halu + hne oLOAD (by decide) +
      hne oSTORE (by decide) + hne oJZ (by decide) + hne oWRITE (by decide)
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  have hactC : c.slotC.act = 0 := by
    linear_combination tc.actC + halu + hne oIMM (by decide) +
      hne oLOAD (by decide) + hne oREAD (by decide)
  exact {
    next_pc := by linear_combination gated hk tc.halt_next_pc
    a_zero := slot_inactive tc.slotA_wf hactA
    b_zero := slot_inactive tc.slotB_wf hactB
    c_zero := slot_inactive tc.slotC_wf hactC
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

/-! ## I/O: READ / WRITE -/

structure ReadSpec (c : Row) : Prop where
  c_idx : c.slotC.idx = c.opA
  c_write : c.slotC.wr = 1
  a_zero : SlotZero c.slotA
  b_zero : SlotZero c.slotB
  next_pc : c.nextPc = c.pc + 1
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

theorem read_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oREAD = 1) : ReadSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactA : c.slotA.act = 0 := by
    linear_combination tc.actA + halu + hne oLOAD (by decide) +
      hne oSTORE (by decide) + hne oJZ (by decide) + hne oWRITE (by decide)
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  exact {
    c_idx := by linear_combination gated hk tc.read_c_idx
    c_write := by linear_combination gated hk tc.read_c_write
    a_zero := slot_inactive tc.slotA_wf hactA
    b_zero := slot_inactive tc.slotB_wf hactB
    next_pc := default_pc tc (hne oJMP (by decide)) (hne oJZ (by decide))
      (hne oHALT (by decide))
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

structure WriteSpec (c : Row) : Prop where
  a_idx : c.slotA.idx = c.opA
  a_read : c.slotA.wr = 0
  b_zero : SlotZero c.slotB
  c_zero : SlotZero c.slotC
  next_pc : c.nextPc = c.pc + 1
  mem_zero : c.memUsed = 0 ∧ c.memAddr = 0 ∧ c.memVal = 0

theorem write_spec {c n : Row} (tc : TransitionConstraints c n)
    (hk : c.sel oWRITE = 1) : WriteSpec c := by
  have hne := sel_env tc hk
  have halu : c.sAlu = 0 := by
    unfold Row.sAlu
    rw [hne oADD (by decide), hne oSUB (by decide), hne oMUL (by decide)]
    ring
  have hactB : c.slotB.act = 0 := by
    linear_combination tc.actB + halu + hne oSTORE (by decide)
  have hactC : c.slotC.act = 0 := by
    linear_combination tc.actC + halu + hne oIMM (by decide) +
      hne oLOAD (by decide) + hne oREAD (by decide)
  exact {
    a_idx := by linear_combination gated hk tc.write_a_idx
    a_read := by linear_combination gated hk tc.write_a_read
    b_zero := slot_inactive tc.slotB_wf hactB
    c_zero := slot_inactive tc.slotC_wf hactC
    next_pc := default_pc tc (hne oJMP (by decide)) (hne oJZ (by decide))
      (hne oHALT (by decide))
    mem_zero := mem_lane_zero tc (hne oLOAD (by decide)) (hne oSTORE (by decide)) }

/-! ## The dispatcher: every satisfying row obeys its opcode's spec -/

/-- The row-level ISA: what the constraints must imply for each opcode. -/
inductive RowSpec (c n : Row) : Prop
  | add (h : AluSpec c (· + ·))
  | sub (h : AluSpec c (· - ·))
  | mul (h : AluSpec c (· * ·))
  | imm (h : ImmSpec c)
  | load (h : LoadSpec c)
  | store (h : StoreSpec c)
  | jmp (h : JmpSpec c)
  | jz (h : JzSpec c)
  | read (h : ReadSpec c)
  | write (h : WriteSpec c)
  | halt (h : HaltSpec c)

/-- **Row soundness**: on any pair of rows satisfying the transition
constraints, exactly one opcode selector fires, and the row obeys that
opcode's full ISA specification. The prover has no per-row freedom beyond
choosing the (ROM-bound) instruction and the (table-bound) read values. -/
theorem row_soundness {c n : Row} (tc : TransitionConstraints c n) :
    RowSpec c n := by
  obtain ⟨k, hk, _⟩ :=
    exactly_one_selector tc.sel_boolean (by linear_combination tc.sel_sum_one)
  fin_cases k
  · exact .add (add_spec tc hk)
  · exact .sub (sub_spec tc hk)
  · exact .mul (mul_spec tc hk)
  · exact .imm (imm_spec tc hk)
  · exact .load (load_spec tc hk)
  · exact .store (store_spec tc hk)
  · exact .jmp (jmp_spec tc hk)
  · exact .jz (jz_spec tc hk)
  · exact .read (read_spec tc hk)
  · exact .write (write_spec tc hk)
  · exact .halt (halt_spec tc hk)

end Zkvm

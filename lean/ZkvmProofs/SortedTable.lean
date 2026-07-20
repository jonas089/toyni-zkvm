/-
# The sorted-table argument: register-file / RAM semantics

The zkvm proves memory and register consistency by committing a *sorted*
copy of all accesses (sorted by key, then access time) and constraining
adjacent sorted entries. This file proves that those local constraints
force global RAM semantics — **every read returns the most recent write to
its key, or 0 if the key was never written**:

1. `bits_bound` — the range-checked difference `1 + Σ bitₖ·2^k` is the
   image of a natural number in `[1, 2^16]`;
2. `flag_correct` — the committed `same_idx` flag *equals* the predicate
   "adjacent keys are equal" (it cannot lie in either direction);
3. `sreg_step_fact` — each `SRegTrans` pack therefore yields the semantic
   step fact: keys either repeat or grow by a range-checked amount, reads
   propagate the previous value within a run, and fresh-key reads see 0;
4. `table_semantics` — by induction along the chain: **under the global
   no-wraparound bound** (total key growth `< p`), every read equals the
   fold of all preceding writes.

The no-wraparound bound is essential, not cosmetic: with enough sorted
entries taking maximal range-checked jumps, key values could wrap the
31-bit modulus and one key could recur in two separated runs, breaking
read-after-write. The builder's parameter choice `2^16 > 3·trace_len`
keeps the total below `p ≈ 2^31` (`≤ 21845·65536 ≈ 1.43·10^9 <
2.01·10^9`), and the hypothesis makes that arithmetic explicit.
-/
import ZkvmProofs.StepSemantics

namespace Zkvm

/-! ## From constraint packs to semantic step facts -/

set_option maxHeartbeats 800000 in
/-- The range-checked reconstruction `1 + Σ bitₖ·2^k` with boolean bits is
the cast of a natural in `[1, 2^16]`. -/
theorem bits_bound {bits : Fin 16 → BB}
    (hbool : ∀ k, bits k * (bits k - 1) = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 65536 ∧
      (1 + ∑ k : Fin 16, bits k * ((2 ^ (k : ℕ) : ℕ) : BB)) = (m : BB) := by
  classical
  set b : Fin 16 → ℕ := fun k => if bits k = 1 then 1 else 0 with hb
  have hble : ∀ k, b k ≤ 1 := by
    intro k
    by_cases h : bits k = 1 <;> simp [hb, h]
  have hcast : ∀ k, bits k = ((b k : ℕ) : BB) := by
    intro k
    rcases boolean_cases (hbool k) with h | h
    · have hne : bits k ≠ 1 := by
        rw [h]
        exact zero_ne_one
      simp [hb, hne, h]
    · simp [hb, h]
  refine ⟨1 + ∑ k : Fin 16, b k * 2 ^ (k : ℕ), Nat.le_add_right 1 _, ?_, ?_⟩
  · have hsum : ∑ k : Fin 16, b k * 2 ^ (k : ℕ) ≤ ∑ k : Fin 16, 2 ^ (k : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      calc b k * 2 ^ (k : ℕ) ≤ 1 * 2 ^ (k : ℕ) :=
            Nat.mul_le_mul_right _ (hble k)
        _ = 2 ^ (k : ℕ) := one_mul _
    have hgeo : ∑ k : Fin 16, 2 ^ (k : ℕ) = 65535 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) 16]
      simp [Finset.sum_range_succ]
    omega
  · have hsummand : ∀ k : Fin 16,
        bits k * ((2 ^ (k : ℕ) : ℕ) : BB) = ((b k * 2 ^ (k : ℕ) : ℕ) : BB) := by
      intro k
      rw [hcast k]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun k _ => hsummand k)]
    push_cast
    ring

/-- The committed same-key flag cannot lie: it is 1 exactly when the
adjacent keys coincide. -/
theorem flag_correct {flag dinv a b : BB}
    (hbool : flag * (flag - 1) = 0)
    (hmatch : flag * (b - a) = 0)
    (hdiff : (1 - flag) * (1 - (b - a) * dinv) = 0) :
    (flag = 1 ∧ a = b) ∨ (flag = 0 ∧ a ≠ b) := by
  rcases boolean_cases hbool with h0 | h1
  · right
    refine ⟨h0, ?_⟩
    intro hab
    rw [h0, ← hab] at hdiff
    simp at hdiff
  · left
    refine ⟨h1, ?_⟩
    have h := gated h1 hmatch
    linear_combination -h

/-- An abstract sorted-table entry. -/
structure Entry where
  key : BB
  val : BB
  wr : BB

/-- The semantic content of one sorted transition, extracted from the
constraint pack. `wr`-booleanity of the *next* entry is a hypothesis here;
in the AIR it is transferred from the main trace by the multiset argument
(sorted tuples are a permutation of main-side tuples, whose `wr` is
boolean by `SLOT_WR_BOOLEAN` / `MEM_WIRING`). -/
structure StepFact (p q : Entry) : Prop where
  /-- Keys repeat or grow by a range-checked amount `m ∈ [1, 2^16]`. -/
  key_step : p.key = q.key ∨
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 65536 ∧ q.key = p.key + (m : BB)
  /-- Read-after-write within a run. -/
  raw : p.key = q.key → q.wr = 0 → q.val = p.val
  /-- A fresh key starts at 0. -/
  init : p.key ≠ q.key → q.wr = 0 → q.val = 0

/-- Every `SRegTrans` pack yields the semantic step fact. -/
theorem sreg_step_fact {p q : SEntry} (t : SRegTrans p q) :
    StepFact ⟨p.idx, p.val, p.wr⟩ ⟨q.idx, q.val, q.wr⟩ := by
  have hflag := flag_correct t.same_boolean t.same_match t.diff_key_inv
  constructor
  · -- key_step
    rcases hflag with ⟨hf, hab⟩ | ⟨hf, _⟩
    · exact Or.inl hab
    · obtain ⟨m, hm1, hm2, hmv⟩ := bits_bound t.bits_boolean
      refine Or.inr ⟨m, hm1, hm2, ?_⟩
      have hd := t.strict_diff
      rw [hf] at hd
      simp only [zero_mul, sub_zero, one_mul, zero_add] at hd
      rw [hmv] at hd
      dsimp only
      linear_combination hd
  · -- raw
    intro hkey hread
    dsimp only at hkey hread ⊢
    rcases hflag with ⟨hf, _⟩ | ⟨_, hab⟩
    · have h := t.raw
      rw [hf, hread] at h
      simp only [one_mul, sub_zero] at h
      linear_combination h
    · exact absurd hkey hab
  · -- init
    intro hkey hread
    dsimp only at hkey hread ⊢
    rcases hflag with ⟨_, hab⟩ | ⟨hf, _⟩
    · exact absurd hab hkey
    · have h := t.init
      rw [hf, hread] at h
      simp only [sub_zero, one_mul] at h
      linear_combination h

/-! ## Global table semantics by induction along the chain -/

/-- The RAM/register-file fold: the key→value map after processing a list
of accesses (writes update, reads don't). -/
noncomputable def stateAfter (es : List Entry) : BB → BB :=
  es.foldl (fun m e k => if k = e.key ∧ e.wr = 1 then e.val else m k)
    (fun _ => 0)

@[simp] theorem stateAfter_nil (k : BB) : stateAfter [] k = 0 := rfl

theorem stateAfter_append (es : List Entry) (e : Entry) (k : BB) :
    stateAfter (es ++ [e]) k =
      if k = e.key ∧ e.wr = 1 then e.val else stateAfter es k := by
  unfold stateAfter
  rw [List.foldl_append]
  rfl

/-- The chain invariant: after processing a prefix ending in entry `l`,
the map at `l.key` carries `l.val`, and the map is still 0 at every key
strictly beyond `l.key` in the (wraparound-free) natural order. -/
structure Inv (pre : List Entry) (l : Entry) : Prop where
  carried : stateAfter pre l.key = l.val
  future : ∀ k : BB, l.key.val < k.val → stateAfter pre k = 0

/-- **Sorted-table semantics.** Along a chain of step facts whose total key
growth cannot wrap the modulus, every read entry's value is the RAM fold
of all entries before it. -/
theorem table_semantics :
    ∀ (es pre : List Entry) (l : Entry),
      List.Chain StepFact l es →
      Inv (pre ++ [l]) l →
      (∀ e ∈ es, e.wr = 0 ∨ e.wr = 1) →
      l.key.val + 65536 * es.length < bbP →
      ∀ (mid : List Entry) (e : Entry) (post : List Entry),
        es = mid ++ e :: post → e.wr = 0 →
        e.val = stateAfter (pre ++ [l] ++ mid) e.key := by
  intro es
  induction es with
  | nil =>
    intro pre l _ _ _ _ mid e post heq
    exact absurd heq (by simp)
  | cons e' rest ih =>
    intro pre l hchain hinv hwr hbound mid e post heq hread
    have hstep : StepFact l e' := (List.chain_cons.mp hchain).1
    have hchain' : List.Chain StepFact e' rest := (List.chain_cons.mp hchain).2
    have he'wr : e'.wr = 0 ∨ e'.wr = 1 := hwr e' (by simp)
    -- Key ordering facts for the step l → e'.
    have hkey_facts : e'.key = l.key ∨
        (l.key.val < e'.key.val ∧ e'.key.val ≤ l.key.val + 65536) := by
      rcases hstep.key_step with h | ⟨m, hm1, hm2, hmv⟩
      · exact Or.inl h.symm
      · right
        have hlen : (1 : ℕ) ≤ (e' :: rest).length := by simp
        have hlt : l.key.val + m < bbP := by
          simp only [List.length_cons] at hbound
          have : 65536 * (rest.length + 1) = 65536 * rest.length + 65536 := by
            ring
          omega
        have hval : e'.key.val = l.key.val + m := by
          rw [hmv, ZMod.val_add, ZMod.val_natCast,
            Nat.mod_eq_of_lt (by omega : m < bbP), Nat.mod_eq_of_lt hlt]
        omega
    -- The invariant after processing e'.
    have hnewinv : Inv ((pre ++ [l]) ++ [e']) e' := by
      constructor
      · rcases he'wr with hr | hw
        · -- e' is a read: forced to the carried/init value.
          rw [stateAfter_append, if_neg (by rintro ⟨_, h1⟩; rw [hr] at h1; exact zero_ne_one h1)]
          rcases hkey_facts with hk | ⟨hk, _⟩
          · rw [hk, hinv.carried]
            exact (hstep.raw hk.symm hr).symm
          · have hne : l.key ≠ e'.key := by
              intro h
              rw [h] at hk
              omega
            rw [hinv.future e'.key hk]
            exact (hstep.init hne hr).symm
        · rw [stateAfter_append, if_pos ⟨rfl, hw⟩]
      · intro k hk
        rw [stateAfter_append, if_neg ?_]
        · apply hinv.future
          rcases hkey_facts with hkeq | ⟨hklt, _⟩
          · rw [← hkeq]
            exact hk
          · omega
        · rintro ⟨hkk, _⟩
          rw [hkk] at hk
          omega
    -- Split on where the queried entry sits.
    cases mid with
    | nil =>
      -- e = e' (the head).
      have he : e' = e := by
        have := heq
        simp only [List.nil_append, List.cons.injEq] at this
        exact this.1
      subst he
      simp only [List.append_nil]
      rcases hkey_facts with hk | ⟨hk, _⟩
      · rw [hk, hinv.carried]
        exact hstep.raw hk.symm hread
      · have hne : l.key ≠ e'.key := by
          intro h
          rw [h] at hk
          omega
        rw [hinv.future e'.key hk]
        exact hstep.init hne hread
    | cons m0 mid' =>
      -- e sits deeper: recurse with the extended prefix.
      have hpair : e' = m0 ∧ rest = mid' ++ e :: post := by
        have h := heq
        simp only [List.cons_append, List.cons.injEq] at h
        exact ⟨h.1, h.2⟩
      have hrest : rest = mid' ++ e :: post := hpair.2
      have hbound' : e'.key.val + 65536 * rest.length < bbP := by
        simp only [List.length_cons] at hbound
        have hexp : 65536 * (rest.length + 1) = 65536 * rest.length + 65536 := by
          ring
        rcases hkey_facts with hk | ⟨_, hk2⟩
        · rw [hk]
          omega
        · omega
      have hrec := ih (pre ++ [l]) e' hchain' hnewinv
        (fun x hx => hwr x (by simp [hx])) hbound' mid' e post hrest hread
      have happ : pre ++ [l] ++ [e'] ++ mid' = pre ++ [l] ++ (m0 :: mid') := by
        rw [← hpair.1]
        simp [List.append_assoc]
      rw [← happ]
      exact hrec

end Zkvm

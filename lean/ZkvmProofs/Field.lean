/-
# The BabyBear field and the algebraic gadgets of the zkvm AIR

The zkvm trace is over BabyBear `p = 2^31 − 2^27 + 1 = 2013265921`
(constraints are *evaluated* over its quartic extension, but every committed
trace value is a base-field element and every constraint has base-field
coefficients, so constraint satisfaction over the extension of a base-valued
row is equivalent to satisfaction over the base field — we model rows as
BabyBear-valued).

This file proves the three reusable gadget lemmas the AIR leans on
everywhere:

* **`inv_gadget`** — from `x·(1 − x·xinv) = 0` conclude `x = 0 ∨ x·xinv = 1`:
  the committed-inverse pattern (`R0_IDX_INV`, `SORTED_DIFF_KEY_INV`, …);
* **`kill_gadget`** — from the pair `x·(1 − x·xinv) = 0` and
  `(1 − x·xinv)·y = 0` conclude `x = 0 → y = 0` **and** that the "flag"
  `x·xinv` is exactly the indicator of `x ≠ 0` (`R0_VAL_ZERO`,
  `SORTED_R0_PIN`, init-binding);
* **`iszero_gadget`** — the three-constraint is-zero pattern
  (`JZ_ZERO_BOOLEAN`, `JZ_ZERO_KILL`, `JZ_NONZERO_INV`) pins the flag to be
  *exactly* `(val = 0)` — the prover has no freedom;
* **`boolean_cases`** — `b·(b−1) = 0 → b = 0 ∨ b = 1`;
* **`exactly_one_selector`** — 11 boolean selectors summing to 1 have
  exactly one selector equal to 1 (this needs the characteristic to exceed
  11, which we get from `p` being a 31-bit prime; over `𝔽₂` three ones also
  sum to one, so this is *not* field-generic!).
-/
import Mathlib

namespace Zkvm

/-- The BabyBear prime `2^31 − 2^27 + 1`. -/
def bbP : ℕ := 2013265921

theorem bbP_prime : Nat.Prime bbP := by unfold bbP; norm_num

instance : Fact (Nat.Prime bbP) := ⟨bbP_prime⟩

/-- The BabyBear field. -/
abbrev BB := ZMod bbP

noncomputable instance : Field BB := ZMod.instField bbP

/-- Natural numbers below `p` embed injectively — the bridge between field
equations and integer semantics (used by the range-check lemmas). -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < bbP) (hb : b < bbP)
    (h : (a : BB) = (b : BB)) : a = b := by
  have := (ZMod.natCast_eq_natCast_iff' a b bbP).mp h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-! ## Gadget lemmas -/

/-- `b·(b − 1) = 0` forces booleanity. -/
theorem boolean_cases {F : Type*} [Field F] {b : F} (h : b * (b - 1) = 0) :
    b = 0 ∨ b = 1 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linear_combination h')

/-- The committed-inverse gadget: `x·(1 − x·xinv) = 0` means `x` is zero or
`xinv` is a genuine inverse. -/
theorem inv_gadget {F : Type*} [Field F] {x xinv : F}
    (h : x * (1 - x * xinv) = 0) : x = 0 ∨ x * xinv = 1 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linear_combination -h')

/-- The kill gadget (`R0_VAL_ZERO` pattern): together with the inverse
gadget, `(1 − x·xinv)·y = 0` forces `y = 0` whenever `x = 0`. -/
theorem kill_gadget {F : Type*} [Field F] {x xinv y : F}
    (hinv : x * (1 - x * xinv) = 0) (hkill : (1 - x * xinv) * y = 0)
    (hx : x = 0) : y = 0 := by
  subst hx
  simpa using hkill

/-- The is-zero gadget (`JZ_*`): boolean flag `z`, `z·v = 0`, and
`(1 − z) = v·vinv` pin `z = 1 ↔ v = 0`. No prover freedom remains. -/
theorem iszero_gadget {F : Type*} [Field F] {z vinv v : F}
    (hbool : z * (z - 1) = 0) (hkill : z * v = 0)
    (hinv : (1 - z) - v * vinv = 0) :
    (z = 1 ∧ v = 0) ∨ (z = 0 ∧ v ≠ 0) := by
  rcases boolean_cases hbool with hz | hz
  · right
    refine ⟨hz, ?_⟩
    intro hv
    rw [hz, hv] at hinv
    simp at hinv
  · left
    refine ⟨hz, ?_⟩
    rw [hz] at hkill
    simpa using hkill

/-- **Exactly one selector fires.** Eleven boolean columns summing to 1
contain exactly one 1. Uses `char BB > 11`: over `𝔽₂` (or `𝔽₃`, …) three
ones also sum to one, so a small-characteristic field would *not* make the
one-hot encoding sound — this lemma is where the field size genuinely
enters the per-row argument. -/
theorem exactly_one_selector {s : Fin 11 → BB}
    (hbool : ∀ i, s i * (s i - 1) = 0) (hsum : ∑ i, s i = 1) :
    ∃ k, s k = 1 ∧ ∀ j, j ≠ k → s j = 0 := by
  classical
  have hcases : ∀ i, s i = 0 ∨ s i = 1 := fun i => boolean_cases (hbool i)
  set T := Finset.univ.filter (fun i => s i = 1) with hT
  have hsum' : ∑ i, s i = (T.card : BB) := by
    rw [hT, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rcases hcases i with h | h <;> simp [h]
  have hcard : ((T.card : ℕ) : BB) = ((1 : ℕ) : BB) := by
    rw [← hsum']
    simpa using hsum
  have hcard1 : T.card = 1 := by
    refine natCast_inj_of_lt ?_ ?_ hcard
    · have h11 : T.card ≤ 11 := by
        have := Finset.card_filter_le Finset.univ (fun i => s i = 1)
        simpa using this
      unfold bbP
      omega
    · unfold bbP
      omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨k, ?_, ?_⟩
  · have hmem : k ∈ T := by
      rw [hk]
      exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hmem).2
  · intro j hj
    rcases hcases j with h | h
    · exact h
    · exfalso
      have hmem : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
      rw [hk, Finset.mem_singleton] at hmem
      exact hj hmem

end Zkvm

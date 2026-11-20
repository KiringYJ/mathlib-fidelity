/-
Tests for norm_cast
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Ring

-- set_option trace.Tactic.norm_cast true
-- set_option trace.Meta.Tactic.simp true
set_option autoImplicit true
set_option linter.unusedVariables false

variable (an bn cn dn : ℕ) (az bz cz dz : ℤ)
variable (aq bq cq dq : ℚ)
variable (ar br cr dr : ℝ) (ac bc cc dc : ℂ)

example : (an : ℤ) = bn → an = bn := by intro h; exact mod_cast h
example : an = bn → (an : ℤ) = bn := by intro h; exact mod_cast h
example : az = bz ↔ (az : ℚ) = bz := by norm_cast

example : (aq : ℝ) = br ↔ (aq : ℂ) = br := by norm_cast
example : (an : ℚ) = bz ↔ (an : ℂ) = bz := by norm_cast
example : (((an : ℤ) : ℚ) : ℝ) = bq ↔ ((an : ℚ) : ℂ) = (bq : ℝ) := by norm_cast

example : (an : ℤ) < bn ↔ an < bn := by norm_cast
example : (an : ℚ) < bz ↔ (an : ℝ) < bz := by norm_cast
example : ((an : ℤ) : ℝ) < bq ↔ (an : ℚ) < bq := by norm_cast
example : (an : ℤ) ≠ (bn : ℤ) ↔ an ≠ bn := by norm_cast

-- zero and one cause special problems
example : 0 < (bq : ℝ) ↔ 0 < bq := by norm_cast
example : az > (1 : ℕ) ↔ az > 1 := by norm_cast
example : az > (0 : ℕ) ↔ az > 0 := by norm_cast
example : (an : ℤ) ≠ 0 ↔ an ≠ 0 := by norm_cast
example : aq < (1 : ℕ) ↔ (aq : ℚ) < (1 : ℤ) := by norm_cast
example : aq < (1 : ℕ) ↔ (aq : ℝ) < (1 : ℤ) := by norm_cast

example : (an : ℤ) + bn = (an + bn : ℕ) := by norm_cast
example : (an : ℂ) + bq = ((an + bq) : ℚ) := by norm_cast
example : (((an : ℤ) : ℚ) : ℝ) + bn = (an + (bn : ℤ)) := by norm_cast

example (h : ((an + bn : ℕ) : ℤ) = (an : ℤ) + (bn : ℤ)) : True := by
  push_cast at h
  guard_hyp h : (an : ℤ) + (bn : ℤ) = (an : ℤ) + (bn : ℤ)
  trivial

example (h : ((an * bn : ℕ) : ℤ) = (an : ℤ) * (bn : ℤ)) : True := by
  push_cast at h
  guard_hyp h : (an : ℤ) * (bn : ℤ) = (an : ℤ) * (bn : ℤ)
  trivial

example : (((((an : ℚ) : ℝ) * bq) + (cq : ℝ) ^ dn) : ℂ) = (an : ℂ) * (bq : ℝ) + cq ^ dn := by
  norm_cast
example : ((an : ℤ) : ℝ) < bq ∧ (cr : ℂ) ^ 2 = dz ↔ (an : ℚ) < bq ∧ ((cr ^ 2) : ℂ) = dz := by
  norm_cast

--testing numerals
example : ((42 : ℕ) : ℤ) = 42 := by norm_cast
example : ((42 : ℕ) : ℂ) = 42 := by norm_cast
example : ((42 : ℤ) : ℚ) = 42 := by norm_cast
example : ((42 : ℚ) : ℝ) = 42 := by norm_cast

structure p (n : ℤ)
example : p 42 := by
  norm_cast
  guard_target = p 42
  exact ⟨⟩

example (h : (an : ℝ) = 0) : an = 0 := mod_cast h
example (h : (an : ℝ) = 42) : an = 42 := mod_cast h
example (h : (an + 42) ≠ 42) : (an : ℝ) + 42 ≠ 42 := mod_cast h

example (n : ℤ) (h : n + 1 > 0) : ((n + 1 : ℤ) : ℚ) > 0 := mod_cast h

-- testing the heuristic
example (h : bn ≤ an) : an - bn = 1 ↔ (an - bn : ℤ) = 1 := by norm_cast
example (hb : bz ≠ 0)
    (h : (cz : ℚ) = Checked.div (az : ℚ) (bz : ℚ) (Int.cast_ne_zero.mpr hb).isUnit) :
    (cz : ℝ) = Checked.div (az : ℝ) (bz : ℝ) (Int.cast_ne_zero.mpr hb).isUnit := by
  have hc : ((cz : ℚ) : ℝ) = ((az : ℚ) / (bz : ℚ) : ℚ) := by
    assumption_mod_cast
  simpa only [Rat.cast_intCast, Rat.cast_div] using hc

namespace hidden

def WithZero (α) := Option α

@[coe]
def WithZero.of (a : α) : WithZero α := some a

instance : CoeTail α (WithZero α) := ⟨WithZero.of⟩

instance : Zero (WithZero α) := ⟨none⟩

instance [One α] : One (WithZero α) := ⟨some 1⟩

instance [Mul α] : MulZeroClass (WithZero α) where
  mul o₁ o₂ := o₁.bind fun a => o₂.map fun b => a * b
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl

@[norm_cast] lemma coe_one [One α] : ((1 : α) : WithZero α) = 1 := rfl

@[norm_cast] lemma coe_inj {a b : α} : (a : WithZero α) = b ↔ a = b :=
  Option.some_inj

@[norm_cast] lemma mul_coe [Mul α] (a b : α) :
  ((a * b : α) : WithZero α) = (a : WithZero α) * b := rfl

example [Mul α] [One α] (x y : α) (h : (x : WithZero α) * y = 1) : x * y = 1 := mod_cast h

end hidden

example (k : ℕ) {x y : ℕ} :
    (x * x + y * y : ℤ) - ↑((x * y + 1) * k) = ↑y * ↑y - ↑k * ↑x * ↑y + (↑x * ↑x - ↑k) := by
  push_cast
  ring

example (k : ℕ) {x y : ℕ} (h : ((x + y + k : ℕ) : ℤ) = 0) : x + y + k = 0 := by
  push_cast at h
  guard_hyp h : (x : ℤ) + y + k = 0
  assumption_mod_cast

example (a b : ℕ) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
    ((a + b : ℕ) : ℤ) = 10 := by
  push_cast
  push_cast [Int.add_zero] at h2
  exact h2

-- example {x : ℚ} : ((x + 42 : ℚ) : ℝ) = x + 42 := by push_cast

namespace ENNReal
lemma half_lt_self_bis {a : ℝ≥0∞} (hz : a ≠ 0) (ht : a ≠ ⊤) : a / 2 < a := by
  lift a to NNReal using ht
  norm_cast at hz
  calc
    (a : ℝ≥0∞) / 2 = ↑(a / (2 : NNReal)) := ENNReal.coe_div.symm
    _ < (a : ℝ≥0∞) := coe_lt_coe.mpr (NNReal.half_lt_self hz)

example (x : NNReal) : (x : ENNReal) / 3 = ↑(x / 3) := by
  have h₃ : IsUnit (3 : NNReal) := (by norm_num : (3 : NNReal) ≠ 0).isUnit
  exact_mod_cast (ENNReal.coe_div (p := x) (hr := h₃)).symm

end ENNReal

lemma b (_h g : true) : true ∧ true := by
  constructor
  assumption_mod_cast
  assumption_mod_cast

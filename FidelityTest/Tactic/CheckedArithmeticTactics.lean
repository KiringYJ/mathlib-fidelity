module

import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Arithmetic tactics on quotients and inverses that carry their invertibility evidence:
`linarith` cancels numeral denominators, and `norm_num1`, `ring_nf` and `field_simp` print ordinary
fractions. -/

section linarith

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

example (x y : ℚ) (h : x ≤ y / 2) (h2 : 0 ≤ y) : x ≤ y := by linarith

example (x y : α) (h : x ≤ y / 2) (h2 : 0 ≤ y) : x ≤ y := by linarith

example (x z : α) (_h1 : z ≤ x + 1 / 2) (h2 : x + 1 / 2 < z + 1) : x - z ≤ 1 / 2 := by
  linarith

example (x : α) (h : 3⁻¹ * x ≤ 1) : x ≤ 3 := by linarith

end linarith

section norm_num

example (x : ℚ) (h : x = 2 / 4 - 1 / 3 - 1) : x = -(5 / 6) := by
  norm_num1 at h
  exact h

example (x : ℚ) (h : x = 2 / 4 + 1 / 3) : x = 5 / 6 := by
  norm_num1 at h
  exact h

end norm_num

section ring_nf

example (x : ℚ) (P : ℚ → Prop) (h : P (x / 2 + x / 3)) : P (x * (5 / 6)) := by
  ring_nf at h
  exact h

end ring_nf

section field_simp

example (x y : ℚ) (hy : y ≠ 0) (P : ℚ → Prop) (h : P (x / y + 1)) : P ((x + y) / y) := by
  field_simp at h
  exact h

example (x y z : ℚ) (hy : y ≠ 0) (hz : z ≠ 0) (P : ℚ → Prop) (h : P (x / y + 1 / z)) :
    P ((x * z + y) / (y * z)) := by
  field_simp at h
  exact h

end field_simp

section field

variable {K : Type*} [Field K]

/-- Goals without denominators still reach the polynomial normalization step. -/
example (a b : K) : a * b = a * b := by field

example (a b : K) : a * b = b * a := by field

example (a b c : K) (hb : b ≠ 0) : a / b + c / b = (a + c) / b := by field

end field

section elaboration

open Equiv Perm in
/-- A power of a group element whose type still contains a placeholder is not postponed, so
`rw` can match it. -/
example {α : Type*} [DecidableEq α] (c : Perm α) (s : Finset α) (hc : ∀ x, c x ∈ s ↔ x ∈ s)
    (n : ℤ) (x : α) (hx : x ∈ s) :
    (ofSubtype (subtypePerm c hc ^ n)) x = (subtypePerm c hc ^ n) ⟨x, hx⟩ := by
  rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx]

end elaboration

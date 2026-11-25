/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped ENNReal NNReal Quantale

#synth Inv ℝ≥0∞
#synth Pow ℝ≥0∞ ℤ

/--
error: failed to synthesize
  Div ℝ≥0∞

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div ℝ≥0∞

/--
error: failed to synthesize
  HDiv ℝ≥0∞ ℝ≥0∞ ℝ≥0∞

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HDiv ℝ≥0∞ ℝ≥0∞ ℝ≥0∞

example : (0 : ℝ≥0∞) ^ (-1 : ℤ) = ∞ := by
  simp [ENNReal.zero_zpow_def]

example : (∞ : ℝ≥0∞) ^ (-1 : ℤ) = 0 := by
  simp [ENNReal.top_zpow_def]

example : ENNReal.div 0 ∞ ⟨ENNReal.top_ne_zero, Or.inl ENNReal.zero_ne_top⟩ = 0 := by
  simp

example : ENNReal.div ∞ 1 ⟨one_ne_zero, Or.inr ENNReal.one_ne_top⟩ = ∞ := by
  simp

example : ENNReal.extendedDiv 1 0 ⟨Or.inl one_ne_zero, Or.inr ENNReal.zero_ne_top⟩ = ∞ := by
  simp

example : ENNReal.extendedDiv 1 ∞ ⟨Or.inr ENNReal.top_ne_zero, Or.inl ENNReal.one_ne_top⟩ = 0 := by
  simp

example : ENNReal.divInf 0 0 = 0 := by simp [ENNReal.divInf]
example : ENNReal.divInf ∞ ∞ = 0 := by simp [ENNReal.divInf]
example : ((0 : ℝ≥0∞) ⇨ₗ 0) = ∞ := by simp
example : (∞ ⇨ₗ ∞) = ∞ := by simp

example (a b : ℝ≥0∞) (hb : IsUnit b) :
    Checked.div a b hb =
      ENNReal.div a b ⟨hb.ne_zero, Or.inr (ENNReal.isUnit_iff.1 hb).2⟩ :=
  ENNReal.checkedDiv_eq_div a b hb

noncomputable section

example (a b : ℝ≥0∞) (h : b ≠ 0 ∧ (a ≠ ∞ ∨ b ≠ ∞)) :
    a / b = ENNReal.div a b h := rfl

example (a b : ℝ≥0∞) (hb : b ≠ 0) (ha : a ≠ ∞) :
    a / b = ENNReal.div a b ⟨hb, Or.inl ha⟩ := rfl

example (a b : ℝ≥0∞) (hb : b ≠ 0) (ht : b ≠ ∞) :
    a / b = ENNReal.div a b ⟨hb, Or.inr ht⟩ := rfl

example (a : ℝ≥0∞) (x : ℝ≥0) (hx : x ≠ 0) :
    a / (x : ℝ≥0∞) = ENNReal.div a x ⟨ENNReal.coe_ne_zero.2 hx, Or.inr ENNReal.coe_ne_top⟩ := rfl

example (a : ℝ≥0∞) : a / 2 = ENNReal.div a 2 ⟨two_ne_zero, Or.inr ENNReal.ofNat_ne_top⟩ := rfl

example (a : ℝ≥0∞) : a / 2 / 3 = ENNReal.div (ENNReal.div a 2) 3 := rfl

example (a : ℝ≥0∞) (ha : 0 < a) (P : ℝ≥0∞ → Prop)
    (h : ∀ b : ℝ≥0∞, 0 < b → P b) : ∃ b, P b := by
  specialize h (a / 2) (ENNReal.half_pos ha.ne')
  exact ⟨_, h⟩

/-- info: fun a => a / 2 : ℝ≥0∞ → ℝ≥0∞ -/
#guard_msgs in
#check fun (a : ℝ≥0∞) => ENNReal.div a 2

/-- info: fun a => a.extendedDiv 2 ⋯ : ℝ≥0∞ → ℝ≥0∞ -/
#guard_msgs in
#check fun (a : ℝ≥0∞) => ENNReal.extendedDiv a 2 ⟨Or.inr two_ne_zero, Or.inr ENNReal.ofNat_ne_top⟩

/-- info: fun a => a.divInf 2 : ℝ≥0∞ → ℝ≥0∞ -/
#guard_msgs in
#check fun (a : ℝ≥0∞) => ENNReal.divInf a 2

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ENNReal division requires a nonzero denominator and a finite operand
a b : ℝ≥0∞
⊢ b ≠ 0 ∧ (a ≠ ∞ ∨ b ≠ ∞)
-/
#guard_msgs in
example (a b : ℝ≥0∞) : ℝ≥0∞ := a / b

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ENNReal division requires a nonzero denominator and a finite operand
⊢ 0 ≠ 0 ∧ (0 ≠ ∞ ∨ 0 ≠ ∞)
-/
#guard_msgs in
example : ℝ≥0∞ := (0 : ℝ≥0∞) / (0 : ℝ≥0∞)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ENNReal division requires a nonzero denominator and a finite operand
⊢ 0 ≠ 0 ∧ (1 ≠ ∞ ∨ 0 ≠ ∞)
-/
#guard_msgs in
example : ℝ≥0∞ := (1 : ℝ≥0∞) / (0 : ℝ≥0∞)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ENNReal division requires a nonzero denominator and a finite operand
⊢ 0 ≠ 0 ∧ (∞ ≠ ∞ ∨ 0 ≠ ∞)
-/
#guard_msgs in
example : ℝ≥0∞ := ∞ / (0 : ℝ≥0∞)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ENNReal division requires a nonzero denominator and a finite operand
⊢ ∞ ≠ 0 ∧ (∞ ≠ ∞ ∨ ∞ ≠ ∞)
-/
#guard_msgs in
example : ℝ≥0∞ := (∞ : ℝ≥0∞) / ∞

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : ℝ≥0∞ := ENNReal.extendedDiv 0 0 (by simp)

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : ℝ≥0∞ := ENNReal.extendedDiv ∞ ∞ (by simp)

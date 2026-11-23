/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Boundary checks for exponential quotients and logarithm positivity certificates. -/

open Filter
open scoped Topology

-- Exponent zero admits every base, including zero.
example : ∃ x : {x : ℝ // x ^ (0 : ℕ) ≠ 0}, (x : ℝ) = 0 :=
  ⟨⟨0, by simp⟩, rfl⟩

example : Tendsto
    (fun x : {x : ℝ // x ^ (0 : ℕ) ≠ 0} ↦
      Checked.div (Real.exp x) ((x : ℝ) ^ (0 : ℕ)) x.2.isUnit)
    (comap Subtype.val atTop) atTop := Real.tendsto_exp_div_pow_atTop 0

-- Positivity derives its certificates from integer comparisons of numerator and denominator.
example : 0 < Real.log (3 / 2 : ℝ) := by positivity
example : 0 < Real.log (-3 / 2 : ℝ) := by positivity
example : Real.log (1 / 2 : ℝ) ≠ 0 := by positivity
example : Real.log (-1 / 2 : ℝ) ≠ 0 := by positivity

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example : ℝ := Real.log (0 : ℝ)⁻¹

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Checked inverse and integer-power domains in the retained real/complex power substrate. -/

open scoped NNReal ENNReal

open Filter

noncomputable section

example : (4 : ℝ) ^ (-1 : ℝ) = 1 / 4 := by norm_num

example : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by norm_num

example : (4 : ℝ≥0) ^ (-1 : ℝ) = 1 / 4 := by norm_num

example : (4 : ℝ≥0) ^ (-(1 / 2) : ℝ) = 1 / 2 := by norm_num

example : (0 : ℝ) ^ (0 : ℤ) = 1 := by simp

example (n : ℕ) : (0 : ℝ) ^ (n : ℝ) = (0 : ℝ) ^ (n : ℤ) :=
  Real.rpow_intCast 0 n
    (h := fun hn ↦ (not_lt_of_ge (Int.natCast_nonneg n) hn).elim)

example (n : ℕ) : (0 : ℂ) ^ (n : ℂ) = (0 : ℂ) ^ (n : ℤ) :=
  Complex.cpow_intCast 0 n
    (h := fun hn ↦ (not_lt_of_ge (Int.natCast_nonneg n) hn).elim)

example : (0 : ℝ) ^ (-(0 : ℝ)) = ((0 : ℝ) ^ (0 : ℝ))⁻¹ :=
  Real.rpow_neg (x := 0) le_rfl 0

example : (0 : ℝ≥0) ^ (-(0 : ℝ)) = ((0 : ℝ≥0) ^ (0 : ℝ))⁻¹ :=
  NNReal.rpow_neg 0 0

-- The extended nonnegative reals retain their intrinsic order-valued reciprocal.
example : (0 : ℝ≥0∞)⁻¹ = ∞ := ENNReal.inv_zero

example : (∞ : ℝ≥0∞)⁻¹ = 0 := ENNReal.inv_top

-- The root sequence is defined on positive indices and its filter is nontrivial.
example : (comap (Subtype.val : {n : ℕ // n ≠ 0} → ℕ) atTop).NeBot :=
  atTop_neBot.comap_of_range_mem <| by
    rw [Subtype.range_coe_subtype]
    exact eventually_iff.mp ((eventually_gt_atTop (0 : ℕ)).mono fun n hn ↦ hn.ne')

example (x : ℝ≥0) :
    ∀ᶠ n : {n : ℕ // n ≠ 0} in comap Subtype.val atTop,
      x ^ (1 / ((n : ℕ) : ℝ)) ≤ 2 :=
  NNReal.eventually_pow_one_div_le x (by norm_num)

example (x : ℝ≥0∞) (hx : x ≠ ∞) :
    ∀ᶠ n : {n : ℕ // n ≠ 0} in comap Subtype.val atTop,
      x ^ (1 / ((n : ℕ) : ℝ)) ≤ 2 :=
  ENNReal.eventually_pow_one_div_le hx (by norm_num)

example : (0 : ℂ) ^ ((-1 : ℤ) * (0 : ℂ)) =
    ((0 : ℂ) ^ (0 : ℂ)) ^ (-1 : ℤ) :=
  Complex.cpow_int_mul 0 (-1) 0 (h := fun _ => by simp)

example (y : ℂ) : (0 : ℂ) ^ (y - 0) = (0 : ℂ) ^ y / (0 : ℂ) ^ (0 : ℂ) :=
  Complex.cpow_sub y 0 (hxz := by simp)

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
example : ℝ := (0 : ℝ)⁻¹

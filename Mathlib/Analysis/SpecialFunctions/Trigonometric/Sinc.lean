/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Sinc function

This file contains the definition of the sinc function and some of its properties.

## Main definitions

* `Real.sinc`: the (unnormalized) sinc function, defined as `sinc x = sin x / x` for `x ≠ 0`
  and `1` for `x = 0`.

## Main statements

* `continuous_sinc`: the sinc function is continuous.

-/

@[expose] public section

open scoped Topology

namespace Real

variable {x : ℝ}

/-- The continuous extension of `sin x / x` with value `1` at zero. -/
@[pp_nodot]
noncomputable def sinc (x : ℝ) : ℝ :=
  if hx : x = 0 then 1 else Checked.div (sin x) x (Ne.isUnit hx)

lemma sinc_apply : sinc x = if hx : x = 0 then 1 else Checked.div (sin x) x (Ne.isUnit hx) := rfl

@[simp]
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

lemma sinc_of_ne_zero (hx : x ≠ 0) : sinc x = sin x / x := by simp [sinc, hx]

lemma sinc_eq_dslope : sinc = dslope sin 0 := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [sinc_zero, dslope_same]
    simpa only [cos_zero] using (hasDerivAt_sin (0 : ℝ)).deriv.symm
  · rw [sinc_of_ne_zero hx, dslope_of_ne _ hx, slope_def_field]
    simp only [sin_zero, sub_zero]

@[simp]
lemma sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx), div_neg₀, neg_div₀]

lemma abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx, abs_div, div_le_one (abs_pos.mpr hx)]
  have hsin : LipschitzWith 1 sin := by
    refine lipschitzWith_of_nnnorm_deriv_le differentiable_sin fun t ↦ ?_
    exact_mod_cast (show ‖deriv sin t id‖ ≤ (1 : ℝ) by
      rw [(hasDerivAt_sin t).deriv, Real.norm_eq_abs]
      exact abs_cos_le_one t)
  simpa [Real.dist_eq] using hsin.dist_le_mul x 0

lemma sinc_le_one (x : ℝ) : sinc x ≤ 1 := (abs_le.mp (abs_sinc_le_one x)).2

lemma neg_one_le_sinc (x : ℝ) : -1 ≤ sinc x := (abs_le.mp (abs_sinc_le_one x)).1

lemma sin_div_le_inv_abs (x : ℝ) {hx : IsUnit x} :
    sin x / x ≤ Checked.inv |x| (abs_ne_zero.mpr hx.ne_zero).isUnit := by
  have habs : 0 < |x| := abs_pos.mpr hx.ne_zero
  calc
    sin x / x ≤ |sin x / x| := le_abs_self _
    _ = |sin x| / |x| := abs_div _ _
    _ ≤ 1 / |x| := (div_le_div_iff_of_pos_right habs).mpr (abs_sin_le_one x)
    _ = _ := one_div₀ _

lemma sinc_le_inv_abs (hx : x ≠ 0) : sinc x ≤ |x|⁻¹ := by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x (hx := hx.isUnit)

/-- The function `sinc` is continuous. -/
@[fun_prop]
lemma continuous_sinc : Continuous sinc := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr (differentiable_sin 0)
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

end Real

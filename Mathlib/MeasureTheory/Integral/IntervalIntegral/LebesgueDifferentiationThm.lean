/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem. There are two
versions in this file.

* `LocallyIntegrable.ae_hasDerivAt_integral` is the global version. It states that if `f : ℝ → E`
  is locally integrable (`E` a Banach space), then for almost every `x`, for any `c : ℝ`, the
  derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.

* `IntervalIntegrable.ae_hasDerivAt_integral` is the local version. It states that if `f : ℝ → E`
  is interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`,
  the derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/

public section

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The (global) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → E` is
locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem LocallyIntegrable.ae_hasDerivAt_integral {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  have hAvg {a b : ℝ} (hab : a < b) :
      (⨍ t in Icc a b, f t) = (b - a)⁻¹ • ∫ t in Icc a b, f t := by
    have hReal : volume.real (Icc a b) = b - a := by
      simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    have hUnit : IsUnit (volume.real (Icc a b)) := by
      rw [hReal]
      exact (sub_pos.mpr hab).ne'.isUnit
    simpa only [hReal] using setAverage_eq volume f (Icc a b) (hs := hUnit)
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hv : Tendsto (Subtype.val : Iio x → ℝ) (comap Subtype.val (𝓝 x)) (𝓝[<] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_comap, .of_forall fun y ↦ y.2⟩
    refine Filter.tendsto_congr' ?_ |>.mpr ((hx.comp x.tendsto_Icc_vitaliFamily_left).comp hv)
    filter_upwards with y
    have hy : (y : ℝ) < x := y.2
    have hInv : ((y : ℝ) - x)⁻¹ = -(x - (y : ℝ))⁻¹ := by
      apply inv_eq_of_mul_eq_one_right₀
      rw [← neg_sub, neg_mul_neg, mul_inv_cancel₀]
    simp [Function.comp_apply, slope, intervalIntegral.integral_interval_sub_left, hg,
      intervalIntegral.integral_of_ge, hy.le, h, hInv, hAvg hy]
  · have hv : Tendsto (Subtype.val : Ioi x → ℝ) (comap Subtype.val (𝓝 x)) (𝓝[>] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_comap, .of_forall fun y ↦ y.2⟩
    refine Filter.tendsto_congr' ?_ |>.mpr ((hx.comp x.tendsto_Icc_vitaliFamily_right).comp hv)
    filter_upwards with y
    have hy : x < (y : ℝ) := y.2
    simp [Function.comp_apply, slope, intervalIntegral.integral_interval_sub_left, hg,
      intervalIntegral.integral_of_le, hy.le, h, hAvg hy]

/-- The (local) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → E` is
interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`, the
derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_hasDerivAt_integral {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → ∀ c ∈ uIcc a b, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, h₁, h₂] with x hx _ _ _
  intro c hc
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind

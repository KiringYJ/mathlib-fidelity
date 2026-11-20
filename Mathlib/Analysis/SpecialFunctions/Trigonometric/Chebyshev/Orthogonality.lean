/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* `integrable_measureT`: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1)`.
* `integral_eval_T_real_mul_evalT_real_measureT_of_ne`:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* `integral_eval_T_real_mul_self_measureT_zero`:
  if `n = m = 0` then the integral equals `π`.
* `integral_eval_T_real_mul_self_measureT_of_ne_zero`:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal ENNReal

open Set

/-- The Chebyshev weight on the open interval where its denominator is positive. -/
noncomputable def weightT (x : Ioo (-1 : ℝ) 1) : ℝ≥0 :=
  let hp := sqrt_pos.mpr
    (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x.val).mpr (abs_lt.mpr x.property)))
  ⟨Checked.inv √(1 - x.val ^ 2) hp.ne'.isUnit, (inv_pos.mpr hp).le⟩

private theorem coe_weightT (x : Ioo (-1 : ℝ) 1) : (weightT x : ℝ) = deriv arcsin x := by
  simp [deriv_arcsin, x.property, weightT]
  rfl

private theorem measurable_weightT : Measurable weightT := by
  change Measurable (fun x : Ioo (-1 : ℝ) 1 ↦ weightT x)
  apply Measurable.subtype_mk
  change Measurable (fun x : Ioo (-1 : ℝ) 1 ↦ (weightT x : ℝ))
  simp_rw [coe_weightT]
  exact (measurable_deriv arcsin).comp measurable_subtype_coe

/-- Lebesgue measure on the open interval, weighted by `1 / √(1 - x ^ 2)` and mapped into ℝ. -/
noncomputable def measureT : Measure ℝ :=
  ((volume.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ)).withDensity
    (fun x ↦ (weightT x : ℝ≥0∞))).map Subtype.val measurable_subtype_coe.aemeasurable

theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x : Ioo (-1 : ℝ) 1, f x * (weightT x : ℝ) ∂volume.comap Subtype.val := by
  rw [measureT, (MeasurableEmbedding.subtype_coe measurableSet_Ioo).integral_map,
    integral_withDensity_eq_integral_smul measurable_weightT]
  simp [NNReal.smul_def, mul_comm]

private theorem intervalIntegrable_deriv_arcsin :
    IntervalIntegrable (fun x ↦ deriv arcsin x) volume (-1) 1 := by
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num)]
  apply integrableOn_deriv_of_nonneg continuous_arcsin.continuousOn
  · exact fun x hx ↦ (differentiableAt_arcsin.mpr ⟨hx.1.ne', hx.2.ne⟩).hasDerivAt
  · intro x hx
    rw [← coe_weightT ⟨x, hx⟩]
    exact (weightT ⟨x, hx⟩).property

theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    Integrable (fun x : Ioo (-1 : ℝ) 1 ↦ (weightT x : ℝ)) (volume.comap Subtype.val) := by
  simp_rw [coe_weightT]
  apply (integrableOn_iff_comap_subtypeVal (f := fun x ↦ deriv arcsin x id) measurableSet_Ioo).mp
  exact (intervalIntegrable_deriv_arcsin.1).mono_set Ioo_subset_Ioc_self

theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    Integrable f measureT := by
  rw [measureT, (MeasurableEmbedding.subtype_coe measurableSet_Ioo).integrable_map_iff,
    integrable_withDensity_iff_integrable_coe_smul measurable_weightT]
  simp only [smul_eq_mul, coe_weightT, Function.comp_apply, mul_comm]
  apply (integrableOn_iff_comap_subtypeVal (f := fun x ↦ f x * deriv arcsin x id)
    measurableSet_Ioo).mp
  have hfc : ContinuousOn f (uIcc (-1) 1) := by
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hf
  exact (intervalIntegrable_deriv_arcsin.continuousOn_mul hfc).1.mono_set Ioo_subset_Ioc_self

theorem integral_measureT_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * deriv arcsin x := by
    rw [integral_measureT, integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    simp_rw [coe_weightT]
    exact integral_subtype_comap measurableSet_Ioo (fun x ↦ f x * deriv arcsin x)
  _ = ∫ x in 1..-1, f x * -(deriv arcsin x) := by
    rw [integral_symm, ← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_deriv_nonpos (f' := fun x ↦ -(deriv arcsin x))]
    · exact integral_congr <| fun x hx ↦ by
        simp [Function.comp_apply, cos_arccos (x := x) (by aesop) (by aesop)]
    · fun_prop
    · intro x hx
      have hi : x ∈ Ioo (-1 : ℝ) 1 := by simpa using hx
      simpa only [deriv_arcsin] using hasDerivAt_arccos hi.1.ne' hi.2.ne
    · intro x hx
      have hi : x ∈ Ioo (-1 : ℝ) 1 := by simpa using hx
      rw [← coe_weightT ⟨x, hi⟩]
      exact neg_nonpos.mpr (weightT ⟨x, hi⟩).property
  _ = ∫ θ in 0..π, f (cos θ) := by simp

@[deprecated (since := "2026-03-19")]
alias integral_measureT_eq_integral_cos_of_continuous := integral_measureT_eq_integral_cos

theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T ℝ 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos]; simp

theorem integral_eval_T_real_measureT_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x ∂measureT = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rw [integral_comp_mul_left _ (hc := hn'), mul_zero, this, smul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : ℤ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT =
    ((∫ x, (T ℝ (n + m)).eval x ∂measureT) +
     (∫ x, (T ℝ (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T ℝ n * T ℝ m).eval x ∂measureT =
      (∫ x, (T ℝ (n + m)).eval x ∂measureT) +
      (∫ x, (T ℝ (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    rw [eq_div_iff, mul_comm]
    exact this
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]

theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind),
    integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_eval_T_real_measureT_zero

theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind), sub_self,
    integral_eval_T_real_measureT_zero, zero_add]

end Polynomial.Chebyshev

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/

public section


noncomputable section

namespace Complex

open Set Filter

open scoped Real

/-- The inclusion of the domain of the tangent into the domain of the quotient rule. -/
private def toUnitsDomain (y : {y : ℂ // cos y ≠ 0}) : {y : ℂ | IsUnit (cos y)} :=
  ⟨y, y.2.isUnit⟩

private theorem continuous_toUnitsDomain : Continuous toUnitsDomain :=
  continuous_subtype_val.subtype_mk _

/-- The tangent has derivative `1 / cos x ^ 2` at every point of its domain. -/
theorem hasStrictDerivAt_tan {x : ℂ} (h : cos x ≠ 0) :
    HasStrictDerivAt (fun y : {y : ℂ // cos y ≠ 0} ↦ tan y y.2) (1 / cos x ^ 2) ⟨x, h⟩
      Subtype.val := by
  have hdiv := (hasStrictDerivAt_sin x).div (hasStrictDerivAt_cos x) h.isUnit
  have key := HasFDerivAtFilter.comp_tendsto hdiv toUnitsDomain
    ((continuous_toUnitsDomain.tendsto ⟨x, h⟩).prodMap_nhds
      (continuous_toUnitsDomain.tendsto ⟨x, h⟩))
  have hD : (cos x * cos x - sin x * -sin x) /ₚ (h.isUnit.unit ^ 2) = 1 / cos x ^ 2 := by
    rw [mul_neg, sub_neg_eq_add, ← sq, ← sq, cos_sq_add_sin_sq]
    show 1 /ₚ _ = 1 /ₚ _
    congr 1
    ext
    simp
  rw [← hD]
  exact key

theorem hasDerivAt_tan {x : ℂ} (h : cos x ≠ 0) :
    HasDerivAt (fun y : {y : ℂ // cos y ≠ 0} ↦ tan y y.2) (1 / cos x ^ 2) ⟨x, h⟩ Subtype.val :=
  (hasStrictDerivAt_tan h).hasDerivAt

open scoped Topology

/-- The norm of the tangent tends to infinity at a pole, as a function on its domain. -/
theorem tendsto_norm_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
    Tendsto (fun y : {y : ℂ // cos y ≠ 0} ↦ ‖tan y y.2‖) (comap Subtype.val (𝓝[≠] x)) atTop := by
  have A : sin x ≠ 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[≠] x) (𝓝[≠] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  have hcos : Tendsto (fun y : {y : ℂ // cos y ≠ 0} ↦
      ((Units.mk0 ‖cos (y : ℂ)‖ (norm_ne_zero_iff.2 y.2) : ℝˣ) : ℝ))
      (comap Subtype.val (𝓝[≠] x)) (𝓝[>] 0) :=
    (tendsto_norm_nhdsNE_zero.comp B).comp tendsto_comap
  have hsin : Tendsto (fun y : {y : ℂ // cos y ≠ 0} ↦ ‖sin (y : ℂ)‖)
      (comap Subtype.val (𝓝[≠] x)) (𝓝 ‖sin x‖) :=
    ((continuous_sin.norm.tendsto x).mono_left nhdsWithin_le_nhds).comp tendsto_comap
  refine (hcos.inv_tendsto_nhdsGT_zero.atTop_mul_pos (norm_pos_iff.2 A) hsin).congr fun y ↦ ?_
  rw [tan_eq_sin_div_cos, norm_div, div_eq_inv_mul₀]
  rfl

theorem tendsto_norm_tan_atTop (k : ℤ) :
    Tendsto (fun y : {y : ℂ // cos y ≠ 0} ↦ ‖tan y y.2‖)
      (comap Subtype.val (𝓝[≠] ((2 * k + 1) * π / 2 : ℂ))) atTop :=
  tendsto_norm_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

theorem continuousAt_tan {x : ℂ} (hx : cos x ≠ 0) :
    ContinuousAt (fun y : {y : ℂ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ :=
  continuous_tan.continuousAt

theorem differentiableAt_tan {x : ℂ} (hx : cos x ≠ 0) :
    DifferentiableAt ℂ (fun y : {y : ℂ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ Subtype.val :=
  (hasDerivAt_tan hx).differentiableAt

@[simp]
theorem deriv_tan (x : ℂ) {hx : cos x ≠ 0} :
    deriv (fun y : {y : ℂ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ Subtype.val = 1 / cos x ^ 2 := by
  apply (hasDerivAt_tan hx).deriv_of_mem_nhds Topology.IsEmbedding.subtypeVal
  rw [Subtype.range_val]
  exact (isOpen_ne_fun continuous_cos continuous_const).mem_nhds hx

end Complex

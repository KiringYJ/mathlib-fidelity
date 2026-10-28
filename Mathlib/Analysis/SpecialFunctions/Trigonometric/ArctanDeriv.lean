/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# Derivatives of the `tan` and `arctan` functions.

Continuity and derivatives of the tangent and arctangent functions.
-/

public section


noncomputable section

namespace Real

open Set Filter

open scoped Topology Real

/-- The inclusion of the domain of the tangent into the domain of the quotient rule. -/
private def toUnitsDomain (y : {y : ℝ // cos y ≠ 0}) : {y : ℝ | IsUnit (cos y)} :=
  ⟨y, y.2.isUnit⟩

private theorem continuous_toUnitsDomain : Continuous toUnitsDomain :=
  continuous_subtype_val.subtype_mk _

/-- The tangent has derivative `1 / cos x ^ 2` at every point of its domain. -/
theorem hasStrictDerivAt_tan {x : ℝ} (h : cos x ≠ 0) :
    HasStrictDerivAt (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2) (1 / cos x ^ 2) ⟨x, h⟩
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

theorem hasDerivAt_tan {x : ℝ} (h : cos x ≠ 0) :
    HasDerivAt (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2) (1 / cos x ^ 2) ⟨x, h⟩ Subtype.val :=
  (hasStrictDerivAt_tan h).hasDerivAt

/-- The absolute value of the tangent tends to infinity at a pole, as a function on its domain. -/
theorem tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
    Tendsto (fun y : {y : ℝ // cos y ≠ 0} ↦ |tan y y.2|) (comap Subtype.val (𝓝[≠] x)) atTop := by
  have A : sin x ≠ 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[≠] x) (𝓝[≠] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  have hcos : Tendsto (fun y : {y : ℝ // cos y ≠ 0} ↦
      ((Units.mk0 |cos (y : ℝ)| (abs_ne_zero.2 y.2) : ℝˣ) : ℝ))
      (comap Subtype.val (𝓝[≠] x)) (𝓝[>] 0) := by
    have : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] 0) (𝓝[>] 0) := by
      simpa only [Real.norm_eq_abs] using tendsto_norm_nhdsNE_zero
    exact (this.comp B).comp tendsto_comap
  have hsin : Tendsto (fun y : {y : ℝ // cos y ≠ 0} ↦ |sin (y : ℝ)|)
      (comap Subtype.val (𝓝[≠] x)) (𝓝 |sin x|) :=
    ((continuous_sin.abs.tendsto x).mono_left nhdsWithin_le_nhds).comp tendsto_comap
  refine (hcos.inv_tendsto_nhdsGT_zero.atTop_mul_pos (abs_pos.2 A) hsin).congr fun y ↦ ?_
  rw [tan_eq_sin_div_cos, abs_div, div_eq_inv_mul₀]
  rfl

theorem tendsto_abs_tan_atTop (k : ℤ) :
    Tendsto (fun y : {y : ℝ // cos y ≠ 0} ↦ |tan y y.2|)
      (comap Subtype.val (𝓝[≠] ((2 * k + 1) * π / 2))) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

theorem continuousAt_tan {x : ℝ} (hx : cos x ≠ 0) :
    ContinuousAt (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ :=
  continuous_tan.continuousAt

theorem differentiableAt_tan {x : ℝ} (hx : cos x ≠ 0) :
    DifferentiableAt ℝ (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ Subtype.val :=
  (hasDerivAt_tan hx).differentiableAt

@[simp]
theorem deriv_tan (x : ℝ) {hx : cos x ≠ 0} :
    deriv (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2) ⟨x, hx⟩ Subtype.val = 1 / cos x ^ 2 := by
  apply (hasDerivAt_tan hx).deriv_of_mem_nhds Topology.IsEmbedding.subtypeVal
  rw [Subtype.range_val]
  exact (isOpen_ne_fun continuous_cos continuous_const).mem_nhds hx

/-- The tangent restricted to `(-(π / 2), π / 2)` has derivative `1 / cos x ^ 2`. -/
theorem hasDerivAt_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) :
    HasDerivAt (fun y : Ioo (-(π / 2) : ℝ) (π / 2) ↦ tan y (cos_pos_of_mem_Ioo y.2).ne')
      (1 / cos x ^ 2) ⟨x, h⟩ Subtype.val := by
  have he : Continuous fun y : Ioo (-(π / 2) : ℝ) (π / 2) ↦
      (⟨y, (cos_pos_of_mem_Ioo y.2).ne'⟩ : {y : ℝ // cos y ≠ 0}) :=
    continuous_subtype_val.subtype_mk _
  exact HasFDerivAtFilter.comp_tendsto (hasDerivAt_tan (cos_pos_of_mem_Ioo h).ne') _
    ((he.tendsto ⟨x, h⟩).prodMap (tendsto_pure_pure ..))

theorem differentiableAt_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun y : Ioo (-(π / 2) : ℝ) (π / 2) ↦ tan y (cos_pos_of_mem_Ioo y.2).ne')
      ⟨x, h⟩ Subtype.val :=
  (hasDerivAt_tan_of_mem_Ioo h).differentiableAt

theorem hasStrictDerivAt_arctan (x : ℝ) : HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x := by
  have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
  simpa [cos_sq_arctan] using
    tanPartialHomeomorph.hasStrictDerivAt_symm trivial (by simpa) (hasStrictDerivAt_tan A)

theorem hasDerivAt_arctan (x : ℝ) : HasDerivAt arctan (1 / (1 + x ^ 2)) x :=
  (hasStrictDerivAt_arctan x).hasDerivAt

theorem hasDerivAt_arctan' (x : ℝ) : HasDerivAt arctan (1 + x ^ 2)⁻¹ x :=
  one_div (1 + x ^ 2) ▸ hasDerivAt_arctan x

theorem differentiableAt_arctan (x : ℝ) : DifferentiableAt ℝ arctan x :=
  (hasDerivAt_arctan x).differentiableAt

theorem differentiable_arctan : Differentiable ℝ arctan :=
  differentiableAt_arctan

@[simp]
theorem deriv_arctan : deriv arctan = fun (x : ℝ) => 1 / (1 + x ^ 2) :=
  funext fun x => (hasDerivAt_arctan x).deriv

theorem contDiff_arctan {n : WithTop ℕ∞} : ContDiff ℝ n arctan :=
  contDiff_iff_contDiffAt.2 fun x =>
    have : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
    tanPartialHomeomorph.contDiffAt_symm_deriv (by simpa) trivial (hasDerivAt_tan this)
      (contDiffAt_tan.2 this)

end Real

section

/-!
### Lemmas for derivatives of the composition of `Real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `Real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/


open Real

section deriv

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.arctan (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasStrictDerivAt_arctan (f x)).comp x hf

theorem HasDerivAt.arctan (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasDerivAt_arctan (f x)).comp x hf

theorem HasDerivWithinAt.arctan (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') s x :=
  (Real.hasDerivAt_arctan (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => arctan (f x)) s x = 1 / (1 + f x ^ 2) * derivWithin f s x :=
  hf.hasDerivWithinAt.arctan.derivWithin hxs

@[simp]
theorem deriv_arctan (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => arctan (f x)) x = 1 / (1 + f x ^ 2) * deriv f x :=
  hc.hasDerivAt.arctan.deriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E} {n : ℕ∞}

theorem HasStrictFDerivAt.arctan (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasStrictDerivAt_arctan (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.arctan (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasDerivAt_arctan (f x)).comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.arctan (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') s x :=
  (hasDerivAt_arctan (f x)).comp_hasFDerivWithinAt x hf

theorem fderivWithin_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => arctan (f x)) s x = (1 / (1 + f x ^ 2)) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.arctan.fderivWithin hxs

@[simp]
theorem fderiv_arctan (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => arctan (f x)) x = (1 / (1 + f x ^ 2)) • fderiv ℝ f x :=
  hc.hasFDerivAt.arctan.fderiv

theorem DifferentiableWithinAt.arctan (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.arctan (f x)) s x :=
  hf.hasFDerivWithinAt.arctan.differentiableWithinAt

@[simp]
theorem DifferentiableAt.arctan (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => arctan (f x)) x :=
  hc.hasFDerivAt.arctan.differentiableAt

theorem DifferentiableOn.arctan (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => arctan (f x)) s := fun x h => (hc x h).arctan

@[simp]
theorem Differentiable.arctan (hc : Differentiable ℝ f) : Differentiable ℝ fun x => arctan (f x) :=
  fun x => (hc x).arctan

theorem ContDiffAt.arctan (h : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => arctan (f x)) x :=
  contDiff_arctan.contDiffAt.comp x h

theorem ContDiff.arctan (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arctan (f x) :=
  contDiff_arctan.comp h

theorem ContDiffWithinAt.arctan (h : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => arctan (f x)) s x :=
  contDiff_arctan.comp_contDiffWithinAt h

theorem ContDiffOn.arctan (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arctan (f x)) s :=
  contDiff_arctan.comp_contDiffOn h

end fderiv

end

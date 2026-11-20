/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Results relating `Measure.tilted` to `mgf` and `cgf`

For a random variable `X : Ω → ℝ` and a measure `μ`, the tilt `μ.tilted (t * X ·) h` uses
the moment-generating function (`mgf`) of `X` as its normalizer. The proof `h` certifies
that this normalizer is a unit. A nonzero measure and an interior parameter of the
exponential integrability set give such a proof.

## Main statements

* `integral_tilted_mul_self`: the integral of `X` against the tilted measure `μ.tilted (t * X ·) h`
  is the first derivative of the cumulant-generating function of `X` at `t`.
  `∫ ω, X ω ∂(μ.tilted (t * X ·) h) = deriv (cgf X μ) t`
* `variance_tilted_mul`: the variance of `X` under the tilted measure `μ.tilted (t * X ·) h`
  is the second derivative of the cumulant-generating function of `X` at `t`.
  `Var[X; μ.tilted (t * X ·) h] = iteratedDeriv 2 (cgf X μ) t`

-/

public section


open MeasureTheory Real Set

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : SigmaAlgebra Ω} {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

namespace ProbabilityTheory

private lemma exp_cgf_of_isUnit {h : IsUnit (mgf X μ t)} : exp (cgf X μ t) = mgf X μ t :=
  exp_log (lt_of_le_of_ne mgf_nonneg h.ne_zero.symm)

section Apply

/-! ### Apply lemmas for `tilted` expressed with `mgf` or `cgf`. -/

variable {h : IsUnit (mgf X μ t)}

lemma tilted_mul_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) h s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ :=
  tilted_apply' μ (t * X ·) hs (h := h)

lemma tilted_mul_apply_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) h s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ :=
  tilted_apply μ (t * X ·) s (h := h)

lemma tilted_mul_apply_cgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) h s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf_of_isUnit (h := h)]

lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) h s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf_of_isUnit (h := h)]

lemma tilted_mul_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) h s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) :=
  tilted_apply_eq_ofReal_integral' (t * X ·) hs (h := h)

lemma tilted_mul_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) h s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) :=
  tilted_apply_eq_ofReal_integral (t * X ·) s (h := h)

lemma tilted_mul_apply_eq_ofReal_integral_cgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) h s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub, exp_cgf_of_isUnit (h := h)]

lemma tilted_mul_apply_eq_ofReal_integral_cgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) h s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub, exp_cgf_of_isUnit (h := h)]

end Apply

section Integral

/-! ### Integral of `tilted` expressed with `mgf` or `cgf`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : IsUnit (mgf X μ t)}

lemma setIntegral_tilted_mul_eq_mgf' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·) h) = ∫ x in s, (exp (t * X x) / mgf X μ t) • g x ∂μ :=
  setIntegral_tilted' (t * X ·) g hs (h := h)

lemma setIntegral_tilted_mul_eq_mgf [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·) h) = ∫ x in s, (exp (t * X x) / mgf X μ t) • g x ∂μ :=
  setIntegral_tilted (t * X ·) g s (h := h)

lemma setIntegral_tilted_mul_eq_cgf' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·) h) = ∫ x in s, exp (t * X x - cgf X μ t) • g x ∂μ := by
  simp_rw [setIntegral_tilted_mul_eq_mgf' g hs, exp_sub, exp_cgf_of_isUnit (h := h)]

lemma setIntegral_tilted_mul_eq_cgf [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·) h) = ∫ x in s, exp (t * X x - cgf X μ t) • g x ∂μ := by
  simp_rw [setIntegral_tilted_mul_eq_mgf g s, exp_sub, exp_cgf_of_isUnit (h := h)]

lemma integral_tilted_mul_eq_mgf (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·) h) = ∫ ω, (exp (t * X ω) / mgf X μ t) • g ω ∂μ :=
  integral_tilted (t * X ·) g (h := h)

lemma integral_tilted_mul_eq_cgf (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·) h) = ∫ ω, exp (t * X ω - cgf X μ t) • g ω ∂μ := by
  simp_rw [integral_tilted_mul_eq_mgf g, exp_sub, exp_cgf_of_isUnit (h := h)]

end Integral

/-- The integral under the tilt equals the first derivative of the cumulant-generating function. -/
lemma integral_tilted_mul_self [NeZero μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    ∫ ω, X ω ∂(μ.tilted (t * X ·) (isUnit_mgf_of_mem_interior ht)) = deriv (cgf X μ) t := by
  have h := isUnit_mgf_of_mem_interior ht
  simp_rw [integral_tilted_mul_eq_mgf (h := h), deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

lemma memLp_tilted_mul [NeZero μ] (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p (μ.tilted (t * X ·) (isUnit_mgf_of_mem_interior ht)) := by
  have h := isUnit_mgf_of_mem_interior ht
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  have hAC := tilted_absolutelyContinuous μ (t * X ·) (h := h)
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac hAC
  refine ⟨hX.aestronglyMeasurable.mono_ac hAC, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (h := h), smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

/-- The variance under the tilt equals the second derivative of the cumulant-generating function. -/
lemma variance_tilted_mul [NeZero μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·) (isUnit_mgf_of_mem_interior ht)] = iteratedDeriv 2 (cgf X μ) t := by
  have h := isUnit_mgf_of_mem_interior ht
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht, iteratedDeriv_two_cgf_eq_integral ht,
    integral_tilted_mul_eq_mgf (h := h), ← integral_div]
  simp only [smul_eq_mul]
  congr with ω
  ring

end ProbabilityTheory

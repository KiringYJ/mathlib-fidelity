/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Results about both conditional expectations

For non-negative real functions, we have two versions of the conditional expectation:
`condExp` and `condLExp`, built from the Bochner and Lebesgue integrals respectively.
In this file, we gather results that involve both versions.

## Main statements

* `MeasureTheory.IsCondLExp.toReal`: for a function `f` with finite integral, the conditional
  (Lebesgue) expectations of `f` converted to `ℝ` by `ENNReal.toReal` are conditional expectations
  of `f` converted to `ℝ`.
* `MeasureTheory.IsCondExp.ofReal`: conversely, for a nonnegative integrable function, the
  extended nonnegative reals of its conditional expectations are its conditional (Lebesgue)
  expectations.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m m𝓧 : SigmaAlgebra 𝓧} {μ : Measure 𝓧}

/-- For a function `f` with finite integral, a conditional (Lebesgue) expectation of `f` given a
sub-σ-algebra, converted to `ℝ` by `ENNReal.toReal`, is a conditional expectation of `f` converted
to `ℝ`: the two
conditional expectations agree. -/
lemma IsCondLExp.toReal (hm : m ≤ m𝓧) {f G : 𝓧 → ℝ≥0∞} (h : IsCondLExp m μ f G)
    (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    IsCondExp m μ (fun x ↦ (f x).toReal) fun x ↦ (G x).toReal := by
  obtain ⟨G', hG'm, hGG', -⟩ := h.exists_measurable
  have hG_meas : AEMeasurable G μ := h.aemeasurable' hm
  have hG_lt : ∀ᵐ x ∂μ, G x < ∞ := h.ae_lt_top hm hf
  have hf_lt : ∀ᵐ x ∂μ, f x < ∞ := ae_lt_top' hf_meas hf
  have h_fin (s : Set 𝓧) (hs : s ∈ m) : ∫⁻ x in s, G x ∂μ ≠ ∞ := by
    rw [h.setLIntegral_eq s hs]
    exact ((setLIntegral_le_lintegral _ _).trans_lt hf.lt_top).ne
  refine ⟨⟨fun x ↦ (G' x).toReal, hG'm.ennreal_toReal.stronglyMeasurable,
    hGG'.fun_comp ENNReal.toReal⟩, fun s hs _ ↦ ?_, fun s hs _ ↦ ?_⟩
  · exact integrable_toReal_of_lintegral_ne_top hG_meas.restrict (h_fin s hs)
  · rw [integral_toReal hG_meas.restrict (ae_restrict_of_ae hG_lt),
      integral_toReal hf_meas.restrict (ae_restrict_of_ae hf_lt), h.setLIntegral_eq s hs]

/-- For a nonnegative integrable function `f`, the extended nonnegative real of a conditional
expectation of `f` given a sub-σ-algebra is a conditional (Lebesgue) expectation of the extended
nonnegative real of `f`: the two conditional expectations agree. -/
lemma IsCondExp.ofReal (hm : m ≤ m𝓧) {f g : 𝓧 → ℝ} (h : IsCondExp m μ f g) (hf : Integrable f μ)
    (h'f : 0 ≤ᵐ[μ] f) :
    IsCondLExp m μ (fun x ↦ ENNReal.ofReal (f x)) fun x ↦ ENNReal.ofReal (g x) := by
  have hg : Integrable g μ := h.integrable hf
  have hg_nonneg : 0 ≤ᵐ[μ] g := h.nonneg hm hf h'f
  obtain ⟨g', hg'm, hgg'⟩ := h.aestronglyMeasurable
  refine ⟨⟨fun x ↦ ENNReal.ofReal (g' x), hg'm.measurable.ennreal_ofReal.stronglyMeasurable,
    hgg'.fun_comp ENNReal.ofReal⟩, fun s hs ↦ ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrableOn (ae_restrict_of_ae hg_nonneg),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae h'f),
    h.setIntegral_eq s hs hf.integrableOn]

/-- For a nonnegative integrable function `f`, the extended norm of a conditional expectation of
`f` given a sub-σ-algebra is a conditional (Lebesgue) expectation of the extended norm of `f`. -/
lemma IsCondExp.enorm (hm : m ≤ m𝓧) {f g : 𝓧 → ℝ} (h : IsCondExp m μ f g) (hf : Integrable f μ)
    (h'f : 0 ≤ᵐ[μ] f) : IsCondLExp m μ (fun x ↦ ‖f x‖ₑ) fun x ↦ ‖g x‖ₑ := by
  refine ((h.ofReal hm hf h'f).congr_left ?_).congr_right ?_
  · filter_upwards [h'f] with x hx using by simp [Real.enorm_eq_ofReal hx]
  · filter_upwards [h.nonneg hm hf h'f] with x hx using by simp [Real.enorm_eq_ofReal hx]

/-- The integral of the extended norm of a conditional probability of a null-measurable set of
finite measure given a sub-σ-algebra is the measure of the set. -/
lemma IsCondExp.lintegral_enorm_indicator (hm : m ≤ m𝓧) {s : Set 𝓧} {g : 𝓧 → ℝ}
    (h : IsCondExp m μ (s.indicator fun _ ↦ (1 : ℝ)) g) (hs : NullMeasurableSet s μ)
    (h's : μ s ≠ ∞ := by finiteness) : ∫⁻ a, ‖g a‖ₑ ∂μ = μ s := by
  have hf : Integrable (s.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrableOn_const h's).integrable_indicator₀ hs
  have h0 : 0 ≤ᵐ[μ] s.indicator fun _ ↦ (1 : ℝ) :=
    Filter.Eventually.of_forall fun x ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
  rw [(h.enorm hm hf h0).lintegral_eq]
  simp [enorm_indicator_eq_indicator_enorm, lintegral_indicator₀ hs]

end MeasureTheory

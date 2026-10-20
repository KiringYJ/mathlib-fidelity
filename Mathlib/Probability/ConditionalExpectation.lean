/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.isCondExp_integral_of_indep`: if `m₁, m₂` are independent σ-algebras and `f` is an
  integrable `m₁`-measurable function, then the constant `𝔼[f]` is a conditional expectation of `f`
  given `m₂`, so that `𝔼[f | m₂] = 𝔼[f]` (`MeasureTheory.condExp_indep_eq`).

-/

public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m₁ m₂ m : SigmaAlgebra Ω} {μ : Measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is an integrable `m₁`-measurable function,
then the constant `𝔼[f]` is a conditional expectation of `f` given `m₂`. No σ-finiteness is needed:
if a set of `m₂` has infinite measure, then so does the whole space, and `𝔼[f] = 0`. -/
theorem isCondExp_integral_of_indep (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m)
    (hf : AEStronglyMeasurable[m₁] f μ) (hfint : Integrable f μ) (hindp : Indep m₁ m₂ μ) :
    IsCondExp m₂ μ f fun _ ↦ ∫ x, f x ∂μ := by
  have h_eq (s : Set Ω) (hs : s ∈ m₂) : μ.real s • ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
    rw [← memLp_one_iff_integrable] at hfint
    refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint hf
    · intro c t hmt _
      rw [Indep_iff] at hindp
      rw [integral_indicator (hle₁ hmt), setIntegral_const, smul_smul, measureReal_def,
        measureReal_def, ← ENNReal.toReal_mul,
        mul_comm, ← hindp _ _ hmt hs, setIntegral_indicator (hle₁ hmt), setIntegral_const,
        Set.inter_comm, measureReal_def]
    · intro u v _ huint hvint hu hv hu_eq hv_eq
      rw [memLp_one_iff_integrable] at huint hvint
      rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
        integral_add' huint.integrableOn hvint.integrableOn]
    · have h_integral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x, (f : Ω → E) x ∂μ := by
        simpa using! continuous_integral.comp
          (ContinuousLinearMap.continuous (Submodule.subtypeL _))
      have h_setIntegral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x in s, (f : Ω → E) x ∂μ := by
        simpa using! (continuous_setIntegral s).comp
          (ContinuousLinearMap.continuous (Submodule.subtypeL _))
      exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
    · intro u v huv _ hueq
      rwa [← integral_congr_ae huv, ←
        (setIntegral_congr_ae (hle₂ hs) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
      filter_upwards [huv] with x hx _ using hx
  refine ⟨aestronglyMeasurable_const, fun s hs _ ↦ ?_, fun s hs _ ↦ ?_⟩
  · rcases (le_top : μ s ≤ ∞).lt_or_eq with hμs | hμs
    · exact integrableOn_const hμs.ne
    have h_univ : μ Set.univ = ∞ := top_le_iff.mp (hμs ▸ measure_mono (Set.subset_univ s))
    have h_zero : ∫ x, f x ∂μ = 0 := by
      simpa [measureReal_def, h_univ] using (h_eq Set.univ m₂.univ_mem).symm
    simp [h_zero]
  · rw [setIntegral_const, h_eq s hs]

/-- If `m₁, m₂` are independent σ-algebras and `f` is an integrable `m₁`-measurable function, then
`𝔼[f | m₂] = 𝔼[f]`. -/
theorem condExp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) (hf : AEStronglyMeasurable[m₁] f μ)
    (hfint : Integrable f μ) (hindp : Indep m₁ m₂ μ) (h : HasUniqueCondExp m₂ μ f) :
    condExp m₂ μ f h = ((fun _ ↦ ∫ x, f x ∂μ : Ω → E) : (ae μ).Germ E) :=
  (isCondExp_integral_of_indep hle₁ hle₂ hf hfint hindp).condExp_eq h

end MeasureTheory

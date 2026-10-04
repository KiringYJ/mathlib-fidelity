/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution with location parameter `x₀` and scale parameter `γ`.

Note that we use "location" and "scale" to refer to these parameters in theorem names.

## Main definition

* `cauchyPDFReal`: the function `x₀ γ x ↦ π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹` for `γ ≠ 0`,
  which is the probability density function of a Cauchy distribution with location parameter `x₀`
  and scale parameter `γ`.
* `cauchyPDF`: `ℝ≥0∞`-valued pdf,
  `cauchyPDF x₀ γ hγ x = ENNReal.ofReal (cauchyPDFReal x₀ γ hγ x)`.
* `cauchyMeasure`: a Cauchy measure on `ℝ`, parametrized by a location parameter `x₀ : ℝ` and a
  scale parameter `γ : ℝ≥0`, defined as the measure with density `cauchyPDF x₀ γ hγ` with respect
  to the Lebesgue measure.

## Parameter domain

All three definitions take a proof `hγ : γ ≠ 0`, and `cauchyMeasure x₀ γ hγ` is a probability
measure. This is the exact parameter domain of the Cauchy distribution, whose scale parameter is
positive ([siegrist_random], §5.32): for `γ = 0` the density formula vanishes away from `x₀`, so
no probability measure has it as a density. The law of `x₀ + γ * Z` for a standard Cauchy random
variable `Z` is then the Dirac measure at `x₀`, which [siegrist_random] does not count as a Cauchy
distribution; such a degenerate law would be a separate object with its own specification and
source.

The proofs are explicit arguments without default values: a default would take the point in
`cauchyPDFReal x₀ γ x` as a proof.

## References

* [K. Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*][siegrist_random]
-/

@[expose] public section

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace ProbabilityTheory

section CauchyPDF

/-- The pdf of the Cauchy distribution with location parameter `x₀` and scale parameter `γ`,
defined for `γ ≠ 0`. -/
@[nolint unusedArguments]
noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (_hγ : γ ≠ 0) (x : ℝ) : ℝ :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

lemma cauchyPDFReal_def (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    cauchyPDFReal x₀ γ hγ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def

lemma cauchyPDFReal_def' (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    cauchyPDFReal x₀ γ hγ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by
  rw [cauchyPDFReal_def]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

/-- The pdf of the Cauchy distribution, as a function valued in `ℝ≥0∞`, defined for `γ ≠ 0`. -/
noncomputable def cauchyPDF (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ hγ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

lemma cauchyPDF_def (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    cauchyPDF x₀ γ hγ x = ENNReal.ofReal (cauchyPDFReal x₀ γ hγ x) := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]
lemma measurable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    Measurable (cauchyPDFReal x₀ γ hγ) := by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]
lemma stronglyMeasurable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    StronglyMeasurable (cauchyPDFReal x₀ γ hγ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]
lemma measurable_cauchyPDF (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    Measurable (cauchyPDF x₀ γ hγ) := by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]
lemma stronglyMeasurable_cauchyPDF (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    StronglyMeasurable (cauchyPDF x₀ γ hγ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

/-- `cauchyPDFReal` is positive. -/
lemma cauchyPDFReal_pos (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    0 < cauchyPDFReal x₀ γ hγ x := by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDFReal_pos

lemma integral_cauchyPDFReal_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫ x, cauchyPDFReal x₀ γ hγ x = 1 := by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : ℝ ↦ (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : ℝ ↦ (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := integral_cauchyPDFReal_eq_one

@[fun_prop]
lemma integrable_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    Integrable (cauchyPDFReal x₀ γ hγ) := by
  apply Integrable.of_integral_ne_zero
  simp [integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

/-- The pdf of the Cauchy distribution integrates to 1. -/
@[simp]
lemma lintegral_cauchyPDF_eq_one (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    ∫⁻ x, cauchyPDF x₀ γ hγ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x ↦ (cauchyPDFReal_pos x₀ hγ x).le) (by fun_prop),
    integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one := lintegral_cauchyPDF_eq_one

end CauchyPDF

section CauchyMeasure

/-- The Cauchy distribution on `ℝ` with location parameter `x₀` and scale parameter `γ`, defined
for `γ ≠ 0`. -/
noncomputable def cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) : Measure ℝ :=
  volume.withDensity (cauchyPDF x₀ γ hγ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure

instance instIsProbabilityMeasure_cauchyMeasure (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) :
    IsProbabilityMeasure (cauchyMeasure x₀ γ hγ) where
  measure_univ := by simp [cauchyMeasure, lintegral_cauchyPDF_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

end CauchyMeasure

end ProbabilityTheory

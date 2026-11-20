/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.CondVar


/-!
# Distributions on two values

This file proves a few lemmas about random variables that take at most two values: the integral of
such a random variable, its conditional variance, and its variance.
-/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : SigmaAlgebra Ω} {X : Ω → ℝ} {μ : Measure Ω}

/-- If an `AEMeasurable` function is ae equal to `0` or `1`, then its integral is equal to the
measure of the set where it equals `1`. -/
lemma integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ∫ ω, X ω ∂μ = μ.real {ω | X ω = 1} := by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop, by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

/-- If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
lemma integral_one_sub_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : ∫ ω, 1 - X ω ∂μ = μ.real {ω | X ω = 0} := by
  calc
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

end MeasureTheory


namespace ProbabilityTheory
variable {Ω : Type*} {m₀ m : SigmaAlgebra Ω} {μ : Measure[m₀] Ω} {X g : Ω → ℝ}

/-- If a random variable is ae equal to `0` or `1` and `g` is a conditional expectation of it given
a sub-σ-algebra, then `g * (1 - g)`, the product of the conditional probabilities that it equals `1`
and that it equals `0`, is a conditional variance of it. -/
theorem isCondVar_of_ae_eq_zero_or_one (hm : m ≤ m₀) (hX : Integrable X μ)
    (hX01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) (hg : IsCondExp m μ X g) :
    IsCondVar m μ X (g * (1 - g)) := by
  have hX_sq : X ^ 2 =ᵐ[μ] X := by
    filter_upwards [hX01] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hX₂ : MemLp X 2 μ := (memLp_two_iff_integrable_sq hX.1).2 (hX.congr hX_sq.symm)
  refine (isCondVar_condExp_sq_sub_sq_condExp hm hX hX₂ hg (hg.congr_left hX_sq.symm)).congr_right
    (.of_forall fun ω ↦ ?_)
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply]
  ring

/-- If a random variable is ae equal to `0` or `1`, then its conditional variance is the product of
the conditional probabilities that it equals `1` and that it equals `0`:
`Var[X; μ | m] = μ[X | m] * μ[1 - X | m]`. -/
theorem condVar_of_ae_eq_zero_or_one (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : AEMeasurable X μ)
    (hX01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) (h : HasCondVar m μ X)
    (h' : HasUniqueCondExp m μ (1 - X)) :
    condVar m μ X h = condExp m μ X h.hasUniqueCondExp * condExp m μ (1 - X) h' := by
  have hX_int : Integrable X μ := .of_bound hX.aestronglyMeasurable 1 <| by
    filter_upwards [hX01]
    rintro ω (hω | hω) <;> simp [hω]
  obtain ⟨g, hg⟩ := h.hasUniqueCondExp.exists_isCondExp
  have h_one_sub : IsCondExp m μ (1 - X) (1 - g) :=
    (isCondExp_const 1).sub hg (integrable_const 1) hX_int
  rw [(isCondVar_of_ae_eq_zero_or_one hm hX_int hX01 hg).condVar_eq h, hg.condExp_eq,
    h_one_sub.condExp_eq, Filter.Germ.coe_mul]

/-- If a random variable is ae equal to `0` or `1`, then its variance is the product of
the probabilities that it's equal to `0` and that it's equal to `1`. -/
lemma variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  have hX_bdd : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ 1 := by
    filter_upwards [hX]
    rintro ω (hω | hω) <;> simp [hω]
  have hX_int : Integrable X μ := .of_bound hXmeas.aestronglyMeasurable 1 hX_bdd
  have hX₂ : MemLp X 2 μ := .of_bound hXmeas.aestronglyMeasurable 1 hX_bdd
  -- given the trivial σ-algebra, the mean is a conditional expectation and the variance is a
  -- conditional variance
  have hg : IsCondExp ⊥ μ X fun _ ↦ ∫ ω, X ω ∂μ := by
    simpa only [average_eq_integral] using isCondExp_bot (μ := μ) hX_int
  have h_var : IsCondVar ⊥ μ X fun _ ↦ (∫ ω, X ω ∂μ) * (1 - ∫ ω, X ω ∂μ) :=
    isCondVar_of_ae_eq_zero_or_one bot_le hX_int hX hg
  have h_eq : Var[X; μ] = (∫ ω, X ω ∂μ) * (1 - ∫ ω, X ω ∂μ) := by
    simpa [average_eq_integral, ← variance_eq_integral hXmeas] using
      (isCondVar_bot hX₂).ae_eq bot_le hX_int hX₂ h_var
  have h_one_sub : 1 - ∫ ω, X ω ∂μ = μ.real {ω | X ω = 0} := by
    rw [← integral_one_sub_of_ae_eq_zero_or_one hXmeas hX,
      integral_sub (integrable_const 1) hX_int]
    simp
  rw [h_eq, h_one_sub, integral_of_ae_eq_zero_or_one hXmeas hX, mul_comm]

end ProbabilityTheory

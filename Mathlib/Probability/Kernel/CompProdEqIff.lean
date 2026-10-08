/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Condition for two kernels to be equal almost everywhere

We prove that two finite kernels `κ, η : Kernel α β` are `μ`-a.e. equal for a σ-finite measure `μ`
iff the composition-products `μ ⊗ₘ κ` and `μ ⊗ₘ η` are equal.
The result requires `α` to be countable or `β` to be a countably generated measurable space.

## Main statements

* `compProd_eq_iff`: `μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η`

-/

public section

open ProbabilityTheory MeasureTheory

open scoped ENNReal

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {μ : Measure α} {κ : Kernel α β}
  {f : α → β → ℝ≥0∞}

namespace ProbabilityTheory.Kernel

variable {η : Kernel α β} [SigmaAlgebra.CountableOrCountablyGenerated α β]

/-- The case of `ae_eq_of_compProd_eq` for a finite measure. -/
private lemma ae_eq_of_compProd_eq_of_isFiniteMeasure [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (h : μ ⊗ₘ κ = μ ⊗ₘ η) :
    κ =ᵐ[μ] η := by
  have h_ac : ∀ᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : ∀ᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices ∀ᵐ a ∂μ, ∀ᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x ↦ κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ ⊗ₘ η
  _ = (μ ⊗ₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq, Measure.compProd_withDensity, withDensity_apply _ hs]
    fun_prop
  _ = (μ ⊗ₘ η) s := by rw [h]

/-- Two finite kernels whose composition-products with a σ-finite measure `μ` agree are `μ`-a.e.
equal. Reweighting `μ` by a positive function with a finite integral reduces this to a finite
measure, since the weight changes neither the null sets nor the equality of the
composition-products. -/
lemma ae_eq_of_compProd_eq [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ = μ ⊗ₘ η) :
    κ =ᵐ[μ] η := by
  obtain ⟨w, hw_pos, hw, hw_int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  have hw' : Measurable fun a ↦ (w a : ℝ≥0∞) := hw.coe_nnreal_ennreal
  have : IsFiniteMeasure (μ.withDensity fun a ↦ (w a : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity (hw_int.trans ENNReal.one_lt_top).ne
  refine (withDensity_absolutelyContinuous' hw'.aemeasurable
    (ae_of_all _ fun a ↦ ENNReal.coe_ne_zero.2 (hw_pos a).ne')).ae_le
    (ae_eq_of_compProd_eq_of_isFiniteMeasure ?_)
  rw [Measure.withDensity_compProd hw', Measure.withDensity_compProd hw', h]

/-- Two finite kernels `κ` and `η` are `μ`-a.e. equal for a σ-finite measure `μ` iff the
composition-products `μ ⊗ₘ κ` and `μ ⊗ₘ η` are equal. -/
lemma compProd_eq_iff [SigmaFinite μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η :=
  ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

end ProbabilityTheory.Kernel

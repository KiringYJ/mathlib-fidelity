/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Posterior

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Bayes estimator

Let `Θ` be a parameter space, `𝓧` a data space, `𝓨` a prediction space, `P : Kernel Θ 𝓧` a
data generating kernel, `π` a prior on the parameter space, and `ℓ : Θ → 𝓨 → ℝ≥0∞` a loss function.

An estimator (a `Kernel 𝓧 𝓨`) is said to be a Bayes estimator if it attains the Bayes risk for
the estimation problem.
It can be written as a measurable function `x ↦ argmin_y η(x)[θ ↦ ℓ θ y]`
for `(P ∘ₘ π)`-almost every `x`, where `η` is a representative of the posterior `P†π`, whenever we
can select the argmin in a measurable way. Since two representatives of the posterior agree
`(P ∘ₘ π)`-almost everywhere, this does not depend on the representative.

## Main definitions

* `IsBayesEstimator`: an estimator is a Bayes estimator if it attains the Bayes risk for the prior.
* `IsArgminEstimator`: a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
  if for every representative `η` of `P†π` and `(P ∘ₘ π)`-almost every `x` the value `f x` belongs
  to `argmin_y η(x)[θ ↦ ℓ θ y]`.
* `HasArgminEstimator`: the estimation problem admits an argmin estimator.
  That is, we can choose the argmin of the posterior expected loss in a measurable way.

## Main statements

* `lintegral_iInf_posterior_le_bayesRisk`: the Bayes risk with respect to a prior is bounded
  from below by the integral over the data (with distribution `P ∘ₘ π`) of the infimum over the
  possible predictions `y` of the posterior loss `∫⁻ θ, ℓ θ y ∂(η x)`, for every Markov
  representative `η` of `P†π`:
  `∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π`
* `IsArgminEstimator.isBayesEstimator`: an argmin Bayes estimator is a Bayes estimator.
  That is, it minimizes the Bayesian risk.
* `HasArgminEstimator.bayesRisk_eq`: if the estimation problem admits an argmin estimator,
  then the Bayesian risk attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π)`
  for every Markov representative `η` of `P†π`.

## TODO

Once Mathlib has measurable selection theorems, we will be able to prove `HasArgminEstimator` under
general conditions on the measurable spaces `𝓧` and/or `𝓨`.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : SigmaAlgebra Θ} {m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ] {η : Kernel 𝓧 Θ}

/-- The average risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((η × κ) ∘ P ∘ π)[(θ, y) ↦ ℓ θ y]` for every Markov
representative `η` of the posterior `P†π`. -/
lemma avgRisk_eq_lintegral_posterior_prod
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel η]
    (hη : η ∈ P†π) :
    avgRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂((η ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  rw [avgRisk, ← Measure.lintegral_compProd (f := fun θy ↦ ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π ⊗ₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π ⊗ₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ (η ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp hη]
  _ = (η ×ₖ κ) ∘ₘ P ∘ₘ π := by
    rw [Measure.comp_assoc]
    apply Measure.comp_congr
    apply ae_of_all
    intro x
    apply DFunLike.congr_fun
    rw [Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]

lemma avgRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel η]
    (hη : η ∈ P†π) :
    avgRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂η x ∂κ x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_posterior_prod hl P κ π hη,
    Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_productBySections_symm' _ (by fun_prop)]

lemma lintegral_iInf_posterior_le_avgRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel η]
    (hη : η ∈ P†π) :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π) ≤ avgRisk ℓ P κ π := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl P κ π hη]
  gcongr with x
  exact iInf_le_lintegral _

lemma lintegral_iInf_posterior_le_bayesRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel η] (hη : η ∈ P†π) :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π :=
  le_iInf₂ fun κ _ ↦ lintegral_iInf_posterior_le_avgRisk hl P κ π hη

end Posterior

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  avgRisk ℓ P κ π = bayesRisk ℓ P π

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 → 𝓨} [IsFiniteKernel P] [IsFiniteMeasure π]

/-- We say that a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
with respect to the prior `π` if for every representative `η` of the posterior `P†π` and
`(P ∘ₘ π)`-almost every `x` it is of the form `x ↦ argmin_y η(x)[θ ↦ ℓ θ y]`. Since two
representatives agree `(P ∘ₘ π)`-almost everywhere, it suffices to check one of them
(`ProbabilityTheory.IsArgminEstimator.of_mem`). -/
structure IsArgminEstimator {𝓨 : Type*} [SigmaAlgebra 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] (f : 𝓧 → 𝓨) : Prop where
  measurable : Measurable f
  property : ∀ η : Kernel 𝓧 Θ, η ∈ P†π →
    ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂η x = ⨅ y, ∫⁻ θ, ℓ θ y ∂η x

/-- A measurable function that is an argmin of the posterior expected loss for one representative
of the posterior is an argmin estimator. -/
lemma IsArgminEstimator.of_mem {η : Kernel 𝓧 Θ} (hf : Measurable f) (hη : η ∈ P†π)
    (h : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂η x = ⨅ y, ∫⁻ θ, ℓ θ y ∂η x) :
    IsArgminEstimator ℓ P π f where
  measurable := hf
  property η' hη' := by
    filter_upwards [h, Kernel.AEClass.eventuallyEq_of_mem hη' hη] with x hx hx'
    rw [hx']
    exact hx

/-- Given an argmin estimator `f`, we can define a deterministic kernel. -/
protected noncomputable
abbrev IsArgminEstimator.kernel (h : IsArgminEstimator ℓ P π f) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/-- The risk of an argmin estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂η x ∂(P ∘ₘ π)` for every Markov representative `η` of `P†π`. -/
lemma IsArgminEstimator.avgRisk_eq_lintegral_iInf (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) {η : Kernel 𝓧 Θ} [IsMarkovKernel η]
    (hη : η ∈ P†π) :
    avgRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂η x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl P _ π hη]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property η hη] with x hx
  rwa [Kernel.lintegral_deterministic' _ (by fun_prop)]

/-- An argmin estimator is a Bayes estimator: that is, it minimizes the Bayesian risk. -/
lemma IsArgminEstimator.isBayesEstimator (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  obtain ⟨η, _, hη⟩ := exists_isMarkovKernel_mem_posterior (κ := P) (μ := π)
  refine le_antisymm ?_ (bayesRisk_le_avgRisk _ _ _ _)
  rw [hf.avgRisk_eq_lintegral_iInf hl hη]
  exact lintegral_iInf_posterior_le_bayesRisk hl _ _ hη

/-- The estimation problem admits an argmin estimator with respect to the prior `π`.
That is, we can choose the argmin of the posterior expected loss in a measurable way. -/
structure HasArgminEstimator {𝓨 : Type*} [SigmaAlgebra 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Prop where
  exists_isArgminEstimator : ∃ f : 𝓧 → 𝓨, IsArgminEstimator ℓ P π f

namespace HasArgminEstimator

/-- If the estimation problem admits an argmin estimator, then the Bayesian risk attains the risk
lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π)` for every Markov representative `η` of
`P†π`. -/
lemma bayesRisk_eq (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ P π)
    {η : Kernel 𝓧 Θ} [IsMarkovKernel η] (hη : η ∈ P†π) :
    bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(η x) ∂(P ∘ₘ π) := by
  obtain ⟨f, hf⟩ := h.exists_isArgminEstimator
  rw [← hf.isBayesEstimator hl, hf.avgRisk_eq_lintegral_iInf hl hη]

end HasArgminEstimator

end ProbabilityTheory

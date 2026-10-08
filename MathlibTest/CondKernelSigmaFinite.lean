import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Posterior

/-!
# Conditional kernels of measures with a σ-finite first marginal

These tests check that a measure on a product whose first marginal is σ-finite has a unique
conditional kernel, including infinite measures; that two finite kernels whose composition-products
with a σ-finite measure agree are equal almost everywhere; that the conditional distribution exists
when the law of the conditioning variable is σ-finite and the posterior exists when the law of the
data is σ-finite, which admits an infinite prior; and that instance search finds no conditional
kernel for planar Lebesgue measure, whose first marginal is not σ-finite and which has none
(`Counterexamples/CondKernel.lean`).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### The instance for finite measures is generalized -/

/-- info: Unknown constant `MeasureTheory.Measure.hasUniqueCondKernel_of_isFiniteMeasure` -/
#guard_msgs in
#check_failure MeasureTheory.Measure.hasUniqueCondKernel_of_isFiniteMeasure

/-! ### Measures with a σ-finite first marginal -/

example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] : ρ.HasUniqueCondKernel := inferInstance

-- An infinite measure whose first marginal, Lebesgue measure, is σ-finite.
example : ((volume : Measure ℝ).prod (gaussianReal 0 1)).HasUniqueCondKernel := inferInstance

example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] (η : Kernel ℝ ℝ) [IsFiniteKernel η] :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η :=
  Measure.mem_condKernel_iff

example (μ : Measure ℝ) [SigmaFinite μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    κ ∈ (μ ⊗ₘ κ).condKernel :=
  Measure.mem_condKernel_compProd μ κ

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : κ ∈ ((volume : Measure ℝ) ⊗ₘ κ).condKernel :=
  Measure.mem_condKernel_compProd volume κ

example {μ : Measure ℝ} [SigmaFinite μ] {κ η : Kernel ℝ ℝ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ = μ ⊗ₘ η) : κ =ᵐ[μ] η :=
  Kernel.ae_eq_of_compProd_eq h

example {κ η : Kernel ℝ ℝ} [IsFiniteKernel κ] [IsFiniteKernel η] :
    (volume : Measure ℝ) ⊗ₘ κ = volume ⊗ₘ η ↔ κ =ᵐ[volume] η :=
  Kernel.compProd_eq_iff

-- The conditional cdf of a composition-product with a σ-finite measure is also unique.
example (μ : Measure ℝ) [SigmaFinite μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    HasUniqueCondCDF (μ ⊗ₘ κ) :=
  inferInstance

/-! ### Within σ-finite measures, the σ-finite first marginal is necessary -/

example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ] : ρ.HasUniqueCondKernel ↔ SigmaFinite ρ.fst :=
  Measure.hasUniqueCondKernel_iff_sigmaFinite_fst

example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ] (η : Kernel ℝ ℝ) [IsMarkovKernel η]
    [ρ.IsCondKernel η] : SigmaFinite ρ.fst :=
  Measure.IsCondKernel.sigmaFinite_fst η

/-! ### The conditional distribution of a σ-finite law -/

example {α : Type*} {mα : SigmaAlgebra α} {μ : Measure α} {X Y : α → ℝ} (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [SigmaFinite (μ.map X hX)] (η : Kernel ℝ ℝ) [IsFiniteKernel η] :
    η ∈ condDistrib Y X μ ↔ μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η :=
  mem_condDistrib_iff hX hY

/-! ### The posterior for a σ-finite law of the data -/

-- An infinite prior, Lebesgue measure.
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ volume)] :
    ∃ η : Kernel ℝ ℝ, IsMarkovKernel η ∧ η ∈ κ†volume :=
  exists_isMarkovKernel_mem_posterior

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ volume)] (η : Kernel ℝ ℝ)
    [IsFiniteKernel η] :
    η ∈ κ†volume ↔ (κ ∘ₘ volume) ⊗ₘ η = ((volume : Measure ℝ) ⊗ₘ κ).map Prod.swap :=
  mem_posterior_iff

-- A concrete infinite prior: the identity kernel and Lebesgue measure.
example :
    ∃ η : Kernel ℝ ℝ, IsMarkovKernel η ∧ η ∈ (Kernel.id : Kernel ℝ ℝ)†(volume : Measure ℝ) :=
  exists_isMarkovKernel_mem_posterior

/-! ### Planar Lebesgue measure has no conditional kernel -/

/--
error: failed to synthesize instance of type class
  ℙ.HasUniqueCondKernel

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Kernel.AEClass (ae (volume : Measure (ℝ × ℝ)).fst) ℝ :=
  (volume : Measure (ℝ × ℝ)).condKernel

end

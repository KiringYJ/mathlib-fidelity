import Mathlib.Probability.Decision.BayesEstimator
import Mathlib.Probability.HasCondDistrib

/-!
# Conditional distributions and posteriors as almost-everywhere classes

These tests check that `ProbabilityTheory.condDistrib` and `ProbabilityTheory.posterior` are classes
of kernels modulo null sets, so that no chosen kernel, with its Markov instance and lemmas, is
public; that a finite kernel represents them exactly when it disintegrates the corresponding joint
law, which for `condDistrib` is the relation `HasCondDistrib`, that Markov representatives exist,
and that every Markov representative of a conditional distribution computes conditional
probabilities; that argmin estimators are checked on a single representative of the posterior and
that no argmin estimator is chosen from their existence; that a kernel that agrees with a
representative except on a null set is again a representative; and that a kernel that is wrong on
a set of positive measure is not.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-! ### No chosen conditional distribution or posterior is public -/

/-- error: Unknown identifier `ProbabilityTheory.instIsMarkovKernelCondDistrib` -/
#guard_msgs in
#check ProbabilityTheory.instIsMarkovKernelCondDistrib

/-- error: Unknown identifier `ProbabilityTheory.measurable_condDistrib` -/
#guard_msgs in
#check ProbabilityTheory.measurable_condDistrib

/-- error: Unknown identifier `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd` -/
#guard_msgs in
#check ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd

/-- error: Unknown identifier `ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd` -/
#guard_msgs in
#check ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd

/--
error: Unknown identifier `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`
-/
#guard_msgs in
#check ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable

/-- error: Unknown identifier `ProbabilityTheory.stronglyMeasurable_integral_condDistrib` -/
#guard_msgs in
#check ProbabilityTheory.stronglyMeasurable_integral_condDistrib

/-- error: Unknown constant `MeasureTheory.StronglyMeasurable.integral_condDistrib` -/
#guard_msgs in
#check MeasureTheory.StronglyMeasurable.integral_condDistrib

/-- error: Unknown identifier `ProbabilityTheory.instIsMarkovKernelPosterior` -/
#guard_msgs in
#check ProbabilityTheory.instIsMarkovKernelPosterior

/-- error: Unknown identifier `ProbabilityTheory.ae_eq_posterior_of_compProd_eq` -/
#guard_msgs in
#check ProbabilityTheory.ae_eq_posterior_of_compProd_eq

/-- error: Unknown identifier `ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp` -/
#guard_msgs in
#check ProbabilityTheory.ae_eq_posterior_of_compProd_eq_swap_comp

/-- error: Unknown identifier `ProbabilityTheory.integrable_toReal_condDistrib` -/
#guard_msgs in
#check ProbabilityTheory.integrable_toReal_condDistrib

/-! ### No argmin estimator is chosen from their existence -/

/-- error: Unknown constant `ProbabilityTheory.HasArgminEstimator.argminEstimator` -/
#guard_msgs in
#check ProbabilityTheory.HasArgminEstimator.argminEstimator

/--
error: Unknown constant `ProbabilityTheory.HasArgminEstimator.isArgminEstimator_argminEstimator`
-/
#guard_msgs in
#check ProbabilityTheory.HasArgminEstimator.isArgminEstimator_argminEstimator

/-! ### Conditional distributions -/

section CondDistrib

variable {α β Ω : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}

-- A finite kernel represents `condDistrib Y X μ` exactly when it disintegrates the joint law.
example (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (η : Kernel β Ω) [IsFiniteKernel η] :
    η ∈ condDistrib Y X μ ↔ μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η :=
  mem_condDistrib_iff hX hY

-- Among finite kernels, the representatives are the conditional distributions in the sense of
-- `HasCondDistrib`.
example (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ) (η : Kernel β Ω) [IsFiniteKernel η] :
    η ∈ condDistrib Y X μ hXY ↔ HasCondDistrib Y X η μ :=
  mem_condDistrib_iff_hasCondDistrib hXY

-- Every Markov representative computes conditional probabilities.
example (hX : Measurable X) (hY : Measurable Y) {η : Kernel β Ω} [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun a ↦ (η (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | SigmaAlgebra.comap X ‹_›⟧ :=
  condDistrib_ae_eq_condExp hX hY hη hs

-- The identity kernel represents the conditional distribution of a random variable given itself.
example (hY : AEMeasurable Y μ) : Kernel.id ∈ condDistrib Y Y μ :=
  id_mem_condDistrib_self hY

-- Equal laws of `(X, Y)` give the same representatives, for every kernel.
example {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ) (η : Kernel β Ω) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y' X' μ (hXY.congr (hX.prodMk hY)) :=
  condDistrib_congr hY hX hXY

end CondDistrib

/-! ### Posteriors -/

section Posterior

variable {Ω 𝓧 𝓨 : Type*} [SigmaAlgebra Ω] [SigmaAlgebra 𝓧] [SigmaAlgebra 𝓨] [StandardBorelSpace Ω]
  [Nonempty Ω] {κ : Kernel Ω 𝓧} [IsFiniteKernel κ] {μ : Measure Ω} [IsFiniteMeasure μ]

example : Kernel.AEClass (ae (κ ∘ₘ μ)) Ω := κ†μ

example : ∃ η : Kernel 𝓧 Ω, IsMarkovKernel η ∧ η ∈ κ†μ := exists_isMarkovKernel_mem_posterior

-- A finite kernel represents the posterior exactly when it has its defining property.
example (η : Kernel 𝓧 Ω) [IsFiniteKernel η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  mem_posterior_iff

example (μ : Measure Ω) [IsFiniteMeasure μ] : Kernel.id ∈ (Kernel.id : Kernel Ω Ω)†μ :=
  id_mem_posterior_id μ

-- A kernel that agrees with a representative `(κ ∘ₘ μ)`-almost everywhere is a representative.
example {η η' : Kernel 𝓧 Ω} (hη : η ∈ κ†μ) (h : ∀ᵐ x ∂(κ ∘ₘ μ), η x = η' x) : η' ∈ κ†μ :=
  Kernel.AEClass.mem_of_eventuallyEq hη h

-- An argmin estimator is checked on a single representative of the posterior.
example {ℓ : Ω → 𝓨 → ℝ≥0∞} {f : 𝓧 → 𝓨} {η : Kernel 𝓧 Ω} (hf : Measurable f) (hη : η ∈ κ†μ)
    (h : ∀ᵐ x ∂(κ ∘ₘ μ), ∫⁻ θ, ℓ θ (f x) ∂η x = ⨅ y, ∫⁻ θ, ℓ θ y ∂η x) :
    IsArgminEstimator ℓ κ μ f :=
  IsArgminEstimator.of_mem hf hη h

-- The Bayes risk of a problem that admits an argmin estimator is computed from any Markov
-- representative of the posterior, without choosing an argmin estimator.
example {ℓ : Ω → 𝓨 → ℝ≥0∞} (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ κ μ)
    {η : Kernel 𝓧 Ω} [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    bayesRisk ℓ κ μ = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(η x) ∂(κ ∘ₘ μ) :=
  h.bayesRisk_eq hl hη

end Posterior

/-! ### Rejection of kernels that are wrong on a set of positive measure -/

-- The conditional distribution of a random variable given itself under `dirac 0` is `dirac 0` at
-- the atom `0`, so the constant kernel `dirac 1` does not represent it.
example : Kernel.const ℝ (Measure.dirac 1) ∉
    condDistrib (id : ℝ → ℝ) id (Measure.dirac 0) := by
  intro h
  have h' := Kernel.AEClass.eventuallyEq_of_mem h (id_mem_condDistrib_self aemeasurable_id)
  rw [Measure.map_id, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure] at h'
  have h1 := congrArg (fun ν : Measure ℝ ↦ ν {0}) h'
  simp [Kernel.const_apply, Kernel.id_apply, Measure.dirac_apply'] at h1

-- The posterior of the identity kernel for the prior `dirac 0` is `dirac 0` at the atom `0`, so
-- the constant kernel `dirac 1` does not represent it.
example : Kernel.const ℝ (Measure.dirac 1) ∉ (Kernel.id : Kernel ℝ ℝ)†(Measure.dirac 0) := by
  intro h
  have h' := Kernel.AEClass.eventuallyEq_of_mem h (id_mem_posterior_id _)
  rw [Measure.id_comp, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure] at h'
  have h1 := congrArg (fun ν : Measure ℝ ↦ ν {0}) h'
  simp [Kernel.const_apply, Kernel.id_apply, Measure.dirac_apply'] at h1

end

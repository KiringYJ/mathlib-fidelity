import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Strict normalization of finite measures

These tests ensure that `FiniteMeasure.normalize` exposes its nonzero-mass obligation, that the
default discharger finds routine evidence without ever choosing the measure itself, and that the
normalization API transfers results about probability measures to finite measures.
-/

open MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

variable {Ω : Type*} [SigmaAlgebra Ω]

/-! ### The domain is enforced -/

/--
error: could not synthesize default value for parameter 'hμ' using tactics
---
error: FiniteMeasure.normalize needs a proof that the finite measure is nonzero
Ω : Type u_1
inst✝ : SigmaAlgebra Ω
μ : FiniteMeasure Ω
⊢ μ ≠ 0
-/
#guard_msgs in
example (μ : FiniteMeasure Ω) : ProbabilityMeasure Ω :=
  μ.normalize

example : True := by
  fail_if_success
    let _P : ProbabilityMeasure Ω := (0 : FiniteMeasure Ω).normalize
  trivial

set_option linter.unusedVariables false in
example (μ ν : FiniteMeasure Ω) (hν : ν ≠ 0) : True := by
  fail_if_success
    let _P : ProbabilityMeasure Ω := μ.normalize
  trivial

-- No ambient instance certifies an arbitrary or zero finite measure as nonzero.
set_option linter.unusedVariables false in
example (μ : FiniteMeasure Ω) : True := by
  fail_if_success
    have : NeZero μ := inferInstance
  trivial

example : True := by
  fail_if_success
    have : NeZero (0 : FiniteMeasure Ω) := inferInstance
  trivial

-- The default discharger never chooses the measure from a hypothesis.
/--
error: could not synthesize default value for parameter 'hμ' using tactics
---
error: FiniteMeasure.normalize: the measure to normalize is not determined; pass it explicitly
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (ν₁ ν₂ : FiniteMeasure Ω) (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) : ProbabilityMeasure Ω :=
  FiniteMeasure.normalize _

/-! ### Routine evidence is found -/

example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) : ProbabilityMeasure Ω :=
  μ.normalize

example (P : ProbabilityMeasure Ω) : P.toFiniteMeasure.normalize = P := by
  simp

example (μs : ℕ → FiniteMeasure Ω) (hμs : ∀ n, μs n ≠ 0) : ℕ → ProbabilityMeasure Ω :=
  fun n ↦ (μs n).normalize

example (S : Set (FiniteMeasure Ω)) (hS : ∀ ν ∈ S, ν ≠ 0) (μ : FiniteMeasure Ω) (hμS : μ ∈ S) :
    ProbabilityMeasure Ω :=
  μ.normalize

example (μs : ℕ → FiniteMeasure Ω) [∀ n, NeZero (μs n)] : ℕ → ProbabilityMeasure Ω :=
  fun n ↦ (μs n).normalize

example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) (c : ℝ≥0) (hc : c ≠ 0) :
    (c • μ).normalize (smul_ne_zero hc hμ) = μ.normalize hμ :=
  FiniteMeasure.normalize_smul hc hμ

-- No `Nonempty` instance is needed: a nonzero finite measure lives on a nonempty space.
example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) : Nonempty Ω :=
  (μ.normalize hμ).nonempty

/-! ### Evaluation, proof independence and rewriting -/

example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) (s : Set Ω) : (μ.normalize) s = μ.mass⁻¹ * μ s := by
  simp

example (μ : FiniteMeasure Ω) (h₁ h₂ : μ ≠ 0) : μ.normalize h₁ = μ.normalize h₂ :=
  rfl

example (μ : FiniteMeasure Ω) (h₁ h₂ : μ ≠ 0) (s : Set Ω) :
    μ.normalize h₁ s = μ.mass⁻¹ * μ s := by
  rw [FiniteMeasure.normalize_apply h₂]

example (μ ν : FiniteMeasure Ω) (h : μ = ν) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    μ.normalize hμ = ν.normalize hν := by
  simp only [h]

example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) (s : Set Ω) :
    μ.mass * μ.normalize hμ s = μ s := by
  simp [hμ]

example (μ : FiniteMeasure Ω) (hμ : μ ≠ 0) (f : Ω → ℝ) :
    ∫ x, f x ∂(μ.normalize hμ : Measure Ω) = (μ.mass : ℝ)⁻¹ * ∫ x, f x ∂(μ : Measure Ω) := by
  simp [NNReal.smul_def]

/-! ### Transfer between probability measures and finite measures -/

variable [TopologicalSpace Ω] [OpensSigmaAlgebra Ω]

example {γ : Type*} {F : Filter γ} {μ : FiniteMeasure Ω} {μs : γ → FiniteMeasure Ω}
    (hμ : μ ≠ 0) (hμs : ∀ i, μs i ≠ 0)
    (h_norm : Tendsto (fun i ↦ (μs i).normalize) F (𝓝 μ.normalize))
    (h_mass : Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass)) :
    Tendsto μs F (𝓝 μ) :=
  (FiniteMeasure.tendsto_normalize_iff_tendsto_of_forall_ne_zero hμ hμs).1 ⟨h_norm, h_mass⟩

-- A portmanteau implication for finite measures, obtained from the probability-measure version.
example [HasOuterApproxClosed Ω] {ι : Type*} {L : Filter ι} {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (h : Tendsto μs L (𝓝 μ)) {E : Set Ω}
    (hE : μ (frontier E) = 0) :
    Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hm : Tendsto (fun i ↦ (μs i).mass) L (𝓝 0) := by simpa using h.mass
    simpa using tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ ↦ zero_le) (fun i ↦ FiniteMeasure.apply_le_mass _ _)
  · rw [← tendsto_comap'_iff (i := ((↑) : {i // μs i ≠ 0} → ι)) (by
      rw [Subtype.range_coe_subtype]
      exact FiniteMeasure.eventually_ne_zero_of_tendsto h hμ)]
    have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      (FiniteMeasure.tendsto_normalize_of_tendsto h hμ) (E := E) (by simp [hE])
    have := (h.mass.comp tendsto_comap).mul key
    simpa only [Function.comp_def, FiniteMeasure.mass_mul_normalize_apply] using this

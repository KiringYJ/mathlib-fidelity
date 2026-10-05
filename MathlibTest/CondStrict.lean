import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strict conditional probability

These tests ensure that a measure is conditioned only on null-measurable sets of positive finite
measure, so that conditioning on a null set or on a set of infinite measure no longer gives the
zero measure, that the notation finds the routine evidence, and that the uniform measure on a set
and the uniform distribution exist only where conditioning does.
-/

open MeasureTheory ProbabilityTheory Set

/-- info: Unknown identifier `ProbabilityTheory.cond_eq_zero` -/
#guard_msgs in
#check_failure ProbabilityTheory.cond_eq_zero

/-- info: Unknown identifier `ProbabilityTheory.cond_empty` -/
#guard_msgs in
#check_failure ProbabilityTheory.cond_empty

/-- info: Unknown identifier `ProbabilityTheory.cond_eq_zero_of_meas_eq_zero` -/
#guard_msgs in
#check_failure ProbabilityTheory.cond_eq_zero_of_meas_eq_zero

/-- info: Unknown identifier `ProbabilityTheory.cond_isProbabilityMeasure_of_finite` -/
#guard_msgs in
#check_failure ProbabilityTheory.cond_isProbabilityMeasure_of_finite

/-- info: Unknown identifier `ProbabilityTheory.uniformOn_empty_meas` -/
#guard_msgs in
#check_failure ProbabilityTheory.uniformOn_empty_meas

/-- info: Unknown identifier `ProbabilityTheory.uniformOn_eq_zero` -/
#guard_msgs in
#check_failure ProbabilityTheory.uniformOn_eq_zero

/-- info: Unknown identifier `ProbabilityTheory.finite_of_uniformOn_ne_zero` -/
#guard_msgs in
#check_failure ProbabilityTheory.finite_of_uniformOn_ne_zero

/--
info: Unknown constant `MeasureTheory.pdf.IsUniform.pdf_eq_zero_of_measure_eq_zero_or_top`
-/
#guard_msgs in
#check_failure MeasureTheory.pdf.IsUniform.pdf_eq_zero_of_measure_eq_zero_or_top

variable {Ω : Type*} [SigmaAlgebra Ω] {μ : Measure Ω} {s t : Set Ω}

/-! Conditioning needs a set of positive finite measure. -/

/--
error: conditioning on this set needs a proof `IsConditionable μ s` that it is null-measurable and has positive finite measure
-/
#guard_msgs (substring := true) in
noncomputable example : Measure Ω := μ[|s]

/-- The empty set cannot be conditioned on; it was formerly mapped to the zero measure. -/
example : ¬IsConditionable μ ∅ := fun h ↦ h.measure_ne_zero measure_empty

/-- Lebesgue measure cannot be conditioned on the whole real line, whose measure is infinite; this
was formerly the zero measure. -/
example : ¬IsConditionable (volume : Measure ℝ) univ := fun h ↦ h.measure_ne_top (by simp)

/-! The notation finds the routine evidence. -/

example (hs : MeasurableSet s) (h₀ : μ s ≠ 0) (h : μ s ≠ ⊤) : IsProbabilityMeasure μ[|s] :=
  inferInstance

example [IsFiniteMeasure μ] (hs : MeasurableSet s) (h₀ : μ s ≠ 0) :
    μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) :=
  cond_apply (.of_isFiniteMeasure hs h₀) t

example [IsProbabilityMeasure μ] : μ[|univ] = μ := cond_univ μ

/-! Conditioning is defined on null-measurable sets, and concentrates on them. -/

example (hs : NullMeasurableSet s μ) (h₀ : μ s ≠ 0) (h : μ s ≠ ⊤) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_cond_mem ⟨hs, h₀, h⟩

/-! Bayes' theorem. -/

example (hs : IsConditionable μ s) (ht : IsConditionable μ t) :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t :=
  cond_eq_inv_mul_cond_mul hs ht

/-! The uniform measure on a set needs a finite nonempty measurable set. -/

/-- The counting measure cannot be conditioned on an infinite set; the uniform measure on `ℕ` was
formerly the zero measure. -/
example : ¬IsConditionable Measure.count (univ : Set ℕ) := fun h ↦
  infinite_univ (isConditionable_count_iff.1 h).2.1

example [MeasurableSingletonClass Ω] (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (uniformOn s (.count_of_finite hs hs')) :=
  inferInstance

example [MeasurableSingletonClass Ω] (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)] :
    uniformOn {ω} (.count_of_finite (finite_singleton ω) (singleton_nonempty ω)) t =
      if ω ∈ t then 1 else 0 :=
  uniformOn_singleton ω t _

/-! A uniform distribution needs a set of positive finite measure. -/

/-- No random variable is uniform on the real line; such a variable formerly had the zero law. -/
example {X : Ω → ℝ} {P : Measure Ω} : ¬pdf.IsUniform X univ P := fun h ↦
  h.isConditionable.measure_ne_top (by simp)

example {X : Ω → ℝ} {P : Measure Ω} (h : pdf.IsUniform X (Icc 0 1) P) : IsProbabilityMeasure P :=
  h.isProbabilityMeasure

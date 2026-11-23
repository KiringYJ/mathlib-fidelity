import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Kullback-Leibler divergence of σ-finite measures

These tests ensure that the Kullback-Leibler divergence is the I-divergence of σ-finite measures,
so that a measure of infinite mass no longer turns the mass correction into the value `0`, and that
measures that are not σ-finite have no divergence.
-/

open MeasureTheory InformationTheory

/-! The divergence needs σ-finite measures. -/

/--
error: failed to synthesize instance of type class
  SigmaFinite μ
-/
#guard_msgs (substring := true) in
noncomputable example {α : Type*} [SigmaAlgebra α] (μ ν : Measure α) : ENNReal := klDiv μ ν

/-! The zero measure has divergence `ν univ` from `ν`, which is `∞` for Lebesgue measure and
for the counting measure on `ℕ`. Their former divergence was `0`, because the mass correction
`ν.real univ` is `0` for a measure of infinite mass. -/

example : klDiv (0 : Measure ℝ) volume = ⊤ := by
  simp

example : klDiv (0 : Measure ℕ) Measure.count = ⊤ := by
  simp [Measure.count_apply_infinite Set.infinite_univ]

/-! For finite measures, the divergence is the corrected integral of the log-likelihood ratio. -/

example {α : Type*} [SigmaAlgebra α] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real Set.univ - μ.real Set.univ) :=
  klDiv_of_ac_of_integrable h h_int

/-! A σ-finite measure has divergence `0` from itself. -/

example : klDiv (volume : Measure ℝ) volume = 0 := klDiv_self _

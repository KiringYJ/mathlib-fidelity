import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Strict domain of the cumulative distribution function

These tests ensure that `ProbabilityTheory.cdf` is defined exactly on measures that are finite on
every ray `Iic x`, including infinite ones; that statements specific to finite or probability
measures require such a measure; that instance search finds routine evidence; and that the cdf is
`x ↦ μ.real (Iic x)` without normalization.
-/

open MeasureTheory Measure Set Filter
open ProbabilityTheory (cdf cdf_eq_real cdf_le_one cdf_le_measureReal_univ measure_cdf
  tendsto_cdf_atBot tendsto_cdf_atTop tendsto_cdf_atTop_measureReal_univ
  cdf_measure_stieltjesFunction cdf_expMeasure_eq isProbabilityMeasure_expMeasure expMeasure
  gaussianReal)
open scoped Topology ENNReal NNReal

noncomputable section

/-! ### The domain is enforced -/

-- Lebesgue measure on `ℝ` is sigma-finite and locally finite, but its rays have infinite measure.
/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic volume

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : StieltjesFunction ℝ := cdf (volume : Measure ℝ)

/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic count

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : StieltjesFunction ℝ := cdf (count : Measure ℝ)

/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic (volume.restrict (Iic 0))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : StieltjesFunction ℝ := cdf ((volume : Measure ℝ).restrict (Iic 0))

-- Neither local finiteness, s-finiteness, nor sigma-finiteness is the domain.
/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] : StieltjesFunction ℝ := cdf μ

/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [SigmaFinite μ] : StieltjesFunction ℝ := cdf μ

/--
error: failed to synthesize instance of type class
  IsFiniteMeasureOnIic μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [SFinite μ] : StieltjesFunction ℝ := cdf μ

-- Statements about finite measures need a finite measure.
/--
error: failed to synthesize instance of type class
  IsFiniteMeasure μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] : cdf μ 0 ≤ μ.real univ :=
  cdf_le_measureReal_univ μ 0

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure (cdf μ).measure

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] : IsFiniteMeasure (cdf μ).measure :=
  inferInstance

-- Statements about probability measures need more than a finite measure.
/--
error: failed to synthesize instance of type class
  IsZeroOrProbabilityMeasure μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsFiniteMeasure μ] : cdf μ 0 ≤ 1 :=
  cdf_le_one μ 0

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure μ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsFiniteMeasure μ] : Tendsto (cdf μ) atTop (𝓝 1) :=
  tendsto_cdf_atTop μ

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure (cdf μ).measure

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure ℝ) [IsFiniteMeasure μ] : IsProbabilityMeasure (cdf μ).measure :=
  inferInstance

/-! ### Infinite measures that are finite on rays -/

-- Lebesgue measure on `[0, ∞)` is infinite, but every ray `Iic x` has finite measure.
instance : IsFiniteMeasureOnIic ((volume : Measure ℝ).restrict (Ici 0)) :=
  ⟨fun x ↦ by
    rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ici]
    exact measure_Icc_lt_top⟩

example (x : ℝ) : cdf ((volume : Measure ℝ).restrict (Ici 0)) x = max x 0 := by
  rw [cdf_eq_real, measureReal_restrict_apply measurableSet_Iic, Iic_inter_Ici,
    Real.volume_real_Icc, sub_zero]

example : IsFiniteMeasureOnIic (cdf ((volume : Measure ℝ).restrict (Ici 0))).measure :=
  inferInstance

-- An unbounded Stieltjes function with limit 0 at -∞ is the cdf of its measure.
example : cdf (cdf ((volume : Measure ℝ).restrict (Ici 0))).measure =
    cdf ((volume : Measure ℝ).restrict (Ici 0)) :=
  cdf_measure_stieltjesFunction _ (tendsto_cdf_atBot _)

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (s : Set ℝ) :
    IsFiniteMeasureOnIic (μ.restrict s) :=
  inferInstance

example (μ ν : Measure ℝ) [IsFiniteMeasureOnIic μ] [IsFiniteMeasureOnIic ν] (x : ℝ) :
    cdf (μ + ν) x = cdf μ x + cdf ν x := by
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real, measureReal_add_apply]

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (c : ℝ≥0) (x : ℝ) :
    cdf (c • μ) x = c * cdf μ x := by
  simp [cdf_eq_real]

-- Automation finds the finiteness of rays.
example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (x : ℝ) : μ (Iic x) ≠ ∞ := by
  finiteness

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (x : ℝ) : μ (Iic x) < ∞ := by
  finiteness

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (x : ℝ) :
    ENNReal.ofReal (μ.real (Iic x)) = μ (Iic x) := by
  simp

-- The class also applies to a measure on a sigma-algebra other than the last local one.
example {α : Type*} [Preorder α] {m m0 : SigmaAlgebra α} (hm : m ≤ m0) (μ : @Measure α m0)
    [IsFiniteMeasure μ] : IsFiniteMeasureOnIic (μ.trim hm) :=
  inferInstance

/-! ### Routine evidence is found for finite and probability measures -/

example (x : ℝ) : cdf (gaussianReal 0 1) x ≤ 1 :=
  cdf_le_one _ x

example {Ω : Type*} [SigmaAlgebra Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (x : ℝ) :
    cdf (P.map X) x = P.real (X ⁻¹' Iic x) := by
  rw [cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]

example {α : Type*} [SigmaAlgebra α] (κ : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] (a : α) :
    Tendsto (cdf (κ a)) atTop (𝓝 1) :=
  tendsto_cdf_atTop _

example (μ : Measure ℝ) [IsFiniteMeasure μ] (s : Set ℝ) (x : ℝ) :
    cdf (μ.restrict s) x = μ.real (s ∩ Iic x) := by
  rw [cdf_eq_real, measureReal_restrict_apply measurableSet_Iic, inter_comm]

example (μ : FiniteMeasure ℝ) (x : ℝ) : cdf (μ : Measure ℝ) x = (μ : Measure ℝ).real (Iic x) :=
  rfl

example (μ : Measure ℝ) [IsFiniteMeasure μ] : IsFiniteMeasure (cdf μ).measure :=
  inferInstance

example (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (cdf μ).measure :=
  inferInstance

-- Evidence that depends on hypotheses is supplied locally.
example {r : ℝ} (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    haveI := isProbabilityMeasure_expMeasure hr
    cdf (expMeasure r) x = 1 - Real.exp (-(r * x)) := by
  simp [cdf_expMeasure_eq hr, hx]

/-! ### The cdf of a finite measure is not normalized -/

example : cdf (0 : Measure ℝ) = 0 := by
  ext x
  simp [cdf_eq_real]

example (x : ℝ) : cdf (0 : Measure ℝ) x ≤ 1 :=
  cdf_le_one _ x

example : cdf ((2 : ℝ≥0) • dirac (0 : ℝ)) 0 = 2 := by
  simp [cdf_eq_real]

example (x : ℝ) : cdf ((2 : ℝ≥0) • dirac (0 : ℝ)) x ≤ 2 := by
  simpa using cdf_le_measureReal_univ ((2 : ℝ≥0) • dirac (0 : ℝ)) x

example : Tendsto (cdf ((2 : ℝ≥0) • dirac (0 : ℝ))) atTop (𝓝 2) := by
  simpa using tendsto_cdf_atTop_measureReal_univ ((2 : ℝ≥0) • dirac (0 : ℝ))

/-! ### Evaluation, proof independence and rewriting -/

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] (x : ℝ) : cdf μ x = μ.real (Iic x) :=
  rfl

example (μ : Measure ℝ) (h₁ h₂ : IsFiniteMeasureOnIic μ) : @cdf μ h₁ = @cdf μ h₂ :=
  rfl

-- The instance derived from a probability measure agrees with any other proof.
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : IsFiniteMeasureOnIic μ) :
    cdf μ = @cdf μ h :=
  rfl

-- `rw [h]` cannot replace `μ` below its instance argument; `simp only [h]` and `subst` can.
example (μ ν : Measure ℝ) [IsFiniteMeasureOnIic μ] [IsFiniteMeasureOnIic ν] (h : μ = ν)
    (x : ℝ) : cdf μ x = cdf ν x := by
  simp only [h]

example (μ ν : Measure ℝ) [IsFiniteMeasureOnIic μ] [IsFiniteMeasureOnIic ν] (h : μ = ν) :
    cdf μ = cdf ν := by
  subst h
  rfl

/-! ### The cdf determines the measure -/

example (μ ν : Measure ℝ) [IsFiniteMeasureOnIic μ] [IsFiniteMeasureOnIic ν]
    (h : ∀ x, μ (Iic x) = ν (Iic x)) : μ = ν := by
  rw [← cdf_eq_iff]
  ext x
  simp only [cdf_eq_real, measureReal_def, h]

example (μ : Measure ℝ) [IsFiniteMeasureOnIic μ] : (cdf μ).measure = μ :=
  measure_cdf μ

-- The lemma applies whatever instance the goal carries.
example (f : StieltjesFunction ℝ) [IsFiniteMeasureOnIic f.measure]
    (hf0 : Tendsto f atBot (𝓝 0)) : cdf f.measure = f :=
  cdf_measure_stieltjesFunction f hf0

-- A probability distribution function is the cdf of its measure.
example (f : StieltjesFunction ℝ) (hf0 : Tendsto f atBot (𝓝 0)) (hf1 : Tendsto f atTop (𝓝 1)) :
    haveI := f.isProbabilityMeasure hf0 hf1
    cdf f.measure = f :=
  cdf_measure_stieltjesFunction f hf0

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open MeasureTheory
open scoped ENNReal

-- Negative real exponents remain in the integral formula's domain.
example : eLpNorm' (fun _ : Unit => (1 : ℝ)) (-2) (0 : Measure Unit) = ∞ := by
  exact eLpNorm'_measure_zero_of_neg (by norm_num)

-- The infinity endpoint uses the essential supremum, including in the constant-function law.
example (c : ℝ) (μ : Measure Unit) (hμ : μ ≠ 0) :
    eLpNorm (fun _ : Unit => c) ∞ μ = ‖c‖ₑ := by
  simpa using eLpNorm_const (p := ∞) c ENNReal.top_ne_zero hμ

-- The numerical formula only needs the extended magnitude of the function.
example {α ε : Type*} [SigmaAlgebra α] [ENorm ε] (f : α → ε) (μ : Measure α) :
    eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ :=
  eLpNorm_one_eq_lintegral_enorm

-- `MemLp` carries a measurability condition at exponent zero.
example {α ε : Type*} [SigmaAlgebra α] [TopologicalSpace ε] [ENorm ε]
    (f : α → ε) (μ : Measure α) (hf : ¬ AEStronglyMeasurable f μ) :
    eLpNorm f 0 μ = 0 ∧ ¬ MemLp f 0 μ :=
  ⟨eLpNorm_exponent_zero, fun h ↦ hf h.aestronglyMeasurable⟩

-- Exponent evidence is inferred from the expression, including negative exponents.
example (f : Unit → ℝ) (q : ℝ) (μ : Measure Unit) (hq : IsUnit q) :
    eLpNorm' (-f) q μ hq = eLpNorm' f q μ hq := by
  simp

-- The ENNReal endpoint formulas remain defined without a nonzero exponent assumption.
example (f : Unit → ℝ) (p : ℝ≥0∞) (μ : Measure Unit) (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) ≤ c ^ (p⁻¹).toReal • eLpNorm f p μ :=
  eLpNorm_smul_measure_le c f p μ

example (f : Unit → ℝ) (μ : Measure Unit) (c : ℝ≥0∞) :
    eLpNorm f 0 (c • μ) = c ^ ((0 : ℝ≥0∞)⁻¹).toReal • eLpNorm f 0 μ :=
  eLpNorm_smul_measure_of_ne_top (by simp) f c

-- Indicator bounds retain both endpoint exponents, even without measurability of the set.
example (s : Set Unit) (c : ℝ) (p : ℝ≥0∞) (μ : Measure Unit) :
    eLpNorm (s.indicator fun _ => c) p μ ≤ ‖c‖ₑ * μ s ^ (p⁻¹).toReal :=
  eLpNorm_indicator_const_le c p

-- Exponent comparison includes the essential-supremum endpoint.
example (f : Unit → ℝ) (p : ℝ≥0∞) (μ : Measure Unit)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ eLpNorm f ∞ μ * μ Set.univ ^ (p⁻¹).toReal := by
  simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := p) le_top hf

-- Real-valued constant norms use the reciprocal in ENNReal before taking toReal.
example (c : ℝ) (μ : Measure Unit) (hμ : μ ≠ 0) :
    lpNorm (fun _ : Unit => c) ∞ μ = ‖c‖ := by
  simpa using lpNorm_const (p := ∞) ENNReal.top_ne_zero hμ c

-- Zero is rejected by the reciprocal-exponent construction itself.
/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example : ℝ≥0∞ :=
  eLpNorm' (fun _ : Unit => (1 : ℝ)) 0 (0 : Measure Unit)

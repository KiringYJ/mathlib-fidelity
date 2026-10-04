/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Geometric distributions

We define the geometric distributions over natural numbers. For `0 < p ≤ 1`,
`geometricMeasure p hp` is the measure which to `{n}` associates `(1 - p) ^ n * p`.

Imagine a certain experiment which has success probability `p`. If you repeat this experiment
infinitely many times and independently, the number of failures before the first success
follows a geometric distribution with parameter `p`.

## Main definition

* `geometricMeasure p hp`: the geometric distribution on `ℕ` with success probability `p`.

## Parameter domain

The success probability lies between `0` and `1`, so it has type `p : unitInterval`; for `1 < p`
the masses `(1 - p) ^ n * p` would alternate in sign. `geometricMeasure p hp` also takes a proof
`hp : p ≠ 0`, and it is then a probability measure. This is the exact parameter domain
`0 < p ≤ 1` ([siegrist_random], §11.3): the masses `(1 - p) ^ n * p` sum to one exactly when
`p ≠ 0`. The degenerate distribution `geometricMeasure 1 hp`, the Dirac measure at `0`, is
included. The proof is an explicit argument without a default value, which would take the set in
`geometricMeasure p s` as the proof.

## References

* [K. Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*][siegrist_random]

## Tags

geometric distribution
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {p : unitInterval}

/-- The geometric distribution on `ℕ` with success probability `p`, defined for `p ≠ 0`. -/
@[nolint unusedArguments]
noncomputable def geometricMeasure (p : unitInterval) (_hp : p ≠ 0) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)

lemma geometricMeasure_eq (hp : p ≠ 0) :
    geometricMeasure p hp =
      Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n) :=
  rfl

/-- The `positivity` tactic does not work for this goal. Use this lemma to rewrite
`(ENNReal.ofReal ((1 - p) ^ n * p)).toReal = (1 - p) ^ n * p`. -/
lemma geometricMeasure_nonneg (p : unitInterval) n :
    0 ≤ (1 - p : ℝ) ^ n * p := mul_nonneg (pow_nonneg (by grind) n) p.2.1

lemma geometricMeasure_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (1 - p : ℝ) ^ n * p := mul_pos (pow_pos (by grind) n) (by grind)

lemma geometricMeasure_singleton (hp : p ≠ 0) n :
    geometricMeasure p hp {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [geometricMeasure_eq hp, Measure.sum_smul_dirac_singleton]

lemma geometricMeasure_real_singleton (hp : p ≠ 0) n :
    (geometricMeasure p hp).real {n} = (1 - p) ^ n * p := by
  rw [measureReal_def, geometricMeasure_singleton hp,
    ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

lemma geometricMeasure_real_singleton_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (geometricMeasure p h1).real {n} := by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n

lemma hasSum_one_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n ↦ (1 - p : ℝ) ^ n * p) 1 := by
  convert! (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : ℝ)
  grind

instance isProbabilityMeasure_geometricMeasure (hp : p ≠ 0) :
    IsProbabilityMeasure (geometricMeasure p hp) :=
  (hasSum_one_geometricMeasure hp).isProbabilityMeasure_sum_dirac (geometricMeasure_nonneg p)

section Integral

variable {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}

lemma integrable_geometricMeasure_iff (hp : p ≠ 0) :
    Integrable f (geometricMeasure p hp) ↔ Summable (fun n ↦ (1 - p : ℝ) ^ n * p * ‖f n‖) := by
  rw [geometricMeasure_eq hp, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

variable [NormedSpace ℝ E]

lemma hasSum_integral_geometricMeasure [CompleteSpace E]
    (hp : p ≠ 0) (hf : Integrable f (geometricMeasure p hp)) :
    HasSum (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) (∫ n, f n ∂geometricMeasure p hp) := by
  have : (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) =
      fun n ↦ (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this, geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable_geometricMeasure_iff hp).1 hf with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

/-- If a function is integrable with respect to `geometricMeasure p hp`, then its integral
against this measure is given by its sum weighted by `(1 - p) ^ n * p`.

See `integral_geometricMeasure` for a version where the codomain is finite-dimensional
and does not require the integrability hypothesis. -/
lemma integral_geometricMeasure' [CompleteSpace E] (hp : p ≠ 0)
    (hf : Integrable f (geometricMeasure p hp)) :
    ∫ n, f n ∂geometricMeasure p hp = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n :=
  (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

/-- The integral of a function taking values in a finite-dimensional space
against `geometricMeasure p hp` is given by its sum weighted by `(1 - p) ^ n * p`. This version
does not require integrability, as the integral exists if and only if the sum exists, and otherwise
they are both defined to be zero.

See `integral_geometricMeasure'` with a general codomain which assumes integrability. -/
lemma integral_geometricMeasure [FiniteDimensional ℝ E] (hp : p ≠ 0) (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p hp = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n := by
  rw [geometricMeasure_eq hp, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

end Integral

section GeometricPMF

variable {p : ℝ}

/-- The pmf of the geometric distribution depending on its success probability. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p

@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]
lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

@[deprecated geometricMeasure_real_singleton_pos (since := "2026-03-08")]
lemma geometricPMFReal_pos {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

@[deprecated measureReal_nonneg (since := "2026-03-08")]
lemma geometricPMFReal_nonneg {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

/-- Geometric distribution with success probability `p`. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
def geometricPMF (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)⟩

@[deprecated Measurable.of_discrete (since := "2026-03-08")]
lemma measurable_geometricPMFReal : Measurable (geometricPMFReal p) := by
  fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
lemma stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

end GeometricPMF

end ProbabilityTheory

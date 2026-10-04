/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Gamma distributions over ℝ

Define the gamma measure over the reals.

## Main definitions
* `gammaPDFReal`: the function `x ↦ r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))`
  for `0 ≤ x` or `0` else, which is the probability density function of the gamma distribution
  with shape `a` and rate `r`.
* `gammaPDF`: `ℝ≥0∞`-valued pdf,
  `gammaPDF a r ha hr = ENNReal.ofReal (gammaPDFReal a r ha hr)`.
* `gammaMeasure`: the gamma distribution on `ℝ` with shape `a` and rate `r`.

## Parameter domain

All three definitions take proofs `ha : 0 < a` and `hr : 0 < r`, and `gammaMeasure a r ha hr` is
a probability measure. This is the exact parameter domain of the gamma distribution
([siegrist_random], §5.8, with scale `1 / r`): `x ↦ x ^ (a - 1) * exp (-(r * x))` is integrable on
`(0, ∞)` exactly when `0 < a` and `0 < r`, so for other parameters no probability measure has a
density proportional to it there.

The proofs are explicit arguments without default values: a default would take the set in
`gammaMeasure a r s` or the point in `gammaPDFReal a r x` as a proof.

## References

* [K. Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*][siegrist_random]
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x -/
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z ≤ y) :
    ∫⁻ x in Iic y, f x = (∫⁻ x in Iio z, f x) + ∫⁻ x in Icc z y, f x := by
  rw [← Iio_union_Icc_eq_Iic hzy, lintegral_union measurableSet_Icc]
  simp_rw [Set.disjoint_iff_forall_ne, mem_Iio, mem_Icc]
  intros
  linarith

namespace ProbabilityTheory

section GammaPDF

/-- The pdf of the gamma distribution with shape `a` and rate `r`, defined for `0 < a` and
`0 < r`. -/
@[nolint unusedArguments]
noncomputable
def gammaPDFReal (a r : ℝ) (_ha : 0 < a) (_hr : 0 < r) (x : ℝ) : ℝ :=
  if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞`, defined for `0 < a` and
`0 < r`. -/
noncomputable
def gammaPDF (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaPDFReal a r ha hr x)

lemma gammaPDF_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    gammaPDF a r ha hr x =
      ENNReal.ofReal (if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0) :=
  rfl

lemma gammaPDF_of_neg {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : x < 0) :
    gammaPDF a r ha hr x = 0 := by
  simp only [gammaPDF_eq, ite_eq_right (not_le.mpr hx), ENNReal.ofReal_zero]

lemma gammaPDF_of_nonneg {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 ≤ x) :
    gammaPDF a r ha hr x =
      ENNReal.ofReal (r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))) := by
  simp only [gammaPDF_eq, ite_eq_left hx]

/-- The Lebesgue integral of the gamma pdf over nonpositive reals equals 0 -/
lemma lintegral_gammaPDF_of_nonpos {x a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : x ≤ 0) :
    ∫⁻ y in Iio x, gammaPDF a r ha hr y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro y (_ : y < _)
    simp only [gammaPDF_eq, ENNReal.ofReal_eq_zero]
    rw [ite_eq_right (by linarith)]

/-- The gamma pdf is measurable. -/
@[fun_prop]
lemma measurable_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Measurable (gammaPDFReal a r ha hr) :=
  Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

/-- The gamma pdf is strongly measurable -/
@[fun_prop]
lemma stronglyMeasurable_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    StronglyMeasurable (gammaPDFReal a r ha hr) :=
  (measurable_gammaPDFReal ha hr).stronglyMeasurable

/-- The gamma pdf is positive for all positive reals -/
lemma gammaPDFReal_pos {x a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    0 < gammaPDFReal a r ha hr x := by
  simp only [gammaPDFReal, ite_eq_left hx.le]
  positivity

/-- The gamma pdf is nonnegative -/
lemma gammaPDFReal_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    0 ≤ gammaPDFReal a r ha hr x := by
  unfold gammaPDFReal
  split_ifs <;> positivity

open Measure

/-- The pdf of the gamma distribution integrates to 1 -/
@[simp]
lemma lintegral_gammaPDF_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, gammaPDF a r ha hr x = 1 := by
  have leftSide : ∫⁻ x in Iio 0, gammaPDF a r ha hr x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio
      (fun x (hx : x < 0) ↦ gammaPDF_of_neg ha hr hx), lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPDF a r ha hr x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ ↦ gammaPDF_of_nonneg ha hr)
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, rightSide, add_zero, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [integral_Ici_eq_integral_Ioi, mul_assoc]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha hr, div_mul_eq_mul_div,
      ← mul_assoc, mul_div_assoc, div_self (Gamma_pos_of_pos ha).ne', mul_one,
      div_rpow zero_le_one hr.le, one_rpow, mul_one_div, div_self (rpow_pos_of_pos hr _).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : 0 ≤ x) ↦ by positivity)
  · apply (measurable_gammaPDFReal ha hr).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : 0 ≤ x) ↦ ?_
    simp_rw [gammaPDFReal, eq_true_intro hx, ite_true]

end GammaPDF

open MeasureTheory

/-- The gamma distribution with shape `a` and rate `r`, defined for `0 < a` and `0 < r`. -/
noncomputable
def gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : Measure ℝ :=
  volume.withDensity (gammaPDF a r ha hr)

instance isProbabilityMeasure_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r ha hr) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]

section GammaCDF

lemma cdf_gammaMeasure_eq_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r ha hr) x = ∫ x in Iic x, gammaPDFReal a r ha hr x := by
  rw [cdf_eq_real, gammaMeasure, measureReal_def, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by simp [gammaPDFReal_nonneg ha hr]
  · fun_prop

lemma cdf_gammaMeasure_eq_lintegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r ha hr) x = ENNReal.toReal (∫⁻ x in Iic x, gammaPDF a r ha hr x) := by
  simp only [gammaPDF, cdf_eq_real]
  simp [gammaMeasure, gammaPDF, measureReal_def]

end GammaCDF

end ProbabilityTheory

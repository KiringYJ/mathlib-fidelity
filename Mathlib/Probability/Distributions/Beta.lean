/-
Copyright (c) 2025 Tommy Löfgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `beta`: the normalizing constant `Γ(α) Γ(β) / Γ(α + β)` of the beta distribution with shape
  parameters `α` and `β`.
* `betaPDFReal`: the function `x ↦ (1 / beta α β hα hβ) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of the beta
  distribution with shape parameters `α` and `β`.
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β hα hβ = ENNReal.ofReal (betaPDFReal α β hα hβ)`.
* `betaMeasure`: the beta distribution on `ℝ` with shape parameters `α` and `β`.

## Parameter domain

All four definitions take proofs `hα : 0 < α` and `hβ : 0 < β`, and `betaMeasure α β hα hβ` is a
probability measure. This is the exact parameter domain of the beta distribution
([siegrist_random], §5.17): `x ↦ x ^ (α - 1) * (1 - x) ^ (β - 1)` is integrable on `(0, 1)` exactly
when `0 < α` and `0 < β`, so for other parameters its integral, the normalizing constant,
diverges, and no probability measure has a density proportional to it there. As for the gamma
distribution, the proofs are explicit arguments without default values.

## References

* [K. Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*][siegrist_random]
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

/-- The normalizing constant `Γ(α) Γ(β) / Γ(α + β)` of the beta distribution with shape
parameters `α` and `β`, defined for `0 < α` and `0 < β`. It is the real part of the beta integral
`Complex.betaIntegral α β` (`beta_eq_betaIntegralReal`). -/
@[nolint unusedArguments]
noncomputable def beta (α β : ℝ) (_hα : 0 < α) (_hβ : 0 < β) : ℝ :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

lemma beta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < beta α β hα hβ :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

/-- The normalizing constant `beta` is the real part of the complex beta integral. -/
theorem beta_eq_betaIntegralReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    beta α β hα hβ = (betaIntegral α β).re := by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

/-- The probability density function of the beta distribution with shape parameters `α` and `β`,
defined for `0 < α` and `0 < β`.
Returns `(1 / beta α β hα hβ) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
when `0 < x < 1` and `0` otherwise. -/
noncomputable def betaPDFReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (1 / beta α β hα hβ) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

/-- The pdf of the beta distribution, as a function valued in `ℝ≥0∞`, defined for `0 < α` and
`0 < β`. -/
noncomputable def betaPDF (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal α β hα hβ x)

lemma betaPDF_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    betaPDF α β hα hβ x =
      ENNReal.ofReal (if 0 < x ∧ x < 1 then
        (1 / beta α β hα hβ) * x ^ (α - 1) * (1 - x) ^ (β - 1) else 0) := rfl

lemma betaPDF_eq_zero_of_nonpos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx : x ≤ 0) :
    betaPDF α β hα hβ x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_eq_zero_of_one_le {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx : 1 ≤ x) :
    betaPDF α β hα hβ x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_of_pos_lt_one {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx_pos : 0 < x)
    (hx_lt : x < 1) :
    betaPDF α β hα hβ x =
      ENNReal.ofReal ((1 / beta α β hα hβ) * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [betaPDF_eq, ite_eq_left ⟨hx_pos, hx_lt⟩]

lemma lintegral_betaPDF {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β hα hβ x =
      ∫⁻ (x : ℝ) in Ioo 0 1,
        ENNReal.ofReal (1 / beta α β hα hβ * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [← lintegral_add_compl _ measurableSet_Iic,
    setLIntegral_eq_zero measurableSet_Iic
      (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_nonpos hα hβ hx),
    zero_add, compl_Iic, ← lintegral_add_compl _ measurableSet_Ici,
    setLIntegral_eq_zero measurableSet_Ici
      (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hα hβ hx),
    zero_add, compl_Ici, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    setLIntegral_congr_fun measurableSet_Ioo
      (fun x ⟨hx_pos, hx_lt⟩ ↦ betaPDF_of_pos_lt_one hα hβ hx_pos hx_lt)]

/-- The beta pdf is positive for all positive reals with positive parameters. -/
lemma betaPDFReal_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : 0 < x) (hx2 : x < 1) :
    0 < betaPDFReal α β hα hβ x := by
  rw [betaPDFReal, ite_eq_left ⟨hx1, hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

/-- The beta pdf is measurable. -/
@[fun_prop]
lemma measurable_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measurable (betaPDFReal α β hα hβ) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

/-- The beta pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StronglyMeasurable (betaPDFReal α β hα hβ) := (measurable_betaPDFReal hα hβ).stronglyMeasurable

/-- The pdf of the beta distribution integrates to 1. -/
@[simp]
lemma lintegral_betaPDF_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β hα hβ x = 1 := by
  rw [lintegral_betaPDF, ← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ)), beta_eq_betaIntegralReal α β hα hβ,
      betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ ↦ ?_
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
      all_goals linarith
    convert! betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx ↦ ?_)
    convert! betaPDFReal_pos hα hβ hx.1 hx.2 |>.le using 1
    rw [betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

end BetaPDF

/-- The beta distribution with shape parameters `α` and `β`, defined for `0 < α` and `0 < β`. -/
noncomputable
def betaMeasure (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : Measure ℝ :=
  volume.withDensity (betaPDF α β hα hβ)

instance isProbabilityMeasure_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β hα hβ) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

end ProbabilityTheory

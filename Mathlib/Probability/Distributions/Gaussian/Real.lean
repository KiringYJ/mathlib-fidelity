/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`
  for `v ≠ 0`, which is the probability density function of a Gaussian distribution with mean `μ`
  and variance `v`.
* `gaussianPDF`: `ℝ≥0∞`-valued pdf,
  `gaussianPDF μ v hv x = ENNReal.ofReal (gaussianPDFReal μ v hv x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v hv` with respect to the Lebesgue measure.

## Parameter domain

`gaussianReal μ v` is defined for every variance `v : ℝ≥0`. A Gaussian measure on `ℝ` is either a
Dirac measure or a measure with a normal density ([bogachev1998], Definition 1.1.1), so the
degenerate Gaussian distribution `gaussianReal μ 0` is `dirac μ`; Siegrist likewise treats a
constant as a normal random variable with variance zero where convenient ([siegrist_random],
§5.6). For every `v`, `gaussianReal μ v` is the probability measure with characteristic function
`t ↦ exp (t * μ * I - v * t ^ 2 / 2)` (`charFun_gaussianReal`), and the degenerate distributions
make the family closed under all linear maps, including the zero map
(`gaussianReal_map_const_mul`), as Gaussian measures on vector spaces require.

A Dirac measure has no density with respect to the Lebesgue measure, and the density formula does
not hold for it ([siegrist_random], §5.6). So `gaussianPDFReal` and `gaussianPDF` take a proof
`hv : v ≠ 0`, and the Radon-Nikodym derivative of the degenerate distribution vanishes
(`rnDeriv_gaussianReal_zero_var`). The proof is an explicit argument without a default value: a
default would take the point in `gaussianPDFReal μ v x` as a proof.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c ^ 2 * v`.

## References

* [V. I. Bogachev, *Gaussian measures*][bogachev1998]
* [K. Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*][siegrist_random]
-/

@[expose] public section

open scoped ENNReal NNReal Real Complex

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

/-- Probability density function of the Gaussian distribution with mean `μ` and variance `v`,
defined for `v ≠ 0`. -/
noncomputable
def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) : ℝ :=
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  Checked.inv (√(2 * π * v))
    (Real.sqrt_pos.2 (mul_pos (mul_pos zero_lt_two Real.pi_pos) hv')).ne'.isUnit *
    rexp (Checked.div (-(x - μ) ^ 2) (2 * v) (mul_pos zero_lt_two hv').ne'.isUnit)

lemma gaussianPDFReal_def (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianPDFReal μ v hv =
      fun x ↦ (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * (v : ℝ))) := rfl

/-- The Gaussian pdf is positive. -/
lemma gaussianPDFReal_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    0 < gaussianPDFReal μ v hv x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is nonnegative. -/
lemma gaussianPDFReal_nonneg (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    0 ≤ gaussianPDFReal μ v hv x :=
  (gaussianPDFReal_pos μ hv x).le

/-- The Gaussian pdf is measurable jointly in its parameters and its argument. -/
@[fun_prop]
lemma _root_.Measurable.gaussianPDFReal {α : Type*} {mα : SigmaAlgebra α} {m : α → ℝ}
    {v : α → ℝ≥0} {x : α → ℝ} (hm : Measurable m) (hv : Measurable v) (hx : Measurable x)
    (h₀ : ∀ a, v a ≠ 0) :
    Measurable fun a ↦ gaussianPDFReal (m a) (v a) (h₀ a) (x a) := by
  have hv_pos (a : α) : 0 < (v a : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (h₀ a))
  have h_scale (a : α) : IsUnit (2 * (v a : ℝ)) := (mul_pos zero_lt_two (hv_pos a)).ne'.isUnit
  have h_norm (a : α) : IsUnit (√(2 * π * (v a : ℝ))) :=
    (Real.sqrt_pos.2 (mul_pos (mul_pos zero_lt_two Real.pi_pos) (hv_pos a))).ne'.isUnit
  have h_scale_meas : Measurable fun a ↦ 2 * (v a : ℝ) :=
    measurable_const.mul hv.coe_nnreal_real
  have h_norm_meas : Measurable fun a ↦ √(2 * π * (v a : ℝ)) :=
    (measurable_const.mul hv.coe_nnreal_real).sqrt
  simp_rw [gaussianPDFReal_def]
  exact (h_norm_meas.inv₀ (hf := h_norm)).mul
    (((hx.sub hm).pow_const (2 : ℕ)).neg.div₀ (hgUnit := h_scale) h_scale_meas).exp

lemma measurable_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measurable (gaussianPDFReal μ v hv) := by
  fun_prop

/-- The Gaussian pdf is strongly measurable. -/
lemma stronglyMeasurable_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    StronglyMeasurable (gaussianPDFReal μ v hv) := by
  fun_prop

@[fun_prop]
lemma integrable_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (gaussianPDFReal μ v hv) := by
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have h : 0 < (2 : ℝ) * v := mul_pos zero_lt_two hv'
  simpa only [gaussianPDFReal_def, div_eq_inv_mul₀, mul_neg, neg_mul] using
    ((integrable_exp_neg_mul_sq (inv_pos.mpr h)).const_mul (√(2 * π * v))⁻¹).comp_sub_right μ

/-- The Gaussian distribution pdf integrates to 1. -/
lemma lintegral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v h x) = 1 := by
  have hv : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h)
  have hden : 0 < (2 : ℝ) * v := mul_pos zero_lt_two hv
  have hinv : 0 < ((2 : ℝ) * v)⁻¹ := inv_pos.mpr hden
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v h) volume := by fun_prop
  have hf : 0 ≤ₐₛ gaussianPDFReal μ v h := ae_of_all _ (gaussianPDFReal_nonneg μ h)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a ↦ rexp (-a ^ 2 / ((2 : ℝ) * v))) μ]
  have he : π / ((2 : ℝ) * v)⁻¹ = 2 * π * v := by
    rw [div_inv_eq_mul₀]
    ring
  simp_rw [div_eq_inv_mul₀, mul_neg, ← neg_mul]
  rw [integral_gaussian _ (hb₀ := hinv.ne'.isUnit), he, inv_mul_cancel₀]

/-- The Gaussian distribution pdf integrates to 1. -/
lemma integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v hv x = 1 := by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ hv)
    (ae_of_all _ (gaussianPDFReal_nonneg _ hv)), ← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ hv)) zero_le_one]

lemma gaussianPDFReal_sub {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ) :
    gaussianPDFReal μ v hv (x - y) = gaussianPDFReal (μ + y) v hv x := by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

lemma gaussianPDFReal_add {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ) :
    gaussianPDFReal μ v hv (x + y) = gaussianPDFReal (μ - y) v hv x := by
  rw [sub_eq_add_neg, ← gaussianPDFReal_sub, sub_eq_add_neg, neg_neg]

lemma gaussianPDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hv : v ≠ 0) (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v hv (c⁻¹ * x)
      = |c| * gaussianPDFReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
          (mul_ne_zero (fun h ↦ hc (by simpa using congrArg NNReal.toReal h)) hv) x := by
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hpos : 0 < 2 * π * (v : ℝ) := by positivity
  have h0 : 0 < (2 : ℝ) * v := by positivity
  have h1 : 0 < (2 : ℝ) * (c ^ 2 * v) := by positivity
  have hnorm : √(2 * π * (c ^ 2 * v)) = |c| * √(2 * π * v) := by
    calc
      _ = √(c ^ 2 * (2 * π * v)) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hnorm_pos : 0 < √(2 * π * (c ^ 2 * v)) := by positivity
  have hcoeff : |c| * (√(2 * π * (c ^ 2 * v)))⁻¹ = (√(2 * π * v))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left₀
    rw [mul_right_comm, ← hnorm, mul_inv_cancel₀]
  have hlin : (c⁻¹ * x - μ) * c = x - c * μ := by
    rw [sub_mul, mul_right_comm, inv_mul_cancel₀, one_mul, mul_comm μ c]
  have hexp : -(c⁻¹ * x - μ) ^ 2 / (2 * (v : ℝ)) = -(x - c * μ) ^ 2 / (2 * (c ^ 2 * v)) := by
    apply div_eq_div_iff.2
    rw [← hlin]
    ring
  simp only [gaussianPDFReal_def, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc, hcoeff, hexp]

lemma gaussianPDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hv : v ≠ 0) (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v hv (c * x)
      = |c⁻¹| * gaussianPDFReal (c⁻¹ * μ) (.mk (c⁻¹ ^ 2) (sq_nonneg _) * v)
          (mul_ne_zero (NNReal.coe_ne_zero.1 (pow_ne_zero _ (inv_ne_zero (ha := hc.isUnit)))) hv)
          x := by
  simpa only [inv_inv₀] using gaussianPDFReal_inv_mul hv (inv_ne_zero (ha := hc.isUnit)) x

/-- The pdf of a Gaussian distribution on ℝ with mean `μ` and variance `v`, defined for
`v ≠ 0`. -/
noncomputable
def gaussianPDF (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianPDFReal μ v hv x)

lemma gaussianPDF_def (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianPDF μ v hv = fun x ↦ ENNReal.ofReal (gaussianPDFReal μ v hv x) := rfl

@[simp]
lemma toReal_gaussianPDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianPDF μ v hv x).toReal = gaussianPDFReal μ v hv x := by
  rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ hv x)]

lemma gaussianPDF_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < gaussianPDF μ v hv x := by
  rw [gaussianPDF, ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ hv _

lemma gaussianPDF_lt_top {μ : ℝ} {v : ℝ≥0} {hv : v ≠ 0} {x : ℝ} : gaussianPDF μ v hv x < ∞ := by
  simp [gaussianPDF]

lemma gaussianPDF_ne_top {μ : ℝ} {v : ℝ≥0} {hv : v ≠ 0} {x : ℝ} : gaussianPDF μ v hv x ≠ ∞ := by
  simp [gaussianPDF]

@[simp]
lemma support_gaussianPDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (gaussianPDF μ v hv) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

/-- The Gaussian pdf is measurable jointly in its parameters and its argument. -/
@[fun_prop]
lemma _root_.Measurable.gaussianPDF {α : Type*} {mα : SigmaAlgebra α} {m : α → ℝ}
    {v : α → ℝ≥0} {x : α → ℝ} (hm : Measurable m) (hv : Measurable v) (hx : Measurable x)
    (h₀ : ∀ a, v a ≠ 0) :
    Measurable fun a ↦ gaussianPDF (m a) (v a) (h₀ a) (x a) :=
  (hm.gaussianPDFReal hv hx h₀).ennreal_ofReal

lemma measurable_gaussianPDF (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Measurable (gaussianPDF μ v hv) := by
  fun_prop

lemma stronglyMeasurable_gaussianPDF (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    StronglyMeasurable (gaussianPDF μ v hv) := by
  fun_prop

@[simp]
lemma lintegral_gaussianPDF_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, gaussianPDF μ v h x = 1 :=
  lintegral_gaussianPDFReal_eq_one μ h

end GaussianPDF

section GaussianReal

/-- A Gaussian distribution on `ℝ` with mean `μ` and variance `v`: the measure with density
`gaussianPDF μ v hv` if `hv : v ≠ 0`, and the degenerate Gaussian distribution `dirac μ` if
`v = 0`. -/
@[wikidata Q133871]
noncomputable
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if hv : v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v hv)

lemma gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v = volume.withDensity (gaussianPDF μ v hv) := dite_eq_right hv

@[simp]
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := dite_eq_left rfl

instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

lemma nullSingletonClass_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) :
    NullSingletonClass (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

@[deprecated (since := "2026-06-09")]
alias noAtoms_gaussianReal := nullSingletonClass_gaussianReal

lemma gaussianReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v hv x := by
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply' _ s]

lemma gaussianReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v hv x) := by
  rw [gaussianReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ hv).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ hv)

lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v ≪ volume := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    volume ≪ gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ hv).aemeasurable
  · exact ae_of_all _ (fun _ ↦ (gaussianPDF_pos _ hv _).ne')

lemma rnDeriv_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v hv := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ hv)

/-- The degenerate Gaussian distribution is singular with respect to the Lebesgue measure, so its
Radon-Nikodym derivative vanishes almost everywhere. -/
lemma rnDeriv_gaussianReal_zero_var (μ : ℝ) : ∂(gaussianReal μ 0)/∂volume =ₐₛ 0 := by
  rw [gaussianReal_zero_var]
  refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
  rw [withDensity_zero, add_zero]

lemma integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v hv x • f x := by
  simp [gaussianReal_of_var_ne_zero _ hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ hv)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]

@[fun_prop]
lemma measurable_gaussianReal :
    Measurable gaussianReal.uncurry :=
  Measurable.dite (s := {p : ℝ × ℝ≥0 | p.2 = 0}) (f := fun p ↦ Measure.dirac p.1.1) (by fun_prop)
    (measurable_withDensity (f := fun (p : ({p : ℝ × ℝ≥0 | p.2 = 0}ᶜ : Set (ℝ × ℝ≥0))) x ↦
      gaussianPDF p.1.1 p.1.2 p.2 x) (by fun_prop))
    (measurableSet_eq_fun measurable_snd measurable_const)

section Transformations

variable {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v hv (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ hv)) (integrable_gaussianPDFReal _ hv)

lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    ((gaussianReal μ v).map f.symm) s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v hv (f x)) := by
  have hmap := congrArg (Measure.mapₗ f.symm f.symm.measurable)
    (gaussianReal_of_var_ne_zero μ hv)
  have hmap' : (gaussianReal μ v).map f.symm =
      (volume.withDensity (gaussianPDF μ v hv)).map f.symm := by
    simpa only [Measure.mapₗ_apply_of_measurable] using hmap
  rw [hmap', gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ hv)) (integrable_gaussianPDFReal _ hv)

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
lemma gaussianReal_map_add_const (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub hv _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
lemma gaussianReal_map_const_add (y : ℝ) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
lemma gaussianReal_map_const_mul (c : ℝ) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, gaussianReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  have hc' : IsUnit c := (show c ≠ 0 from hc).isUnit
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs',
    gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.toMeasurableEquiv_coe, Homeomorph.mulLeft₀_symm_apply,
    gaussianPDFReal_inv_mul hv hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀ (ha := (abs_pos.2 hc).ne'.isUnit)]

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
lemma gaussianReal_map_mul_const (c : ℝ) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x ↦ -x) = gaussianReal (-μ) v := by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

private lemma isUnit_nnreal_sq (c : ℝ) (hc : IsUnit c) : IsUnit (⟨c ^ 2, sq_nonneg _⟩ : ℝ≥0) :=
  (NNReal.coe_ne_zero.1 (show ((⟨c ^ 2, sq_nonneg _⟩ : ℝ≥0) : ℝ) ≠ 0 from
    (hc.pow 2).ne_zero)).isUnit

/-- Scaling a Gaussian distribution by the reciprocal of a nonzero constant is Gaussian. -/
lemma gaussianReal_map_div_const (c : ℝ) {hc : IsUnit c} :
    (gaussianReal μ v).map (fun x : ℝ ↦ x / c) =
      gaussianReal (μ / c)
        (Checked.div v ⟨c ^ 2, sq_nonneg _⟩ (by exact isUnit_nnreal_sq c hc)) := by
  have hinv : (⟨c⁻¹ ^ 2, sq_nonneg _⟩ : ℝ≥0) =
      Checked.inv ⟨c ^ 2, sq_nonneg _⟩ (isUnit_nnreal_sq c hc) := by
    apply NNReal.coe_injective
    exact (inv_pow₀ 2).trans
      (NNReal.coe_inv _ (hr := isUnit_nnreal_sq c hc)).symm
  simp only [div_eq_inv_mul₀, gaussianReal_map_const_mul]
  exact congrArg (gaussianReal (c⁻¹ * μ)) <|
    (congrArg (fun x : ℝ≥0 ↦ x * v) hinv).trans
      (div_eq_inv_mul₀ v _ (hb := isUnit_nnreal_sq c hc)).symm

lemma gaussianReal_map_sub_const (y : ℝ) :
    (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]

lemma gaussianReal_map_const_sub (y : ℝ) :
    (gaussianReal μ v).map (y - ·) = gaussianReal (y - μ) v := by
  have hfun : (fun x : ℝ ↦ y - x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by
    ext
    exact sub_eq_add_neg _ _
  calc
    _ = (gaussianReal μ v).map ((fun x ↦ y + x) ∘ fun x ↦ -x) :=
      Measure.map_congr (ae_of_all _ fun x ↦ congrFun hfun x) (by fun_prop)
    _ = ((gaussianReal μ v).map (fun x ↦ -x)).map (fun x ↦ y + x) :=
      (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = _ := by rw [gaussianReal_map_neg, gaussianReal_map_const_add, add_comm,
      sub_eq_add_neg]

variable {Ω : Type*} {mΩ : SigmaAlgebra Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X + y`
has Gaussian law with mean `μ + y` and variance `v`. -/
lemma gaussianReal_add_const (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ X ω + y) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_add_const y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `y + X`
has Gaussian law with mean `μ + y` and variance `v`. -/
lemma gaussianReal_const_add (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ y + X ω) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_add y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X - y`
has Gaussian law with mean `μ - y` and variance `v`. -/
lemma gaussianReal_sub_const (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ X ω - y) (gaussianReal (μ - y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_sub_const y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `c * X`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma gaussianReal_const_mul (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ c * X ω) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul c⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma gaussianReal_mul_const (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ X ω * c) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_mul_const c⟩ hX

lemma gaussianReal_neg (hX : HasLaw X (gaussianReal μ v) P) :
    HasLaw (-X) (gaussianReal (-μ) v) P := by
  rw [Pi.neg_def, ← Function.comp_def]
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_neg⟩ hX

/-- Dividing a Gaussian random variable by a nonzero constant `c` scales its mean by `c⁻¹`
and its variance by `(c ^ 2)⁻¹`. -/
lemma gaussianReal_div_const (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) {hc : IsUnit c} :
    HasLaw (fun ω ↦ X ω / c)
      (gaussianReal (μ / c)
        (Checked.div v ⟨c ^ 2, sq_nonneg _⟩ (by exact isUnit_nnreal_sq c hc))) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_div_const c⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `y - X`
has Gaussian law with mean `y - μ` and variance `v`. -/
lemma gaussianReal_const_sub (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ y - X ω) (gaussianReal (y - μ) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_sub y⟩ hX

end Transformations

section CharacteristicFunction

open Real Complex

variable {Ω : Type*} {mΩ : SigmaAlgebra Ω} {p : Measure Ω} {μ : ℝ} {v : ℝ≥0} {X : Ω → ℝ}

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The complex moment-generating function of a Gaussian distribution with mean `μ` and variance `v`
is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
theorem complexMGF_id_gaussianReal (z : ℂ) :
    complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 2) := by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hvR
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v hv x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : ℝ, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + (μ : ℂ) / (v : ℂ)) * x
          + -(μ : ℂ) ^ 2 / (2 * (v : ℂ))) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * ((π : ℂ) / - -(2 * (v : ℂ))⁻¹) ^ (1 / 2 : ℂ)
        * cexp (-(μ : ℂ) ^ 2 / (2 * (v : ℂ))
          - (z + (μ : ℂ) / (v : ℂ)) ^ 2 / (4 * -(2 * (v : ℂ))⁻¹)) := by
      have hv_pos : 0 < v := pos_iff_ne_zero.mpr hv
      have h_scale : IsUnit (2 * v) := (mul_pos zero_lt_two hv_pos).ne'.isUnit
      let q : ℝ≥0 := Checked.inv (2 * v) h_scale
      have hb : (-((q : ℝ) : ℂ)).re < 0 := by
        rw [neg_re, ofReal_re, neg_lt_zero]
        exact NNReal.coe_pos.mpr (inv_pos.mpr (mul_pos zero_lt_two hv_pos))
      dsimp only [q] at hb
      rw [integral_cexp_quadratic hb, ← mul_assoc]
      push_cast
      rfl
    _ = 1 * cexp (-(μ : ℂ) ^ 2 / (2 * (v : ℂ))
          - (z + (μ : ℂ) / (v : ℂ)) ^ 2 / (4 * -(2 * (v : ℂ))⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
      rw [inv_inv₀]
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : ℂ) ≠ 0 := by simpa
      simp [field]
      ring

/-- The complex moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
theorem complexMGF_gaussianReal (hX : HasLaw X (gaussianReal μ v) p) (z : ℂ) :
    complexMGF X p z = cexp (z * μ + v * z ^ 2 / 2) := by
  rw [← complexMGF_id_map hX.aemeasurable, hX.map_eq, complexMGF_id_gaussianReal]

/-- The characteristic function of a Gaussian distribution with mean `μ` and variance `v`
is given by `t ↦ exp (t * μ * I - v * t ^ 2 / 2)`. -/
theorem charFun_gaussianReal (t : ℝ) :
    charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2) := by
  rw [← complexMGF_id_mul_I, complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  push_cast
  ring_nf

/-- The moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ exp (μ * t + v * t ^ 2 / 2)`. -/
theorem mgf_gaussianReal (hX : HasLaw X (gaussianReal μ v) p) (t : ℝ) :
    mgf X p t = rexp (μ * t + v * t ^ 2 / 2) := by
  suffices (mgf X p t : ℂ) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  rw [← mgf_id_map hX.aemeasurable, ← complexMGF_ofReal, hX.map_eq, complexMGF_id_gaussianReal,
    mul_comm μ]
  rw [Complex.ofReal_exp]
  push_cast
  rfl

theorem mgf_fun_id_gaussianReal :
    mgf (fun x ↦ x) (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) := by
  ext t
  rw [mgf_gaussianReal]
  simp

theorem mgf_id_gaussianReal : mgf id (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) :=
  mgf_fun_id_gaussianReal

/-- The cumulant-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ μ * t + v * t ^ 2 / 2`. -/
theorem cgf_gaussianReal (hX : HasLaw X (gaussianReal μ v) p) (t : ℝ) :
    cgf X p t = μ * t + v * t ^ 2 / 2 := by
  rw [cgf, mgf_gaussianReal hX t, Real.log_exp]

lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff, mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]
lemma integrableExpSet_fun_id_gaussianReal :
    integrableExpSet (fun x ↦ x) (gaussianReal μ v) = Set.univ :=
  integrableExpSet_id_gaussianReal

end CharacteristicFunction

section Moments

variable {μ : ℝ} {v : ℝ≥0}

private lemma hasDerivAt_gaussian_exponent (v : ℝ≥0) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ v * u ^ 2 / 2) (v * t) t := by
  have h := (((hasDerivAt_id t).fun_pow 2).const_mul (v : ℝ)).div_const 2
    (hd := (two_ne_zero : (2 : ℝ) ≠ 0).isUnit)
  let slope : ℝ := (v : ℝ) * (((2 : ℕ) : ℝ) * t ^ ((2 : ℕ) - 1) * 1) / 2
  change HasDerivAt (fun u : ℝ ↦ v * u ^ 2 / 2) slope t at h
  have h_slope : slope = v * t := by
    simp only [slope, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  exact h_slope ▸ h

/-- The mean of a real Gaussian distribution `gaussianReal μ v` is its mean parameter `μ`. -/
@[simp]
lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ := by
  rw [← deriv_mgf_zero (by simp), mgf_fun_id_gaussianReal]
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul μ).add (hasDerivAt_gaussian_exponent v 0)
  simpa using h.exp.deriv

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_fun_id_gaussianReal : Var[fun x ↦ x; gaussianReal μ v] = v := by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x ↦ x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal, iteratedDeriv_succ, iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have h : deriv (fun t : ℝ ↦ rexp (v * t ^ 2 / 2)) =
        fun t : ℝ ↦ v * t * rexp (v * t ^ 2 / 2) := by
      funext t
      exact (hasDerivAt_gaussian_exponent v t).exp.deriv.trans (mul_comm _ _)
    rw [h]
    have h' := ((hasDerivAt_id (0 : ℝ)).const_mul (v : ℝ)).mul
      (hasDerivAt_gaussian_exponent v 0).exp
    change HasDerivAt (fun t : ℝ ↦ v * t * rexp (v * t ^ 2 / 2)) _ _ at h'
    simpa using h'.deriv

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v :=
  variance_fun_id_gaussianReal

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_gaussianReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_gaussianReal p

end Moments

/-- Two real Gaussian distributions are equal iff they have the same mean and variance. -/
lemma gaussianReal_ext_iff {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    gaussianReal μ₁ v₁ = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁),
    ← integral_id_gaussianReal (μ := μ₂) (v := v₂), h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : ℝ) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁),
    ← variance_id_gaussianReal (μ := μ₂) (v := v₂), h]

section LinearMap

variable {μ : ℝ} {v : ℝ≥0}

lemma gaussianReal_map_linearMap (L : ℝ →ₗ[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) := by
  have hfun : (L : ℝ → ℝ) = fun x ↦ L 1 * x := by simp
  calc
    _ = (gaussianReal μ v).map (fun x ↦ L 1 * x) :=
      Measure.map_congr (ae_of_all _ fun x ↦ congrFun hfun x) (by fun_prop)
    _ = gaussianReal (L 1 * μ) ((L 1 ^ 2).toNNReal * v) := by
      simpa [Real.toNNReal_of_nonneg (sq_nonneg (L 1))] using
        (gaussianReal_map_const_mul (μ := μ) (v := v) (L 1))
    _ = _ := by
      congr
      simp

lemma gaussianReal_map_continuousLinearMap (L : ℝ →L[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) :=
  gaussianReal_map_linearMap L

@[simp]
lemma integral_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]
lemma integral_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := integral_linearMap_gaussianReal L

@[simp]
lemma variance_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v := by
  rw [← variance_id_map, gaussianReal_map_linearMap, variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]
lemma variance_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v :=
  variance_linearMap_gaussianReal L

end LinearMap

/-- The convolution of two real Gaussian distributions with means `m₁, m₂` and variances `v₁, v₂`
is a real Gaussian distribution with mean `m₁ + m₂` and variance `v₁ + v₂`. -/
lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  push_cast
  ring_nf

/- The sum of two real Gaussian variables with means `m₁, m₂` and variances `v₁, v₂` is a real
Gaussian distribution with mean `m₁ + m₂` and variance `v_1 + v_2`. -/
lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : SigmaAlgebra Ω} {P : Measure Ω}
    {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal m₁ v₁) P) (hY : HasLaw Y (gaussianReal m₂ v₂) P) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  have hσX : SigmaFinite (P.map X hX.aemeasurable) := by
    simpa only [hX.map_eq] using (inferInstance : SigmaFinite (gaussianReal m₁ v₁))
  have hσY : SigmaFinite (P.map Y hY.aemeasurable) := by
    simpa only [hY.map_eq] using (inferInstance : SigmaFinite (gaussianReal m₂ v₂))
  calc
    _ = P.map X hX.aemeasurable ∗ P.map Y hY.aemeasurable :=
      hXY.map_add_eq_map_conv_map₀' hX.aemeasurable hY.aemeasurable hσX hσY
    _ = gaussianReal m₁ v₁ ∗ gaussianReal m₂ v₂ := by simp only [hX.map_eq, hY.map_eq]
    _ = _ := gaussianReal_conv_gaussianReal

end GaussianReal

end ProbabilityTheory

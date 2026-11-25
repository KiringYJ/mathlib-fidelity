/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ` with respect to `μ`. This is sometimes also called
the Esscher transform.

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
can be used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `Measure.tilted μ f`: exponential tilting of `μ` by `f` when the exponential has a finite,
  positive integral, with density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ`.

-/

@[expose] public section

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : SigmaAlgebra α} {μ : Measure α} {f : α → ℝ}

/-- The exponential tilt of a measure by a function whose exponential has a finite,
positive integral. -/
noncomputable def Measure.tilted (μ : Measure α) (f : α → ℝ)
    (h : IsUnit (∫ x, exp (f x) ∂μ) := by checked_unit) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (Checked.div (exp (f x)) (∫ y, exp (f y) ∂μ) h))

/-- The exponential normalizer is invertible exactly when the base measure is nonzero and
exponentiation gives an integrable function. -/
lemma isUnit_tilted_normalizer_iff :
    IsUnit (∫ x, exp (f x) ∂μ) ↔ μ ≠ 0 ∧ Integrable (fun x ↦ exp (f x)) μ := by
  constructor
  · intro h
    refine ⟨?_, Integrable.of_integral_ne_zero h.ne_zero⟩
    rintro rfl
    exact h.ne_zero (by simp)
  · rintro ⟨hμ, hf⟩
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'.isUnit

lemma isUnit_tilted_normalizer_const (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ] (c : ℝ) :
    IsUnit (∫ _x, exp c ∂μ) :=
  isUnit_tilted_normalizer_iff.2 ⟨NeZero.ne _, integrable_const _⟩

/-- A defined exponential tilt has a positive normalizer. -/
lemma tilted_normalizer_pos {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    0 < ∫ x, exp (f x) ∂μ :=
  lt_of_le_of_ne (integral_nonneg fun _ ↦ (exp_pos _).le) h.ne_zero.symm

@[simp]
lemma tilted_const' (μ : Measure α) (c : ℝ) {h : IsUnit (∫ _x, exp c ∂μ)} :
    μ.tilted (fun _ ↦ c) = (μ Set.univ)⁻¹ • μ := by
  have hm : μ.real Set.univ ≠ 0 := by
    intro hz
    apply h.ne_zero
    simp [integral_const, hz]
  have hμ : μ Set.univ ≠ 0 := fun hz ↦ hm (by simp [Measure.real, hz])
  have hExp : exp c ≠ 0 := (exp_pos c).ne'
  have hdiv : exp c / (∫ _x, exp c ∂μ) = (μ.real Set.univ)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right₀
    simp only [integral_const, smul_eq_mul]
    field_simp
  rw [Measure.tilted, withDensity_const, hdiv]
  change ENNReal.ofReal (((μ Set.univ).toReal)⁻¹) • μ = (μ Set.univ)⁻¹ • μ
  rw [← ENNReal.toReal_inv (ha := hm.isUnit), ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hμ)]

lemma tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    μ.tilted (fun _ ↦ c) (isUnit_tilted_normalizer_const μ c) = μ := by simp

@[simp]
lemma tilted_zero' (μ : Measure α) {h : IsUnit (∫ x, exp ((0 : α → ℝ) x) ∂μ)} :
    μ.tilted 0 = (μ Set.univ)⁻¹ • μ := tilted_const' μ 0

lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.tilted 0 (isUnit_tilted_normalizer_const μ 0) = μ := tilted_const μ 0

lemma tilted_congr {g : α → ℝ} (hfg : f =ᵐ[μ] g)
    {hf : IsUnit (∫ x, exp (f x) ∂μ)} {hg : IsUnit (∫ x, exp (g x) ∂μ)} :
    μ.tilted f hf = μ.tilted g hg := by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ :=
    integral_congr_ae (hfg.fun_comp exp)
  apply withDensity_congr_ae
  filter_upwards [hfg] with x hx
  apply congrArg ENNReal.ofReal
  apply eq_div_iff_mul_eq.mpr
  rw [← h_int_eq, div_mul_cancel₀, hx]

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    μ.tilted f = μ.withDensity (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞)
      (.mk (exp (f x) / ∫ y, exp (f y) ∂μ) (div_nonneg (exp_pos _).le
        (tilted_normalizer_pos (h := h)).le))) := by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply' (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    μ.tilted f h s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ :=
  withDensity_apply _ hs

lemma tilted_apply (μ : Measure α) [SFinite μ] (f : α → ℝ) (s : Set α)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    μ.tilted f h s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ :=
  withDensity_apply' _ s

lemma tilted_apply_eq_ofReal_integral' {s : Set α} (f : α → ℝ) (hs : MeasurableSet s)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    μ.tilted f h s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · exact (Integrable.of_integral_ne_zero h.ne_zero).integrableOn.div_const _
  · exact ae_of_all _ (fun _ ↦ div_nonneg (exp_pos _).le (tilted_normalizer_pos (h := h)).le)

lemma tilted_apply_eq_ofReal_integral [SFinite μ] (f : α → ℝ) (s : Set α)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    μ.tilted f h s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
  · exact (Integrable.of_integral_ne_zero h.ne_zero).integrableOn.div_const _
  · exact ae_of_all _ (fun _ ↦ div_nonneg (exp_pos _).le (tilted_normalizer_pos (h := h)).le)

instance isProbabilityMeasure_tilted {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    IsProbabilityMeasure (μ.tilted f h) where
  measure_univ := by
    rw [tilted_apply_eq_ofReal_integral' f MeasurableSet.univ, setIntegral_univ,
      integral_div, div_self, ENNReal.ofReal_one]

private lemma aemeasurable_tilted_density {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    AEMeasurable (fun x ↦ exp (f x) / ∫ y, exp (f y) ∂μ) μ := by
  have hf := (Integrable.of_integral_ne_zero h.ne_zero).aemeasurable
  simpa only [div_eq_mul_inv₀] using hf.mul_const (∫ y, exp (f y) ∂μ)⁻¹

section lintegral

lemma setLIntegral_tilted' (f : α → ℝ) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ y, exp (f y) ∂μ) * g x ∂μ := by
  rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · exact (aemeasurable_tilted_density (h := h)).ennreal_ofReal.restrict
  · exact hs
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top

lemma setLIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → ℝ≥0∞) (s : Set α)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ y, exp (f y) ∂μ) * g x ∂μ := by
  rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
  · simp only [Pi.mul_apply]
  · exact (aemeasurable_tilted_density (h := h)).ennreal_ofReal.restrict
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top

lemma lintegral_tilted (f : α → ℝ) (g : α → ℝ≥0∞) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫⁻ x, g x ∂(μ.tilted f)
      = ∫⁻ x, ENNReal.ofReal (exp (f x) / ∫ y, exp (f y) ∂μ) * g x ∂μ := by
  rw [← setLIntegral_univ, setLIntegral_tilted' f g MeasurableSet.univ, setLIntegral_univ]

end lintegral

section integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma setIntegral_tilted' (f : α → ℝ) (g : α → E) {s : Set α} (hs : MeasurableSet s)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ y, exp (f y) ∂μ) • g x ∂μ := by
  rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
  · congr
  · rw [← aemeasurable_coe_nnreal_real_iff]
    exact (aemeasurable_tilted_density (h := h)).restrict

lemma setIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → E) (s : Set α)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ y, exp (f y) ∂μ) • g x ∂μ := by
  rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
  · congr
  · rw [← aemeasurable_coe_nnreal_real_iff]
    exact (aemeasurable_tilted_density (h := h)).restrict

lemma integral_tilted (f : α → ℝ) (g : α → E) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ y, exp (f y) ∂μ) • g x ∂μ := by
  rw [← setIntegral_univ, setIntegral_tilted' f g MeasurableSet.univ, setIntegral_univ]

end integral

lemma integral_exp_tilted (f g : α → ℝ) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ := by
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_eq_mul_inv₀, Pi.add_apply, exp_add]
  rw [← integral_mul_const]
  congr with x
  ring

/-- The normalizer for a second tilt exists exactly when the combined tilt exists. -/
lemma isUnit_integral_exp_tilted_iff (f g : α → ℝ) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    IsUnit (∫ x, exp (g x) ∂(μ.tilted f)) ↔ IsUnit (∫ x, exp ((f + g) x) ∂μ) := by
  rw [integral_exp_tilted]
  exact ⟨IsUnit.of_div₀, fun hfg ↦ hfg.div₀ h⟩

lemma tilted_tilted (g : α → ℝ) {hf : IsUnit (∫ x, exp (f x) ∂μ)}
    {hfg : IsUnit (∫ x, exp ((f + g) x) ∂μ)} :
    (μ.tilted f).tilted g ((isUnit_integral_exp_tilted_iff f g).mpr hfg) = μ.tilted (f + g) := by
  have hg : IsUnit (∫ x, exp (g x) ∂(μ.tilted f)) :=
    (isUnit_integral_exp_tilted_iff f g).mpr hfg
  have hnorm : (∫ x, exp ((f + g) x) ∂μ) =
      (∫ x, exp (g x) ∂(μ.tilted f)) * ∫ x, exp (f x) ∂μ :=
    (eq_div_iff_mul_eq.mp (integral_exp_tilted f g)).symm
  ext1 s hs
  rw [tilted_apply' _ _ hs, tilted_apply' _ _ hs, setLIntegral_tilted' f _ hs]
  congr with x
  rw [← ENNReal.ofReal_mul (div_nonneg (exp_pos _).le (tilted_normalizer_pos (h := hf)).le)]
  apply congrArg ENNReal.ofReal
  apply eq_div_iff_mul_eq.mpr
  simp only [hnorm]
  rw [Pi.add_apply, exp_add]
  field

lemma tilted_comm {g : α → ℝ} {hf : IsUnit (∫ x, exp (f x) ∂μ)}
    {hg : IsUnit (∫ x, exp (g x) ∂μ)} {hfg : IsUnit (∫ x, exp ((f + g) x) ∂μ)} :
    (μ.tilted f).tilted g ((isUnit_integral_exp_tilted_iff f g).mpr hfg) =
      (μ.tilted g).tilted f ((isUnit_integral_exp_tilted_iff g f).mpr (by
        simpa only [add_comm g f] using hfg)) := by
  have hgf : IsUnit (∫ x, exp ((g + f) x) ∂μ) := by simpa only [add_comm g f] using hfg
  rw [tilted_tilted g (hfg := hfg), tilted_tilted f (hfg := hgf)]
  exact tilted_congr (ae_of_all _ fun x ↦ congrFun (add_comm f g) x)

lemma tilted_neg_same' {hf : IsUnit (∫ x, exp (f x) ∂μ)}
    {hzero : IsUnit (∫ x, exp ((0 : α → ℝ) x) ∂μ)} :
    (μ.tilted f).tilted (-f) ((isUnit_integral_exp_tilted_iff f (-f)).mpr (by
      simpa only [add_neg_cancel] using hzero)) = (μ Set.univ)⁻¹ • μ := by
  have hsum : IsUnit (∫ x, exp ((f + -f) x) ∂μ) := by
    simpa only [add_neg_cancel] using hzero
  rw [tilted_tilted (-f) (hfg := hsum)]
  refine (tilted_congr (g := 0) (hg := hzero) (ae_of_all _ ?_)).trans (tilted_zero' μ)
  exact fun x ↦ congrFun (add_neg_cancel f) x

@[simp]
lemma tilted_tilted_neg {hf : IsUnit (∫ x, exp (f x) ∂μ)}
    {hneg : IsUnit (∫ x, exp ((-f) x) ∂(μ.tilted f hf))} :
    (μ.tilted f hf).tilted (-f) hneg = (μ Set.univ)⁻¹ • μ := by
  have hsum := (isUnit_integral_exp_tilted_iff f (-f)).mp hneg
  have hzero : IsUnit (∫ x, exp ((0 : α → ℝ) x) ∂μ) := by
    simpa only [add_neg_cancel] using hsum
  exact tilted_neg_same' (hzero := hzero)

lemma tilted_neg_same [IsProbabilityMeasure μ] {hf : IsUnit (∫ x, exp (f x) ∂μ)} :
    (μ.tilted f).tilted (-f) ((isUnit_integral_exp_tilted_iff f (-f)).mpr (by
      simpa only [add_neg_cancel, Pi.zero_apply] using
        isUnit_tilted_normalizer_const μ 0)) = μ := by
  simpa only [measure_univ, ENNReal.inv_one, one_smul] using
    (tilted_neg_same' (f := f) (hzero := isUnit_tilted_normalizer_const μ 0))

lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_tilted {h : IsUnit (∫ x, exp (f x) ∂μ)} : μ ≪ μ.tilted f := by
  refine withDensity_absolutelyContinuous' (aemeasurable_tilted_density (h := h)).ennreal_ofReal ?_
  exact ae_of_all _ fun _ ↦ (ENNReal.ofReal_pos.mpr
    (div_pos (exp_pos _) (tilted_normalizer_pos (h := h)))).ne'

lemma integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : α → E) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    Integrable g (μ.tilted f) ↔ Integrable (fun x ↦ exp (f x) • g x) μ := by
  have hpos := tilted_normalizer_pos (h := h)
  rw [Measure.tilted, integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_tilted_density (h := h)).ennreal_ofReal (by simp)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (exp_pos _).le hpos.le), div_eq_inv_mul₀,
    mul_smul]
  exact integrable_fun_smul_iff (inv_ne_zero (ha := h)) (fun x ↦ exp (f x) • g x)

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {h : IsUnit (∫ x, exp (f x) ∂ν)} :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (-f x) * ∫ x, exp (f x) ∂ν) * μ.rnDeriv ν x := by
  have hpos := tilted_normalizer_pos (h := h)
  refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
  · exact (aemeasurable_tilted_density (h := h)).ennreal_ofReal
  · exact ae_of_all _ fun _ ↦ (ENNReal.ofReal_pos.mpr (div_pos (exp_pos _) hpos)).ne'
  · exact ae_of_all _ (by simp)
  · filter_upwards with x
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos (div_pos (exp_pos _) hpos), exp_neg]
    congr 1
    apply inv_eq_of_mul_eq_one_right₀
    field

lemma toReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {h : IsUnit (∫ x, exp (f x) ∂ν)} :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (-f x) * (∫ x, exp (f x) ∂ν) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_right μ ν (h := h)] with x hx
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  exact mul_nonneg (exp_pos _).le (tilted_normalizer_pos (h := h)).le

variable (μ) in
lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ)) * μ.rnDeriv ν x := by
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) ?_ ?_
  · apply AEMeasurable.ennreal_ofReal
    simpa only [div_eq_mul_inv₀, Function.comp_apply] using
      (measurable_exp.comp_aemeasurable hfν).mul_const (∫ x, exp (f x) ∂μ)⁻¹
  · exact ae_of_all _ (by simp)

variable (μ) in
lemma toReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x) / (∫ x, exp (f x) ∂μ) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  exact div_nonneg (exp_pos _).le (tilted_normalizer_pos (h := h)).le

lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ)
    {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) := by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx, mul_one]

lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] {h : IsUnit (∫ x, exp (f x) ∂μ)} :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - log (∫ x, exp (f x) ∂μ) := by
  have hf := (Integrable.of_integral_ne_zero h.ne_zero).aemeasurable
  filter_upwards [rnDeriv_tilted_left_self (aemeasurable_of_aemeasurable_exp hf)] with x hx
  rw [hx, ENNReal.toReal_ofReal (div_nonneg (exp_pos _).le (tilted_normalizer_pos (h := h)).le),
    log_div (exp_pos _).ne', log_exp]

end MeasureTheory

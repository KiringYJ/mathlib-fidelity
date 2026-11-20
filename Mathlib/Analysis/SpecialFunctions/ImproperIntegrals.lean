/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`).

## See also

- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: specific integrals over finite intervals
- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: integral of `exp (-x ^ 2)`
- `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`: integrability of `(1+‖x‖)^(-r)`.
-/

public section


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integrableOn_exp_Iic (c : ℝ) : IntegrableOn exp (Iic c) := by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

theorem integrableOn_exp_neg_Ioi (c : ℝ) : IntegrableOn (fun (x : ℝ) => exp (-x)) (Ioi c) :=
  Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

theorem integral_exp_Iic (c : ℝ) : ∫ x : ℝ in Iic c, exp x = exp c := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

theorem integral_exp_Iic_zero : ∫ x : ℝ in Iic 0, exp x = 1 :=
  exp_zero ▸ integral_exp_Iic 0

theorem integral_exp_neg_Ioi (c : ℝ) : (∫ x : ℝ in Ioi c, exp (-x)) = exp (-c) := by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

theorem integral_exp_neg_Ioi_zero : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 := by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

theorem integrableOn_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using!
      (integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr <|
        integrableOn_exp_neg_Ioi _

theorem integrableOn_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Iic c) := by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

theorem integrableOn_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Ioi c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

theorem integrableOn_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Iic c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Iic (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

theorem integral_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    (∫ x : ℝ in Set.Ioi c, Complex.exp (a * x)) =
      Checked.div (-Complex.exp (a * c)) a (show a ≠ 0 by
        intro he
        simp [he] at ha).isUnit := by
  have ha0 : a ≠ 0 := by
    intro he
    simp [he] at ha
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) ha0, id_eq]
  suffices Tendsto (fun x : ℝ ↦ Complex.exp (a * x)) atTop (𝓝 0) by
    simpa using (this.sub_const _).div_const₀ _ (hy := ha0.isUnit)
  simpa [Complex.tendsto_exp_nhds_zero_iff] using tendsto_const_nhds.neg_mul_atTop ha tendsto_id

theorem integral_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    (∫ x : ℝ in Set.Iic c, Complex.exp (a * x)) =
      Checked.div (Complex.exp (a * c)) a (Complex.ne_zero_of_re_pos ha).isUnit := by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg, div_neg₀, neg_div₀,
    integral_comp_neg_Ioi (f := fun x : ℝ ↦ Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

theorem integral_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Real.exp (a * x) = - Real.exp (a * c) / a := by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re, integral_exp_mul_complex_Ioi (by simpa using ha), RCLike.re_to_complex,
    RCLike.re_to_complex, Complex.div_ofReal_re, Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using ha) _

theorem integral_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ in Set.Iic c, Real.exp (a * x) = Real.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, div_neg₀, neg_div₀,
    integral_comp_neg_Ioi (f := fun x : ℝ ↦ Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

/-- If `-m < c`, then `(fun t : ℝ ↦ (t + m) ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_add_rpow_Ioi_of_lt {a c m : ℝ} (ha : a < -1) (hc : -m < c) :
    IntegrableOn (fun (x : ℝ) ↦ (x + m) ^ a) (Ioi c) := by
  have h₀ : IsUnit (a + 1) := (show a + 1 ≠ 0 by linarith).isUnit
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t ↦ (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    have hx' : x + m ≠ 0 := by linarith [mem_Ici.mp hx]
    simpa [mul_div_cancel_left₀, add_sub_cancel_right] using
      ((((hasDerivAt_id x).add_const m).rpow_const (p := a + 1) (.inl hx')).div_const (a + 1)
        (hd := h₀))
  have ht : Tendsto (fun t ↦ (t + m) ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const₀
    refine (show Tendsto (fun t : ℝ ↦ t ^ (a + 1)) atTop (𝓝 0) from ?_).comp
      (tendsto_atTop_add_const_right _ m tendsto_id)
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht ↦ rpow_nonneg (by linarith [mem_Ioi.mp ht]) a) ht

/-- If `0 < c`, then `(fun t : ℝ ↦ t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_Ioi_rpow_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t ^ a) (Ioi c) := by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

theorem integrableOn_Ioi_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioi t) ↔ s < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  let S : Set ℝ := Ioi (max 1 t) \ {0}
  have hS : S = Ioi (max 1 t) := by
    refine sdiff_eq_left.mpr (disjoint_singleton_right.mpr ?_)
    exact notMem_Ioi.mpr (zero_le_one.trans (le_max_left _ _))
  have hs : MeasurableSet S := hS.symm ▸ measurableSet_Ioi
  have hone (x : S) : 1 ≤ x.val := (le_max_left _ _).trans (mem_Ioi.mp x.2.1).le
  have hpow : Integrable (fun x : S ↦ x.val ^ s) (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (f := fun t : ℝ ↦ t ^ s) (μ := volume) hs).mp
      (hS.symm ▸ H')
  apply not_integrableOn_Ioi_inv (a := max 1 t)
  apply hpow.mono' (continuous_subtype_val.fun_inv₀ (h0 := fun x : S ↦
    Ne.isUnit x.2.2)).aestronglyMeasurable
  filter_upwards [] with x
  calc
    ‖Checked.inv x.val (Ne.isUnit x.2.2)‖ = Checked.inv x.val (Ne.isUnit x.2.2) := by
      simp only [norm_inv, norm_of_nonneg (zero_le_one.trans (hone x))]
    _ = x.val ^ (-1 : ℝ) := (Real.rpow_neg_one x.val (hx := Ne.isUnit x.2.2)).symm
    _ ≤ x.val ^ s := rpow_le_rpow_of_exponent_le (hone x) h

theorem integrableAtFilter_rpow_atTop_iff {s : ℝ} :
    IntegrableAtFilter (fun x : ℝ ↦ x ^ s) atTop ↔ s < -1 := by
  refine ⟨fun ⟨t, ht, hint⟩ ↦ ?_, fun h ↦
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
  exact hint.mono_set <| fun x hx ↦ ha _ <| (le_max_left a 1).trans hx.le

/-- The real power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_rpow (s : ℝ) : ¬ IntegrableOn (fun x ↦ x ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioi (1 : ℝ)) := h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_rpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem not_integrableOn_Ioi_rpow_of_neg_one_le {a s : ℝ} (hs : -1 ≤ s) :
    ¬ IntegrableOn (fun x ↦ x ^ s) (Ioi a) := by
  refine fun h ↦ not_lt.mpr hs ?_
  rw [← integrableAtFilter_rpow_atTop_iff]
  exact ⟨Ioi a, Ioi_mem_atTop a, h⟩

theorem setIntegral_Ioi_zero_rpow (s : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

theorem integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi c, t ^ a =
      Checked.div (-c ^ (a + 1)) (a + 1) (show a + 1 ≠ 0 by linarith).isUnit := by
  have h₀ : IsUnit (a + 1) := (show a + 1 ≠ 0 by linarith).isUnit
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    simpa [mul_div_cancel_left₀] using
      (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const
        (a + 1) (hd := h₀)
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const₀
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht using 1
  simp only [neg_div₀, zero_div, zero_sub]

theorem integrableOn_Ioi_norm_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ ‖(t : ℂ) ^ a‖) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

theorem integrableOn_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp <| integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

theorem integrableOn_Ioi_norm_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Ioi t) ↔ s.re < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_norm_cpow_of_lt h ht⟩
  refine (integrableOn_Ioi_rpow_iff ht).mp <| h.congr_fun (fun a ha ↦ ?_) measurableSet_Ioi
  #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
  instantiation order leads to a term with a beta redex.
  https://github.com/leanprover/lean4/pull/13762
  This will be removed once app elaboration itself does beta reduction. -/
  dsimp only
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht.trans ha)]

theorem integrableOn_Ioi_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi t) ↔ s.re < -1 :=
  ⟨fun h ↦ (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h ↦ integrableOn_Ioi_cpow_of_lt h ht⟩

theorem integrableOn_Ioi_deriv_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re < 0) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ s) (Set.Ioi t) := by
  have h : IntegrableOn (fun x : ℝ ↦ s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpow_const (ht.trans hx).ne' (fun h ↦ (Complex.zero_re ▸ h ▸ hs).false)]

theorem integrableOn_Ioi_deriv_norm_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re ≤ 0) :
    IntegrableOn (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Set.Ioi t) := by
  have heq : EqOn (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ s‖)
      (fun x : ℝ ↦ s.re * x ^ (s.re - 1)) (Ioi t) :=
    fun _ hx ↦ deriv_norm_ofReal_cpow s (ht.trans hx)
  rw [integrableOn_congr_fun heq measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (integrableOn_Ioi_rpow_of_lt hs ht).const_mul s.re

/-- The complex power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_cpow (s : ℂ) :
    ¬ IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi 1) :=
      h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_cpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem setIntegral_Ioi_zero_cpow (s : ℂ) : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) =
      Checked.div (-(c : ℂ) ^ (a + 1)) (a + 1) (show a + 1 ≠ 0 by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
        linarith).isUnit := by
  have h₀ : IsUnit (a + 1) := (show a + 1 ≠ 0 by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith).isUnit
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.congr' ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
    have ha' : a ≠ -1 := fun h ↦ ha.ne (by
      simpa only [Complex.neg_re, Complex.one_re] using congrArg Complex.re h)
    exact (integral_cpow (a := c) (b := x) (r := a)
      (Or.inr ⟨ha', notMem_uIcc_of_lt hc hx⟩)).symm
  simp_rw [← zero_sub, sub_div]
  refine (Tendsto.div_const₀ ?_ _ (hy := h₀)).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
  simp_rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

theorem integrable_inv_one_add_sq : Integrable fun (x : ℝ) ↦
    Checked.inv (1 + x ^ 2) (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit := by
  suffices h : Integrable fun (x : ℝ) ↦ (1 + ‖x‖ ^ 2) ^ ((-2 : ℝ) / 2) by
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [show (-2 : ℝ) / 2 = -1 by norm_num, Real.norm_eq_abs, sq_abs]
    exact rpow_neg_one _ (hx := (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit)
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]
theorem integral_Iic_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Iic i, Checked.inv (1 + x ^ 2)
      (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    |>.trans (sub_neg_eq_add _ _)

@[simp]
theorem integral_Ioi_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Ioi i, Checked.inv (1 + x ^ 2)
      (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]
theorem integral_univ_inv_one_add_sq :
    ∫ (x : ℝ), Checked.inv (1 + x ^ 2) (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit = π :=
  (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

theorem integrable_inv_one_add_mul_sq {b : ℝ} (hb : b ≠ 0) :
    Integrable fun x ↦ Checked.inv (1 + (b * x) ^ 2)
      (show 0 < 1 + (b * x) ^ 2 by positivity).ne'.isUnit :=
  integrable_inv_one_add_sq.comp_mul_left' hb

@[simp]
theorem integral_univ_inv_one_add_mul_sq (b : ℝ) {hb : b ≠ 0} :
    ∫ x, Checked.inv (1 + (b * x) ^ 2)
      (show 0 < 1 + (b * x) ^ 2 by positivity).ne'.isUnit =
        Checked.div π |b| (abs_ne_zero.mpr hb).isUnit := by
  rw [Measure.integral_comp_mul_left (fun x ↦ Checked.inv (1 + x ^ 2)
    (show 0 < 1 + x ^ 2 by positivity).ne'.isUnit) b (ha := hb.isUnit),
    integral_univ_inv_one_add_sq]
  simp [div_eq_inv_mul₀]

private theorem inv_mul_one_add_log_sq (b : ℝ) (t : Ioi (0 : ℝ)) :
    Checked.inv (t.val * (1 + (b * log t.val) ^ 2))
        (mul_ne_zero t.2.ne' (show 0 < 1 + (b * log t.val) ^ 2 by positivity).ne').isUnit =
      Checked.inv t.val t.2.ne'.isUnit •
        Checked.inv (1 + (b * log t.val) ^ 2)
          (show 0 < 1 + (b * log t.val) ^ 2 by positivity).ne'.isUnit := by
  rw [mul_inv_rev₀, smul_eq_mul, mul_comm]

theorem integrableOn_Ioi_zero_inv_mul_one_add_log_sq {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun t : Ioi (0 : ℝ) ↦
      Checked.inv (t.val * (1 + (b * log t.val) ^ 2))
        (mul_ne_zero t.2.ne' (show 0 < 1 + (b * log t.val) ^ 2 by positivity).ne').isUnit)
      (volume.comap Subtype.val) := by
  simp_rw [inv_mul_one_add_log_sq]
  exact (integrableOn_comp_log_Ioi_zero (fun u ↦ Checked.inv (1 + (b * u) ^ 2)
    (show 0 < 1 + (b * u) ^ 2 by positivity).ne'.isUnit)).mpr
    (integrable_inv_one_add_mul_sq hb)

/-- The mass of the log-Cauchy density on the positive half-line for a nonzero scale. -/
theorem integral_Ioi_zero_inv_mul_one_add_log_sq (b : ℝ) {hb : IsUnit b} :
    (∫ t : Ioi (0 : ℝ),
      Checked.inv (t.val * (1 + (b * log t.val) ^ 2))
        (mul_ne_zero t.2.ne' (show 0 < 1 + (b * log t.val) ^ 2 by positivity).ne').isUnit
          ∂(volume.comap Subtype.val)) = π / |b| := by
  simp_rw [inv_mul_one_add_log_sq]
  exact (integral_comp_log_Ioi_zero (fun u ↦ Checked.inv (1 + (b * u) ^ 2)
    (show 0 < 1 + (b * u) ^ 2 by positivity).ne'.isUnit)).trans
    (integral_univ_inv_one_add_mul_sq b (hb := hb.ne_zero))

private theorem integrable_integral_inv_div_log_sq_Ioi {c : ℝ} (hc : 1 < c) :
    let g (t : Ioi c) :=
      Checked.div (Checked.inv t.val (zero_lt_one.trans (hc.trans t.2)).ne'.isUnit)
        (log t.val ^ 2) ((log_pos (hc.trans t.2)).ne'.isUnit.pow 2)
    Integrable g (volume.comap Subtype.val) ∧
      (∫ t, g t ∂(volume.comap Subtype.val)) = Checked.inv (log c) (log_pos hc).ne'.isUnit := by
  let D := Ioi (1 : ℝ)
  have h₀ (t : D) : IsUnit t.val := (zero_lt_one.trans t.2).ne'.isUnit
  have hl (t : D) : IsUnit (log t.val) := (log_pos t.2).ne'.isUnit
  let f (t : D) := -(Checked.inv (log t.val) (hl t))
  let g (t : D) := Checked.div (Checked.inv t.val (h₀ t)) (log t.val ^ 2) ((hl t).pow 2)
  let F : ℝ → ℝ := Function.extend Subtype.val f 0
  let G : ℝ → ℝ := Function.extend Subtype.val g 0
  have hF (t : D) : F t.val = f t := Subtype.val_injective.extend_apply _ _ _
  have hG (t : D) : G t.val = g t := Subtype.val_injective.extend_apply _ _ _
  let j (t : D) : {x : ℝ // IsUnit (log x)} := ⟨t.val, hl t⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk hl
  have hd (t : D) : HasDerivAt f (g t) t Subtype.val := by
    let J (x : D) := Checked.inv (log x.val) (hl x)
    have hJ : HasDerivAt J (-g t) t Subtype.val := by
      change HasDerivAtFilter J (-g t) (𝓝 t ×ˢ pure t) (fun x : D ↦ x.val)
      simpa only [J, g, j, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul, neg_div₀] using
        ((Real.hasDerivAt_inv_log (j t)).hasFDerivAt.comp_tendsto j
          (hj.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))).hasDerivAtFilter
    simpa only [f, J, Function.comp_def, neg_mul, one_mul, neg_neg] using
      (hasDerivAt_neg (J t)).comp (h := J) (coord' := id) t hJ continuousAt_subtype_val
  have hderiv (t : ℝ) (ht : t ∈ Ici c) : HasDerivAt F (G t) t := by
    let x : D := ⟨t, hc.trans_le ht⟩
    have hd' : HasFDerivAt (fun y : D ↦ F y.val)
        (ContinuousLinearMap.toSpanSingleton ℝ (g x)) x Subtype.val := by
      simpa only [hF] using (hd x).hasFDerivAt
    rw [show G t = g x from hG x]
    have hN : D ∈ 𝓝 x.val := Ioi_mem_nhds x.2
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hasFDerivAt_iff_hasDerivAt.mp (hd'.of_restrict (coord := id) (x := x) hN)
  have hGpos (t : ℝ) (ht : t ∈ Ioi c) : 0 ≤ G t := by
    let x : D := ⟨t, hc.trans ht⟩
    rw [show G t = g x from hG x]
    exact div_nonneg (inv_nonneg.mpr (zero_lt_one.trans x.2).le) (sq_nonneg _)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hlog : Tendsto (fun t : D ↦ log t.val) (comap Subtype.val atTop) atTop :=
      tendsto_log_atTop.comp tendsto_comap
    apply (tendsto_comap_val_iff (Ioi_mem_atTop (1 : ℝ))).mp
    change Tendsto (fun t : D ↦ F t.val) (comap Subtype.val atTop) (𝓝 0)
    have h := (hlog.fun_inv_tendsto_atTop (h0 := hl)).neg
    simpa only [neg_zero] using h.congr (fun t ↦ (hF t).symm)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hderiv hGpos hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hGpos hlim
  refine ⟨?_, ?_⟩
  · exact ((integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi).congr
      (Eventually.of_forall fun t ↦ hG ⟨t.val, hc.trans t.2⟩)
  · calc
      _ = ∫ t in Ioi c, G t := by
        rw [← integral_subtype_comap measurableSet_Ioi G]
        exact integral_congr_ae (Eventually.of_forall fun t ↦ (hG ⟨t.val, hc.trans t.2⟩).symm)
      _ = 0 - F c := he
      _ = _ := by rw [show F c = f ⟨c, hc⟩ from hF ⟨c, hc⟩]; simp [f]

@[simp]
theorem integrableOn_inv_div_log_sq_Ioi {c : ℝ} (hc : 1 < c) :
    Integrable (fun t : Ioi c ↦
      Checked.div (Checked.inv t.val (zero_lt_one.trans (hc.trans t.2)).ne'.isUnit)
        (log t.val ^ 2) ((log_pos (hc.trans t.2)).ne'.isUnit.pow 2))
      (volume.comap Subtype.val) :=
  (integrable_integral_inv_div_log_sq_Ioi hc).1

@[simp]
theorem integral_inv_div_log_sq_Ioi {c : ℝ} (hc : 1 < c) :
    (∫ t : Ioi c,
      Checked.div (Checked.inv t.val (zero_lt_one.trans (hc.trans t.2)).ne'.isUnit)
        (log t.val ^ 2) ((log_pos (hc.trans t.2)).ne'.isUnit.pow 2)
          ∂(volume.comap Subtype.val)) = Checked.inv (log c) (log_pos hc).ne'.isUnit :=
  (integrable_integral_inv_div_log_sq_Ioi hc).2

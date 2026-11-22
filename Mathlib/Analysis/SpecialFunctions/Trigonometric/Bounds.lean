/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial bounds for trigonometric functions

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `Trigonometric.Basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x` we have `x - x ^ 3 / 6 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.
* `arctan_lt_self`: for `x > 0` we have `arctan x < x`.
* `cos_le_one_div_sqrt_sq_add_one` and `cos_lt_one_div_sqrt_sq_add_one`: for
  `-3 * π / 2 ≤ x ≤ 3 * π / 2`, we have `cos x ≤ 1 / sqrt (x ^ 2 + 1)`, with strict inequality if
  `x ≠ 0`. (This bound is not quite optimal, but not far off)

## Tags

sin, cos, tan, angle
-/

public section

open Set

namespace Real
variable {x : ℝ}

/-- For 0 < x, we have sin x < x. -/
theorem sin_lt (h : 0 < x) : sin x < x := by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| ≤ 1 by rwa [hx])
  rw [sub_le_iff_le_add', hx] at this
  apply this.trans_lt
  have hpow : x ^ 5 ≤ x ^ 3 := pow_le_pow_of_le_one h.le h' (by decide)
  linarith [pow_pos h 3]

lemma sin_le (hx : 0 ≤ x) : sin x ≤ x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

lemma lt_sin (hx : x < 0) : x < sin x := by simpa using sin_lt <| neg_pos.2 hx
lemma le_sin (hx : x ≤ 0) : x ≤ sin x := by simpa using sin_le <| neg_nonneg.2 hx

theorem lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin (π / 2 * x) := by
  have h : ∀ ⦃z : ℝ⦄, 0 ≤ z → z ≤ π → z = π / 2 * x → x < sin z := by
    simpa [mul_comm x] using
      strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
        pi_div_two_pos.ne (sub_pos.2 hx') hx
  exact h (by positivity) (by nlinarith [mul_nonneg pi_div_two_pos.le (sub_nonneg.mpr hx'.le)]) rfl

theorem le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin (π / 2 * x) := by
  have h : ∀ ⦃z : ℝ⦄, 0 ≤ z → z ≤ π → z = π / 2 * x → x ≤ sin z := by
    simpa [mul_comm x] using
      strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
        ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
        (sub_nonneg.2 hx') hx
  exact h (by positivity)
    (by nlinarith [mul_nonneg pi_div_two_pos.le (sub_nonneg.mpr hx'), pi_pos]) rfl

theorem mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : 2 / π * x < sin x := by
  have hcancel : π / 2 * (x / (π / 2)) = x := mul_div_cancel₀ x
  have hscale : 2 / π * x = x / (π / 2) := by rw [div_eq_inv_mul₀ x (π / 2), inv_div₀]
  have h := lt_sin_mul (div_pos hx pi_div_two_pos) ((div_lt_one pi_div_two_pos).mpr hx')
  rwa [hcancel, ← hscale] at h

/-- One half of **Jordan's inequality**.

In the range `[0, π / 2]`, we have a linear lower bound on `sin`. The other half is given by
`Real.sin_le`.
-/
theorem mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : 2 / π * x ≤ sin x := by
  have hcancel : π / 2 * (x / (π / 2)) = x := mul_div_cancel₀ x
  have hscale : 2 / π * x = x / (π / 2) := by rw [div_eq_inv_mul₀ x (π / 2), inv_div₀]
  have h := le_sin_mul (div_nonneg hx pi_div_two_pos.le) ((div_le_one pi_div_two_pos).mpr hx')
  rwa [hcancel, ← hscale] at h

/-- Half of **Jordan's inequality** for negative values. -/
lemma sin_le_mul (hx : -(π / 2) ≤ x) (hx₀ : x ≤ 0) : sin x ≤ 2 / π * x := by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

/-- Half of **Jordan's inequality** for absolute values. -/
lemma mul_abs_le_abs_sin (hx : |x| ≤ π / 2) : 2 / π * |x| ≤ |sin x| := by
  wlog hx₀ : 0 ≤ x
  case inr => simpa using this (by rwa [abs_neg]) <| neg_nonneg.2 <| le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

lemma sin_sq_lt_sq (hx : x ≠ 0) : sin x ^ 2 < x ^ 2 := by
  wlog! hx₀ : 0 < x
  case inr =>
    simpa using this (neg_ne_zero.2 hx) <| neg_pos_of_neg <| hx.lt_of_le hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact (sin_sq_le_one _).trans_lt (by rwa [one_lt_sq_iff₀ hx₀.le])

lemma sin_sq_le_sq : sin x ^ 2 ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

lemma abs_sin_lt_abs (hx : x ≠ 0) : |sin x| < |x| := sq_lt_sq.1 (sin_sq_lt_sq hx)
lemma abs_sin_le_abs : |sin x| ≤ |x| := sq_le_sq.1 sin_sq_le_sq

lemma one_sub_sq_div_two_lt_cos (hx : x ≠ 0) : 1 - x ^ 2 / 2 < cos x := by
  have := (sin_sq_lt_sq (by positivity)).trans_eq' (sin_sq_eq_half_sub (x / 2))
  ring_nf at this
  linarith

lemma one_sub_sq_div_two_le_cos : 1 - x ^ 2 / 2 ≤ cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (one_sub_sq_div_two_lt_cos hx).le

/-- Half of **Jordan's inequality** for `cos`. -/
lemma one_sub_mul_le_cos (hx₀ : 0 ≤ x) (hx : x ≤ π / 2) : 1 - 2 / π * x ≤ cos x := by
  simpa [sin_pi_div_two_sub, mul_sub, div_mul_div_comm₀, mul_comm π, pi_pos.ne']
    using mul_le_sin (x := π / 2 - x) (by simpa) (by simpa)

/-- Half of **Jordan's inequality** for `cos` and negative values. -/
lemma one_add_mul_le_cos (hx₀ : -(π / 2) ≤ x) (hx : x ≤ 0) : 1 + 2 / π * x ≤ cos x := by
  simpa using one_sub_mul_le_cos (x := -x) (by linarith) (by linarith)

lemma cos_le_one_sub_mul_cos_sq (hx : |x| ≤ π) : cos x ≤ 1 - 2 / π ^ 2 * x ^ 2 := by
  wlog hx₀ : 0 ≤ x
  case inr => simpa using this (by rwa [abs_neg]) <| neg_nonneg.2 <| le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx
  have : x / π ≤ sin (x / 2) := by simpa using mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have := (pow_le_pow_left₀ (by positivity) this 2).trans_eq (sin_sq_eq_half_sub _)
  ring_nf at this ⊢
  linarith

/-- For 0 < x we have x - x ^ 3 / 6 < sin x.

This inequality is tight, in that the constant 6 is best possible. -/
theorem sin_gt_sub_cube {x : ℝ} (hx : 0 < x) : x - x ^ 3 / 6 < Real.sin x := by
  let f (t : ℝ) : ℝ := Real.sin t - (t - t ^ 3 / 6)
  have hderiv (t : ℝ) : deriv f t = cos t - 1 + t ^ 2 / 2 := by
    have hpow := (hasDerivAt_pow 3 t).div_const 6 (hd := (by norm_num : (6 : ℝ) ≠ 0).isUnit)
    have hd := (hasDerivAt_sin t).sub ((hasDerivAt_id t).sub hpow)
    have hval := hd.deriv
    simp only [Pi.sub_def, id_eq, Nat.cast_ofNat] at hval
    change deriv (fun y : ℝ ↦ sin y - (y - y ^ 3 / 6)) t id = _ at hval ⊢
    rw [hval]
    ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    grind [one_sub_sq_div_two_lt_cos, interior_Ici]
  have h0 : f 0 < f x := hmono (by simp) hx.le hx
  simpa [f, sub_pos] using h0

/-- For 0 ≤ x we have x - x ^ 3 / 6 ≤ sin x.

This inequality is tight, in that the constant 6 is best possible. -/
theorem sin_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  exact (sin_gt_sub_cube hx).le

/-- `|x - sin x| ≤ |x|³ / 6` for every real `x`. -/
theorem abs_sub_sin_le (x : ℝ) : |x - Real.sin x| ≤ |x| ^ 3 / 6 := by
  wlog hx : 0 ≤ x
  · grind [sin_neg]
  · grind [Real.sin_le, abs_of_nonneg, sin_ge_sub_cube]

/-- The derivative of `tan x - x` is `1/(cos x)^2 - 1` away from the zeroes of cos. -/
theorem deriv_tan_sub_id (x : ℝ) (h : cos x ≠ 0) :
    deriv (fun y : {y : ℝ // cos y ≠ 0} ↦ tan y y.2 - y.val) ⟨x, h⟩ Subtype.val =
      1 / cos x ^ 2 - 1 := by
  have hval : HasDerivAt (Subtype.val : {y : ℝ // cos y ≠ 0} → ℝ) 1 ⟨x, h⟩ Subtype.val :=
    HasFDerivAtFilter.comp_tendsto (hasDerivAt_id x).hasFDerivAt _
      ((continuous_subtype_val.tendsto _).prodMap (Filter.tendsto_pure_pure ..))
  have hd := ((hasDerivAt_tan h).hasFDerivAt.sub hval.hasFDerivAt).hasDerivAt
  simpa only [sub_apply, Pi.sub_def, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    using hd.deriv (isOpen_ne_fun continuous_cos continuous_const).isOpenEmbedding_subtypeVal

/-- For all `0 < x < π/2` we have `x < tan x`.

This is proved by checking that the function `sin x - x * cos x` vanishes at zero and has positive
derivative `x * sin x` on `(0, π / 2)`. -/
theorem lt_tan {x : ℝ} (h1 : 0 < x) (h2 : x < π / 2) :
    x < tan x (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩).ne' := by
  have hcos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩
  rw [tan_eq_sin_div_cos, lt_div_iff₀ hcos]
  let g : ℝ → ℝ := fun y ↦ sin y - y * cos y
  have hg (y : ℝ) : HasDerivAt g (y * sin y) y := by
    convert (hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (hasDerivAt_cos y)) using 1
    · rfl
    · simp only [id]; ring
  have mono : StrictMonoOn g (Ico 0 (π / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 (π / 2))
      (continuous_sin.sub (continuous_id.mul continuous_cos)).continuousOn fun y hy ↦ ?_
    rw [interior_Ico] at hy
    rw [(hg y).deriv]
    exact mul_pos hy.1 (sin_pos_of_pos_of_lt_pi hy.1 (by linarith [hy.2, pi_pos]))
  have := mono ⟨le_rfl, by linarith [pi_pos]⟩ ⟨h1.le, h2⟩ h1
  simp only [g, sin_zero, zero_mul, sub_zero] at this
  linarith

theorem le_tan {x : ℝ} (h1 : 0 ≤ x) (h2 : x < π / 2) :
    x ≤ tan x (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩).ne' := by
  rcases eq_or_lt_of_le h1 with (rfl | h1')
  · rw [tan_zero]
  · exact le_of_lt (lt_tan h1' h2)

/-- For `0 < x` we have `arctan x < x`.

This is `lt_tan` reflected in the diagonal: `tan` lies above the identity on `(0, π / 2)`, hence
its inverse lies below it. -/
theorem arctan_lt_self (h : 0 < x) : arctan x < x := by
  simpa using lt_tan (arctan_pos.2 h) (arctan_lt_pi_div_two x)

theorem arctan_le_self (h : 0 ≤ x) : arctan x ≤ x := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · exact (arctan_lt_self h).le

theorem self_lt_arctan (h : x < 0) : x < arctan x := by
  simpa using arctan_lt_self <| neg_pos.2 h

theorem self_le_arctan (h : x ≤ 0) : x ≤ arctan x := by
  simpa using arctan_le_self <| neg_nonneg.2 h

theorem abs_arctan_lt_abs (h : x ≠ 0) : |arctan x| < |x| := by
  grind [arctan_lt_self, self_lt_arctan, arctan_pos, arctan_lt_zero]

theorem abs_arctan_le_abs : |arctan x| ≤ |x| := by
  grind [abs_arctan_lt_abs, arctan_zero]

theorem cos_lt_one_div_sqrt_sq_add_one {x : ℝ} (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2)
    (hx3 : x ≠ 0) : cos x < (1 / √(x ^ 2 + 1) : ℝ) := by
  suffices ∀ {y : ℝ}, 0 < y → y ≤ 3 * π / 2 → cos y < 1 / √(y ^ 2 + 1) by
    rcases lt_or_lt_iff_ne.mpr hx3.symm with ⟨h⟩
    · exact this h hx2
    · convert! this (by linarith : 0 < -x) (by linarith) using 1
      · rw [cos_neg]
      · rw [div_eq_div_iff]
        simp
  intro y hy1 hy2
  have hy3 : ↑0 < y ^ 2 + 1 := by linarith [sq_nonneg y]
  rcases lt_or_ge y (π / 2) with (hy2' | hy1')
  · -- Main case : `0 < y < π / 2`
    have hy4 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy2'⟩
    rw [lt_div_iff₀ (sqrt_pos_of_pos hy3)]
    apply (sq_lt_sq₀ (mul_nonneg hy4.le (sqrt_nonneg _)) zero_le_one).mp
    rw [mul_pow, sq_sqrt hy3.le]
    have htan := lt_tan hy1 hy2'
    rw [tan_eq_sin_div_cos, lt_div_iff₀ hy4] at htan
    have hs := (sq_lt_sq₀ (mul_pos hy1 hy4).le
      (sin_nonneg_of_nonneg_of_le_pi hy1.le (by linarith [pi_pos]))).mpr htan
    nlinarith only [hs, sin_sq_add_cos_sq y]
  · -- Easy case : `π / 2 ≤ y ≤ 3 * π / 2`
    refine lt_of_le_of_lt ?_ (one_div_pos.mpr <| sqrt_pos_of_pos hy3)
    exact cos_nonpos_of_pi_div_two_le_of_le hy1' (by linarith [pi_pos])

theorem cos_le_one_div_sqrt_sq_add_one {x : ℝ} (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2) :
    cos x ≤ (1 : ℝ) / √(x ^ 2 + 1) := by
  rcases eq_or_ne x 0 with (rfl | hx3)
  · simp
  · exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le

theorem lipschitzWith_sin : LipschitzWith 1 sin :=
  lipschitzWith_of_nnnorm_deriv_le differentiable_sin fun x ↦ by
    rw [(hasDerivAt_sin x).deriv]
    exact_mod_cast abs_cos_le_one x

theorem lipschitzWith_cos : LipschitzWith 1 cos :=
  lipschitzWith_of_nnnorm_deriv_le differentiable_cos fun x ↦ by
    rw [(hasDerivAt_cos x).deriv]
    simpa [← NNReal.coe_le_coe, Real.norm_eq_abs] using abs_sin_le_one x

theorem abs_sin_sub_sin_le (x y : ℝ) : |sin x - sin y| ≤ |x - y| := by
  simpa [edist_dist] using! lipschitzWith_sin x y

theorem abs_cos_sub_cos_le (x y : ℝ) : |cos x - cos y| ≤ |x - y| := by
  simpa [edist_dist] using! lipschitzWith_cos x y

theorem norm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖ ≤ ‖x‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    _ = 2 * |Real.sin (x / 2)| := by simp
    _ ≤ 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
    _ = _ := by
      rw [Real.norm_eq_abs, abs_div]
      field_simp
      norm_num [mul_comm]

theorem enorm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖ₑ ≤ ‖x‖ₑ := by
  iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

theorem nnnorm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖.exp (.I * x) - (1 : ℂ)‖₊ ≤ ‖x‖₊ := by
  rw [← ENNReal.coe_le_coe]; exact enorm_exp_I_mul_ofReal_sub_one_le

end Real

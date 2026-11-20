/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.

This file is still being developed.

## Tags

integrate, integration, integrable
-/

public section


open Real Set Finset Filter

open scoped Real Interval Topology

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} (c d : ℝ)

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/
section

@[simp]
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c

@[simp]
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c

theorem inv_mul_integral_comp_div {hc : IsUnit c} :
    (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c

@[simp]
theorem mul_integral_comp_mul_add :
    (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d

@[simp]
theorem mul_integral_comp_add_mul :
    (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d

theorem inv_mul_integral_comp_div_add {hc : IsUnit c} :
    (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d

theorem inv_mul_integral_comp_add_div {hc : IsUnit c} :
    (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d

@[simp]
theorem mul_integral_comp_mul_sub :
    (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d

@[simp]
theorem mul_integral_comp_sub_mul :
    (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d

theorem inv_mul_integral_comp_div_sub {hc : IsUnit c} :
    (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d

theorem inv_mul_integral_comp_sub_div {hc : IsUnit c} :
    (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d

end

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


/-- An exponent satisfying the hypotheses for the complex power integral is different from `-1`. -/
theorem complex_add_one_ne_zero_of_exponent {r : ℂ}
    (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) : r + 1 ≠ 0 := by
  rw [Ne, add_eq_zero_iff_eq_neg]
  rcases h with h | h
  · intro hr
    simp [hr] at h
  · exact h.1

theorem integral_cpow {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x : ℝ in a..b, (x : ℂ) ^ r) =
      Checked.div ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) (r + 1)
        (complex_add_one_ne_zero_of_exponent h).isUnit := by
  have hr : IsUnit (r + 1) := (complex_add_one_ne_zero_of_exponent h).isUnit
  let F (x : ℝ) := Checked.div ((x : ℂ) ^ (r + 1)) (r + 1) hr
  have hF (x : ℝ) (hx : x ≠ 0) : HasDerivAt F ((x : ℂ) ^ r) x :=
    hasDerivAt_ofReal_cpow_const' (r := r) (hr := hr) hx
  rw [_root_.sub_div]
  change (∫ x : ℝ in a..b, (x : ℂ) ^ r) = F b - F a
  by_cases hab : (0 : ℝ) ∉ [[a, b]]
  · exact integral_eq_sub_of_hasDerivAt (f := F) (fun x hx ↦ hF x (ne_of_mem_of_not_mem hx hab))
      (intervalIntegrable_cpow (r := r) <| Or.inr hab)
  replace h : -1 < r.re := by tauto
  suffices ∀ c : ℝ, (∫ x : ℝ in 0..c, (x : ℂ) ^ r) = F c - F 0 by
    rw [← integral_add_adjacent_intervals (@intervalIntegrable_cpow' a 0 r h)
      (@intervalIntegrable_cpow' 0 b r h), integral_symm, this a, this b]
    abel
  intro c
  apply integral_eq_sub_of_hasDeriv_right (f := F)
  · simp only [F, div_eq_mul_inv₀]
    refine ((Complex.continuous_ofReal_cpow_const ?_).mul continuous_const).continuousOn
    rwa [Complex.add_re, Complex.one_re, ← neg_lt_iff_pos_add]
  · intro x hx
    apply (hF x ?_).hasDerivWithinAt
    rcases le_total c 0 with (hc | hc)
    · rw [max_eq_left hc] at hx
      exact hx.2.ne
    · rw [min_eq_left hc] at hx
      exact hx.1.ne'
  · exact intervalIntegrable_cpow' h

/-- An exponent satisfying the hypotheses for the real power integral is different from `-1`. -/
theorem real_add_one_ne_zero_of_exponent {r : ℝ}
    (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) : r + 1 ≠ 0 := by
  rw [Ne, add_eq_zero_iff_eq_neg]
  exact h.elim (·.ne') And.left

theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x in a..b, x ^ r) =
      Checked.div (b ^ (r + 1) - a ^ (r + 1)) (r + 1)
        (real_add_one_ne_zero_of_exponent h).isUnit := by
  have hr := real_add_one_ne_zero_of_exponent h
  have h' : -1 < (r : ℂ).re ∨ (r : ℂ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  have := integral_cpow h'
  apply_fun Complex.re at this; convert! this
  · simp_rw [intervalIntegral_eq_integral_uIoc, Complex.real_smul, Complex.re_ofReal_mul, rpow_def,
      ← RCLike.re_eq_complex_re, smul_eq_mul]
    rw [integral_re]
    refine intervalIntegrable_iff.mp ?_
    rcases h' with h' | h'
    · exact intervalIntegrable_cpow' h'
    · exact intervalIntegrable_cpow (Or.inr h'.2)
  · have hInv : Checked.inv ((r + 1 : ℝ) : ℂ) (hr.isUnit.map Complex.ofRealHom) =
        ((Checked.inv (r + 1) hr.isUnit : ℝ) : ℂ) :=
      (Complex.ofReal_inv (r + 1) (hr := hr.isUnit)).symm
    simp only [(by push_cast; rfl : (r : ℂ) + 1 = ((r + 1 : ℝ) : ℂ)), div_eq_inv_mul₀,
      hInv, Complex.re_ofReal_mul, Complex.sub_re, rpow_def]

theorem integral_zpow {n : ℤ} (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    integralSubtype (fun x : [[a, b]] ↦ Checked.zpow x.val n fun hn ↦
      (ne_of_mem_of_not_mem x.2 (h.resolve_left hn.not_ge).2).isUnit) =
      Checked.div
        (Checked.zpow b (n + 1) (fun hn ↦ (ne_of_mem_of_not_mem Set.right_mem_uIcc
          (h.resolve_left (by omega)).2).isUnit) -
          Checked.zpow a (n + 1) (fun hn ↦ (ne_of_mem_of_not_mem Set.left_mem_uIcc
            (h.resolve_left (by omega)).2).isUnit))
        (n + 1 : ℝ) (show (n + 1 : ℝ) ≠ 0 by
          norm_cast
          rcases h with h | h <;> omega).isUnit := by
  have h' : -1 < (n : ℝ) ∨ (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := by
    rcases h with h | h
    · exact .inl (neg_one_lt_zero.trans_le (by exact_mod_cast h))
    · exact .inr ⟨by exact_mod_cast h.1, h.2⟩
  have h₀ (x : [[a, b]]) : n < 0 → IsUnit x.val :=
    fun hn ↦ (ne_of_mem_of_not_mem x.2 (h.resolve_left hn.not_ge).2).isUnit
  have heq : (fun x : [[a, b]] ↦ Checked.zpow x.val n (h₀ x)) =
      (fun x ↦ x.val ^ (n : ℝ)) := funext fun x ↦
        (Real.rpow_intCast x.val n (h := fun hn ↦ (h₀ x hn).ne_zero)).symm
  rw [heq, integral_subtype_eq_integral (fun z : ℝ ↦ z ^ (n : ℝ)), integral_rpow h']
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) := by push_cast; rfl
  have ha (hn : n + 1 < 0) : a ≠ 0 := (h₀ ⟨a, Set.left_mem_uIcc⟩ (by omega)).ne_zero
  have hb (hn : n + 1 < 0) : b ≠ 0 := (h₀ ⟨b, Set.right_mem_uIcc⟩ (by omega)).ne_zero
  simp only [hcast, Real.rpow_intCast a (n + 1) (h := ha), Real.rpow_intCast b (n + 1) (h := hb)]

@[simp]
theorem integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa only [← Nat.cast_succ, Real.rpow_natCast] using
    integral_rpow (r := (n : ℝ)) (a := a) (b := b)
      (.inl (neg_one_lt_zero.trans_le (Nat.cast_nonneg _)))

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_uIoc : ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1) := by
  rcases le_or_gt a b with hab | hab
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab, ← integral_of_le hab]
      _ = ∫ x in 0..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonneg <| ?_) rfl
        rw [uIcc_of_le (sub_nonneg.2 hab)] at hx
        exact hx.1
      _ = |b - a| ^ (n + 1) / (n + 1) := by simp [abs_of_nonneg (sub_nonneg.2 hab)]
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in b..a, |x - a| ^ n := by
        rw [uIoc_of_ge hab.le, ← integral_of_le hab.le]
      _ = ∫ x in b - a..0, (-x) ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonpos <| ?_) rfl
        rw [uIcc_of_le (sub_nonpos.2 hab.le)] at hx
        exact hx.2
      _ = |b - a| ^ (n + 1) / (n + 1) := by
        simp [integral_comp_neg fun x => x ^ n, abs_of_neg (sub_neg.2 hab)]

@[simp]
theorem integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have := @integral_pow a b 1
  norm_num at this
  exact this

theorem integral_one : (∫ _ in a..b, (1 : ℝ)) = b - a := by
  simp only [mul_one, smul_eq_mul, integral_const]

theorem integral_const_on_unit_interval : ∫ _ in a..a + 1, b = b := by simp

@[simp]
theorem integral_inv (h : (0 : ℝ) ∉ [[a, b]]) :
    integralSubtype (fun x : [[a, b]] ↦ Checked.inv x.val (ne_of_mem_of_not_mem x.2 h).isUnit) =
      log (Checked.div b a (ne_of_mem_of_not_mem Set.left_mem_uIcc h).isUnit) := by
  have h' (x : [[a, b]]) : IsUnit x.val := (ne_of_mem_of_not_mem x.2 h).isUnit
  have hd (x : [[a, b]]) :
      HasDerivAt (fun t : [[a, b]] ↦ log t.val) (Checked.inv x.val (h' x)) x Subtype.val := by
    change HasDerivAtFilter _ _ (𝓝 x ×ˢ pure x) (fun t : [[a, b]] ↦ t.val)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, id_eq, Function.comp_def]
      using ((Real.hasDerivAt_log (hx := h' x)).hasFDerivAt.comp_tendsto Subtype.val
        (continuousAt_subtype_val.tendsto.prodMap (tendsto_pure_pure ..))).hasDerivAtFilter
  have hc : Continuous (fun x : [[a, b]] ↦ log x.val) := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (hd x).hasFDerivAt.continuousAt continuousAt_subtype_val
  rw [integral_subtype_uIcc_eq_sub_of_hasDerivAt hc (fun x _ ↦ hd x)
    (integrable_subtype_uIcc (continuous_subtype_val.fun_inv₀ (h0 := h')))]
  exact (log_div (h' ⟨b, right_mem_uIcc⟩).ne_zero (hy := h' ⟨a, left_mem_uIcc⟩)).symm

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) :
    integralSubtype (fun x : [[a, b]] ↦
      Checked.inv x.val (ne_of_mem_of_not_mem x.2 (notMem_uIcc_of_lt ha hb)).isUnit) =
      log (Checked.div b a ha.ne'.isUnit) :=
  integral_inv <| notMem_uIcc_of_lt ha hb

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) :
    integralSubtype (fun x : [[a, b]] ↦
      Checked.inv x.val (ne_of_mem_of_not_mem x.2 (notMem_uIcc_of_gt ha hb)).isUnit) =
      log (Checked.div b a ha.ne.isUnit) :=
  integral_inv <| notMem_uIcc_of_gt ha hb

theorem integral_one_div (h : (0 : ℝ) ∉ [[a, b]]) :
    integralSubtype (fun x : [[a, b]] ↦
      Checked.div 1 x.val (ne_of_mem_of_not_mem x.2 h).isUnit) =
      log (Checked.div b a (ne_of_mem_of_not_mem Set.left_mem_uIcc h).isUnit) := by
  simp only [one_div₀, integral_inv h]

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) :
    integralSubtype (fun x : [[a, b]] ↦
      Checked.div 1 x.val (ne_of_mem_of_not_mem x.2 (notMem_uIcc_of_lt ha hb)).isUnit) =
      log (Checked.div b a ha.ne'.isUnit) := by
  simp only [one_div₀, integral_inv_of_pos ha hb]

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) :
    integralSubtype (fun x : [[a, b]] ↦
      Checked.div 1 x.val (ne_of_mem_of_not_mem x.2 (notMem_uIcc_of_gt ha hb)).isUnit) =
      log (Checked.div b a ha.ne.isUnit) := by
  simp only [one_div₀, integral_inv_of_neg ha hb]

@[simp]
theorem integral_exp : ∫ x in a..b, exp x = exp b - exp a := by
  rw [integral_deriv_eq_sub']
  · simp
  · exact fun _ _ => differentiableAt_exp
  · exact continuousOn_exp

theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) (hb := hc.isUnit)]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  · ring
  · fun_prop

lemma integral_exp_mul_I_eq_sin (r : ℝ) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, Complex.exp (t * Complex.I)
  _ = (Complex.exp (Complex.I * r) - Complex.exp (Complex.I * (-r))) / Complex.I := by
    simp_rw [mul_comm _ Complex.I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      add_sub_add_left_eq_sub, Complex.div_I, Complex.ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp

lemma integral_exp_mul_I_eq_sinc (r : ℝ) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * r * sinc r := by
  rw [integral_exp_mul_I_eq_sin]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field

/-- Helper lemma for `integral_log`: case where `a = 0` and `b` is positive. -/
lemma integral_log_from_zero_of_pos (ht : 0 < b) : ∫ s in 0..b, log s = b * log b - b := by
  -- Compute the integral by giving a primitive and considering it limit as x approaches 0 from the
  -- right. The following lines were suggested by Gareth Ma on Zulip.
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x ↦ x * log x - x)
    (fa := 0) (fb := b * log b - b) (hint := intervalIntegrable_log')]
  · abel
  · exact ht
  · intro s ⟨hs, _ ⟩
    simpa using! (hasDerivAt_mul_log hs.ne.symm).sub (hasDerivAt_id s)
  · simpa [mul_comm] using! ((tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).sub
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id))
  · exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (by fun_prop))

/-- Helper lemma for `integral_log`: case where `a = 0`. -/
lemma integral_log_from_zero {b : ℝ} : ∫ s in 0..b, log s = b * log b - b := by
  rcases lt_trichotomy b 0 with h | h | h
  · -- If t is negative, use that log is an even function to reduce to the positive case.
    conv => arg 1; arg 1; intro t; rw [← log_neg_eq_log]
    rw [intervalIntegral.integral_comp_neg, intervalIntegral.integral_symm, neg_zero,
      integral_log_from_zero_of_pos (Left.neg_pos_iff.mpr h), log_neg_eq_log]
    ring
  · simp [h]
  · exact integral_log_from_zero_of_pos h

@[simp]
theorem integral_log : ∫ s in a..b, log s = b * log b - a * log a - b + a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · rw [intervalIntegral.integral_symm, integral_log_from_zero, integral_log_from_zero]
    ring
  all_goals exact intervalIntegrable_log'

@[simp]
theorem integral_sin : ∫ x in a..b, sin x = cos a - cos b := by
  have h (x : ℝ) : HasDerivAt (-cos) (sin x) x := by
    simpa only [neg_neg] using (hasDerivAt_cos x).neg
  simpa only [Pi.neg_apply, neg_sub_neg] using
    integral_eq_sub_of_hasDerivAt (fun x _ ↦ h x) (continuous_sin.intervalIntegrable _ _)

@[simp]
theorem integral_cos : ∫ x in a..b, cos x = sin b - sin a := by
  exact integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_sin x)
    (continuous_cos.intervalIntegrable _ _)

theorem integral_cos_mul_complex {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) / z - Complex.sin (z * a) / z := by
  have hd (w : ℂ) : HasDerivAt (fun t : ℂ ↦ Checked.div (Complex.sin (z * t)) z hz.isUnit)
      (Complex.cos (z * w)) w := by
    have hzmul : HasDerivAt (fun t : ℂ ↦ z * t) z w := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul z
    have hs := (Complex.hasDerivAt_sin (z * w)).comp
      (h := fun t : ℂ ↦ z * t) (coord' := id) w hzmul
    simpa only [Function.comp_def, mul_div_cancel_right₀] using hs.div_const z (hd := hz.isUnit)
  exact integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ Complex.sin (z * x) / z)
    (fun x _ ↦ (hd x).comp_ofReal) (Continuous.intervalIntegrable (by fun_prop) _ _)

theorem integral_cos_sq_sub_sin_sq :
    ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a := by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable

theorem integral_one_div_one_add_sq :
    (∫ x : ℝ in a..b, 1 / (1 + x ^ 2)) = arctan b - arctan a :=
  integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_arctan x)
    intervalIntegrable_one_div_one_add_sq

@[simp]
theorem integral_inv_one_add_sq : (∫ x : ℝ in a..b, (1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [← one_div₀, integral_one_div_one_add_sq]

@[simp]
theorem integral_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, (c ^ 2 + x ^ 2)⁻¹ = c⁻¹ * (arctan (b / c) - arctan (a / c)) := by
  have hu (x : ℝ) : IsUnit (c ^ 2 + x ^ 2) :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg x)).ne'.isUnit
  rw [mul_sub, ← div_eq_inv_mul₀, ← div_eq_inv_mul₀]
  apply integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ arctan (x / c) / c)
  · intro x _
    have hinner : HasDerivAt (fun t : ℝ ↦ t / c) c⁻¹ x := by
      simpa only [one_div₀, id_eq] using (hasDerivAt_id x).div_const c (hd := hc.isUnit)
    have hd := (hasDerivAt_arctan' (x / c)).comp
      (h := fun t : ℝ ↦ t / c) (coord' := id) x hinner
    convert hd.div_const c (hd := hc.isUnit) using 1
    · rfl
    · field [hc, (hu x).ne_zero]
  · exact ((continuous_const.add (continuous_id.pow 2)).fun_inv₀ (h0 := hu)).intervalIntegrable _ _

theorem integral_div_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, c / (c ^ 2 + x ^ 2) = arctan (b / c) - arctan (a / c) := calc
  _ = ∫ x : ℝ in a..b, c * (c ^ 2 + x ^ 2)⁻¹ := by ring_nf
  _ = _ := by
    rw [integral_const_mul, integral_inv_sq_add_sq hc, ← mul_assoc, mul_inv_cancel₀, one_mul]

theorem integral_id_div_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, x / (c ^ 2 + x ^ 2) = (log (c ^ 2 + b ^ 2) - log (c ^ 2 + a ^ 2)) / 2 := by
  rw [sub_div]
  apply integral_eq_sub_of_hasDerivAt (f := fun x => log (c ^ 2 + x ^ 2) / 2)
  · intro x _
    have h := (((hasDerivAt_pow 2 x).const_add (c ^ 2)).log
      (by dsimp; positivity)).div_const 2
    convert! h using 1
    ring
  · exact (continuous_id.div (by fun_prop) fun x => by positivity).intervalIntegrable _ _

/-- The integrand is chosen to match the conclusion of `Real.deriv_log_log`. -/
@[simp]
theorem integral_inv_div_log (ha : 1 < a) (hb : 1 < b) :
    integralSubtype (fun t : [[a, b]] ↦
      Checked.div
        (Checked.inv t.val (zero_lt_one.trans_le ((lt_min ha hb).le.trans t.2.1)).ne'.isUnit)
        (log t.val) (log_pos ((lt_min ha hb).trans_le t.2.1)).ne'.isUnit) =
      log (log b) - log (log a) := by
  have ht (t : [[a, b]]) : 1 < t.val := (lt_min ha hb).trans_le t.2.1
  have h₀ (t : [[a, b]]) : IsUnit t.val := (zero_lt_one.trans (ht t)).ne'.isUnit
  have hl (t : [[a, b]]) : IsUnit (log t.val) := (log_pos (ht t)).ne'.isUnit
  let j (t : [[a, b]]) : {x : ℝ // IsUnit (log x)} := ⟨t.val, hl t⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk hl
  have hd (t : [[a, b]]) : HasDerivAt (fun x : [[a, b]] ↦ log (log x.val))
      (Checked.div (Checked.inv t.val (h₀ t)) (log t.val) (hl t)) t Subtype.val := by
    change HasDerivAtFilter _ _ (𝓝 t ×ˢ pure t) (fun x : [[a, b]] ↦ x.val)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def] using
      ((Real.hasDerivAt_log_log (j t)).hasFDerivAt.comp_tendsto j
        (hj.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))).hasDerivAtFilter
  have hclog : Continuous (fun x : [[a, b]] ↦ log x.val) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (continuousAt_log (h₀ x).ne_zero).comp continuousAt_subtype_val
  have hc : Continuous (fun x : [[a, b]] ↦ log (log x.val)) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (hd x).hasFDerivAt.continuousAt continuousAt_subtype_val
  exact integral_subtype_uIcc_eq_sub_of_hasDerivAt hc (fun x _ ↦ hd x) <|
    integrable_subtype_uIcc ((continuous_subtype_val.fun_inv₀ (h0 := h₀)).div₀ hclog (h₀ := hl))

/-- The integrand is chosen to match the conclusion of `Real.deriv_inv_log`. -/
@[simp]
theorem integral_inv_div_log_sq (ha : 1 < a) (hb : 1 < b) :
    integralSubtype (fun t : [[a, b]] ↦
      Checked.div
        (Checked.inv t.val (zero_lt_one.trans_le ((lt_min ha hb).le.trans t.2.1)).ne'.isUnit)
        (log t.val ^ 2) ((log_pos ((lt_min ha hb).trans_le t.2.1)).ne'.isUnit.pow 2)) =
      Checked.inv (log a) (log_pos ha).ne'.isUnit -
        Checked.inv (log b) (log_pos hb).ne'.isUnit := by
  have ht (t : [[a, b]]) : 1 < t.val := (lt_min ha hb).trans_le t.2.1
  have h₀ (t : [[a, b]]) : IsUnit t.val := (zero_lt_one.trans (ht t)).ne'.isUnit
  have hl (t : [[a, b]]) : IsUnit (log t.val) := (log_pos (ht t)).ne'.isUnit
  let j (t : [[a, b]]) : {x : ℝ // IsUnit (log x)} := ⟨t.val, hl t⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk hl
  let F (t : [[a, b]]) := -(Checked.inv (log t.val) (hl t))
  let G (t : [[a, b]]) := Checked.div (Checked.inv t.val (h₀ t)) (log t.val ^ 2) ((hl t).pow 2)
  have hd (t : [[a, b]]) : HasDerivAt F (G t) t Subtype.val := by
    let J (x : [[a, b]]) := Checked.inv (log x.val) (hl x)
    have hJ : HasDerivAt J (-G t) t Subtype.val := by
      change HasDerivAtFilter J (-G t) (𝓝 t ×ˢ pure t) (fun x : [[a, b]] ↦ x.val)
      simpa only [J, G, j, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul, neg_div₀] using
        ((Real.hasDerivAt_inv_log (j t)).hasFDerivAt.comp_tendsto j
          (hj.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))).hasDerivAtFilter
    simpa only [F, J, Function.comp_def, neg_mul, one_mul, neg_neg] using
      (hasDerivAt_neg (J t)).comp (h := J) (coord' := id) t hJ continuousAt_subtype_val
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun x ↦
    (hd x).hasFDerivAt.continuousAt continuousAt_subtype_val
  have hclog : Continuous (fun x : [[a, b]] ↦ log x.val) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (continuousAt_log (h₀ x).ne_zero).comp continuousAt_subtype_val
  have hci : Continuous G :=
    (continuous_subtype_val.fun_inv₀ (h0 := h₀)).div₀ (hclog.pow 2)
  simpa only [F, G, neg_sub_neg] using
    integral_subtype_uIcc_eq_sub_of_hasDerivAt hc (fun x _ ↦ hd x) (integrable_subtype_uIcc hci)

section RpowCpow

open Complex

theorem integral_mul_cpow_one_add_sq {t : ℂ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, (x : ℂ) * ((1 : ℂ) + ↑x ^ 2) ^ t) =
      let hu := (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (mt add_eq_zero_iff_eq_neg.mp ht)).isUnit
      Checked.div (((1 : ℂ) + (b : ℂ) ^ 2) ^ (t + 1)) (2 * (t + 1)) hu -
        Checked.div (((1 : ℂ) + (a : ℂ) ^ 2) ^ (t + 1)) (2 * (t + 1)) hu := by
  have ht₁ : t + 1 ≠ 0 := mt add_eq_zero_iff_eq_neg.mp ht
  have hu : IsUnit (2 * (t + 1)) := (mul_ne_zero (by norm_num) ht₁).isUnit
  have hslit (x : ℝ) : (1 + (x : ℂ) ^ 2) ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_mem_slitPlane.2 (add_pos_of_pos_of_nonneg one_pos (sq_nonneg x))
  apply integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦
    Checked.div (((1 : ℂ) + (x : ℂ) ^ 2) ^ (t + 1)) (2 * (t + 1)) hu)
  · intro x _
    have hinner : HasDerivAt (fun y : ℂ => 1 + y ^ 2) (2 * x : ℂ) x := by
      convert! (hasDerivAt_pow 2 (x : ℂ)).const_add 1
      simp
    have h := (hinner.cpow_const (c := t + 1) (hslit x)).div_const (2 * (t + 1)) (hd := hu)
    convert h.comp_ofReal using 1
    rw [add_sub_cancel_right]
    field [ht₁]
  · apply Continuous.intervalIntegrable
    refine continuous_ofReal.mul ?_
    apply Continuous.cpow (by fun_prop) continuous_const
    exact hslit

theorem integral_mul_rpow_one_add_sq {t : ℝ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, x * (↑1 + x ^ 2) ^ t) =
      let hu := (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (mt add_eq_zero_iff_eq_neg.mp ht)).isUnit
      Checked.div ((1 + b ^ 2) ^ (t + 1)) (2 * (t + 1)) hu -
        Checked.div ((1 + a ^ 2) ^ (t + 1)) (2 * (t + 1)) hu := by
  have : ∀ x s : ℝ, (((↑1 + x ^ 2) ^ s : ℝ) : ℂ) = (1 + (x : ℂ) ^ 2) ^ (s : ℂ) := by
    intro x s
    norm_cast
    rw [ofReal_cpow, ofReal_add, ofReal_pow, ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  apply ofReal_injective
  convert! integral_mul_cpow_one_add_sq (_ : (t : ℂ) ≠ -1)
  · rw [← intervalIntegral.integral_ofReal]
    congr with x : 1
    rw [ofReal_mul, this x t]
  · simp_rw [ofReal_sub, ofReal_div, this a (t + 1), this b (t + 1)]
    push_cast; rfl
  · rw [← ofReal_one, ← ofReal_neg, Ne, ofReal_inj]
    exact ht

end RpowCpow

open Nat

/-! ### Integral of `sin x ^ n` -/

theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using! (hasDerivAt_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using! (hasDerivAt_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
        simp only [_root_.pow_succ]
      _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
      _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
        simp [cos_sq', sub_mul, ← pow_add, add_comm]
      _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
        rw [integral_sub, mul_sub, add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n := by
  rw [div_mul_eq_mul_div₀, ← _root_.add_div]
  apply (eq_div_iff (hb := (show 0 < (n : ℝ) + 2 by positivity).ne'.isUnit)).mpr
  linear_combination integral_sin_pow_aux (a := a) (b := b) n

@[simp]
theorem integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 := by
  simp [field, integral_sin_pow, add_sub_assoc]

theorem integral_sin_pow_odd :
    (∫ x in 0..π, sin x ^ (2 * n + 1)) = 2 * ∏ i ∈ range n, (2 * (i : ℝ) + 2) / (2 * i + 3) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
    norm_cast
    field_simp
    simp

theorem integral_sin_pow_even :
    (∫ x in 0..π, sin x ^ (2 * n)) = π * ∏ i ∈ range n, (2 * (i : ℝ) + 1) / (2 * i + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
    norm_cast
    field_simp
    simp

theorem integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  refine mul_pos (by simp [pi_pos]) (prod_pos fun n _ => div_pos ?_ ?_) <;>
  norm_cast <;>
  lia

theorem integral_sin_pow_succ_le : (∫ x in 0..π, sin x ^ (n + 1)) ≤ ∫ x in 0..π, sin x ^ n := by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine integral_mono_on pi_pos.le ?_ ?_ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫ x in 0..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le

/-! ### Integral of `cos x ^ n` -/


theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x :=
    fun x _ => by
      simpa only [mul_right_comm, neg_mul, mul_neg] using! (hasDerivAt_cos x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt sin (cos x) x := fun x _ => hasDerivAt_sin x
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
        simp only [_root_.pow_succ]
      _ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by simp [C, H, h, sq, -neg_add_rev]
      _ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
        simp [sin_sq, sub_mul, ← pow_add, add_comm]
      _ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
        rw [integral_sub, mul_sub, add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n := by
  rw [div_mul_eq_mul_div₀, ← _root_.add_div]
  apply (eq_div_iff (hb := (show 0 < (n : ℝ) + 2 by positivity).ne'.isUnit)).mpr
  linear_combination integral_cos_pow_aux (a := a) (b := b) n

@[simp]
theorem integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 := by
  simp [field, integral_cos_pow, add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : ℝ => u ^ m * (↑1 - u ^ 2) ^ n := by fun_prop
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ, mul_assoc, pow_mul, one_mul]
      congr! 5
      rw [← sq, ← sq, cos_sq']
    _ = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos hc

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
theorem integral_sin_sq_mul_cos :
    ∫ x in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  norm_num at this; exact this

@[simp]
theorem integral_cos_pow_three :
    ∫ x in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  norm_num at this; exact this

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : ℝ => u ^ n * (↑1 - u ^ 2) ^ m := by fun_prop
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by rw [integral_symm]
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only [_root_.pow_succ, pow_mul, _root_.pow_zero, one_mul, mul_neg, neg_mul,
        integral_neg, neg_inj]
      congr! 5
      rw [← sq, ← sq, sin_sq]
    _ = ∫ x in b..a, cos x ^ n * (↑1 - cos x ^ 2) ^ m * -sin x := by congr; ext; ring
    _ = ∫ u in cos b..cos a, u ^ n * (↑1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_cos x) continuousOn_sin.neg hc

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
theorem integral_sin_mul_cos_sq :
    ∫ x in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  norm_num at this; exact this

@[simp]
theorem integral_sin_pow_three :
    ∫ x in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  norm_num at this; exact this

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n := by
  apply integral_congr
  intro x _
  have hs : sin x ^ 2 = (1 - cos (2 * x)) / 2 := by rw [cos_two_mul_eq_one_sub]; ring
  have hc : cos x ^ 2 = (1 + cos (2 * x)) / 2 := by rw [cos_two_mul]; ring
  simp only [pow_mul, hs, hc]

@[simp]
theorem integral_sin_sq_mul_cos_sq :
    ∫ x in a..b, sin x ^ 2 * cos x ^ 2 = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert! integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : ∀ c : ℝ, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by fun_prop
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [sin_two_mul]; ring
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := fun d => by ring
  simp [h1, h2.intervalIntegrable, integral_comp_mul_left fun x => cos x ^ 2, h3, h4]
  ring

/-! ### Integral of miscellaneous functions -/

theorem integral_sqrt_one_sub_sq : ∫ x in (-1 : ℝ)..1, √(1 - x ^ 2 : ℝ) = π / 2 :=
  calc
    _ = ∫ x in sin (-(π / 2))..sin (π / 2), √(1 - x ^ 2 : ℝ) := by rw [sin_neg, sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), √(1 - sin x ^ 2 : ℝ) * cos x :=
          (integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos
            (by fun_prop)).symm
    _ = ∫ x in (-(π / 2))..(π / 2), cos x ^ 2 := by
          refine integral_congr_ae (MeasureTheory.ae_of_all _ fun _ h => ?_)
          rw [uIoc_of_le (neg_le_self (le_of_lt (half_pos Real.pi_pos))), Set.mem_Ioc] at h
          rw [← Real.cos_eq_sqrt_one_sub_sin_sq (le_of_lt h.1) h.2, pow_two]
    _ = π / 2 := by simp

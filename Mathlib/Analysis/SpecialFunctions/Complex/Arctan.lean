/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Complex arctangent

This file defines the complex arctangent `Complex.arctan` as
$$\arctan z = -\frac i2 \log \frac{1 + zi}{1 - zi}$$
and shows that it extends `Real.arctan` to the complex plane away from `I` and `-I`.
Its Taylor series expansion
$$\arctan z = \frac{(-1)^n}{2n + 1} z^{2n + 1},\ |z|<1$$
is proved in `Complex.hasSum_arctan`.
-/

@[expose] public section


namespace Complex

open scoped Real

theorem one_sub_mul_I_ne_zero {z : ℂ} (hz : z ≠ -I) : 1 - z * I ≠ 0 := by
  intro h
  apply hz
  have : z * I * -I = 1 * -I := by rw [sub_eq_zero.1 h]
  rwa [mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one, one_mul] at this

theorem one_add_mul_I_ne_zero {z : ℂ} (hz : z ≠ I) : 1 + z * I ≠ 0 := by
  intro h
  apply hz
  have : z * I * -I = -1 * -I := by rw [eq_neg_of_add_eq_zero_right h]
  rwa [mul_assoc, mul_neg, I_mul_I, neg_neg, mul_one, neg_one_mul, neg_neg] at this

/-! The rule below lets `checked_nonzero` infer that `1 - z * I` is nonzero when `z ≠ -I`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply Complex.one_sub_mul_I_ne_zero; assumption))

/-- The complex arctangent, defined via the complex logarithm away from `I` and `-I`. -/
noncomputable def arctan (z : ℂ) (_h₁ : z ≠ I := by checked_nonzero)
    (h₂ : z ≠ -I := by checked_nonzero) : ℂ :=
  -I / 2 * log ((1 + z * I) / (1 - z * I))

theorem exp_two_mul_arctan_mul_I {z : ℂ} (h₁ : z ≠ I) (h₂ : z ≠ -I) :
    exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
  have hq : (1 + z * I) / (1 - z * I) ≠ 0 := div_ne_zero (one_add_mul_I_ne_zero h₁)
  have h2 (w : ℂ) : 2 * (-I / 2 * w * I) = w := by
    rw [show 2 * (-I / 2 * w * I) = -(I * I) * w by ring, I_mul_I, neg_neg, one_mul]
  rw [arctan, h2, exp_log hq]

theorem tan_arctan {z : ℂ} (h₁ : z ≠ I) (h₂ : z ≠ -I) {hc : cos (arctan z) ≠ 0} :
    tan (arctan z) = z := by
  have z₂ := one_sub_mul_I_ne_zero h₂
  have key := exp_two_mul_arctan_mul_I h₁ h₂
  set w := arctan z
  have he : exp (w * I) * exp (-w * I) = 1 := by rw [← exp_add, neg_mul, add_neg_cancel, exp_zero]
  have hq : exp (w * I) ^ 2 = (1 + z * I) / (1 - z * I) := by
    rw [sq, ← exp_add, ← two_mul, key]
  rw [tan_eq_sin_div_cos, div_eq_iff]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero (exp_ne_zero (w * I))) z₂)
  calc 2 * exp (w * I) * (1 - z * I) * sin w
      = (1 - z * I) * (exp (w * I) * exp (-w * I) - exp (w * I) ^ 2) * I := by
        simp only [sin]
        ring
    _ = (1 - z * I) * (exp (w * I) ^ 2 + exp (w * I) * exp (-w * I)) * z := by
        rw [he, hq, mul_sub, mul_add, mul_div_cancel₀, mul_one,
          show (1 - z * I - (1 + z * I)) * I = -2 * z * (I * I) by ring, I_mul_I]
        ring
    _ = 2 * exp (w * I) * (1 - z * I) * (z * cos w) := by
        simp only [cos]
        ring

/-- `cos z` is nonzero when the bounds in `arctan_tan` are met (`z` lies in the vertical strip
`-π / 2 < z.re < π / 2` and `z ≠ π / 2`). -/
lemma cos_ne_zero_of_arctan_bounds {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re)
    (h₂ : z.re ≤ π / 2) : cos z ≠ 0 := by
  refine cos_ne_zero_iff.mpr fun k hk ↦ ?_
  have hz : z = (((2 * (k : ℝ) + 1) * π / 2 : ℝ) : ℂ) := by
    simpa only [ofReal_div, ofReal_mul, ofReal_add, ofReal_ofNat, ofReal_one, ofReal_intCast]
      using hk
  have hre : z.re = (2 * (k : ℝ) + 1) * (π / 2) := by
    rw [hz, ofReal_re, mul_div_assoc₀]
  have hp : 0 < (π / 2 : ℝ) := div_pos Real.pi_pos zero_lt_two
  have ha : (-1 : ℤ) < 2 * k + 1 := by
    exact_mod_cast (mul_lt_mul_iff_of_pos_right hp).1
      (show (-1 : ℝ) * (π / 2) < (2 * (k : ℝ) + 1) * (π / 2) by
        simpa only [neg_one_mul, ← hre] using h₁)
  have hb : 2 * k + 1 ≤ 1 := by
    exact_mod_cast (mul_le_mul_iff_of_pos_right hp).1
      (show (2 * (k : ℝ) + 1) * (π / 2) ≤ 1 * (π / 2) by
        simpa only [one_mul, ← hre] using h₂)
  apply h₀
  rw [hz, show k = 0 by omega]
  simp only [Int.cast_zero, mul_zero, zero_add, one_mul, ofReal_div, ofReal_ofNat]

/-- The tangent never takes the value `-I`. -/
theorem tan_ne_neg_I {z : ℂ} (hz : cos z ≠ 0) : tan z ≠ -I := by
  intro h
  have hs : sin z = -I * cos z := by rw [← h, tan_mul_cos hz]
  have : cos z - sin z * I = 0 := by
    rw [hs, show cos z - -I * cos z * I = cos z * (1 + I * I) by ring, I_mul_I, add_neg_cancel,
      mul_zero]
  exact exp_ne_zero _ (cos_sub_sin_I z ▸ this)

/-- The tangent never takes the value `I`. -/
theorem tan_ne_I {z : ℂ} (hz : cos z ≠ 0) : tan z ≠ I := by
  intro h
  have hs : sin z = I * cos z := by rw [← h, tan_mul_cos hz]
  have hz' : cos z + sin z * I = 0 := by
    rw [hs, show cos z + I * cos z * I = cos z * (1 + I * I) by ring, I_mul_I, add_neg_cancel,
      mul_zero]
  exact exp_ne_zero _ (cos_add_sin_I z ▸ hz')

theorem arctan_tan {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re ≤ π / 2) :
    arctan (tan z (cos_ne_zero_of_arctan_bounds h₀ h₁ h₂))
      (tan_ne_I (cos_ne_zero_of_arctan_bounds h₀ h₁ h₂))
      (tan_ne_neg_I (cos_ne_zero_of_arctan_bounds h₀ h₁ h₂)) = z := by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  have hne := one_sub_mul_I_ne_zero (tan_ne_neg_I h)
  have hq : (1 + tan z h * I) / (1 - tan z h * I) = exp (2 * (I * z)) := by
    rw [div_eq_iff]
    apply mul_left_cancel₀ h
    calc cos z * (1 + tan z h * I) = cos z + sin z * I := by
          rw [← tan_mul_cos h]
          ring
      _ = exp (z * I) := cos_add_sin_I z
      _ = exp (2 * (I * z)) * exp (-z * I) := by
          rw [← exp_add]
          ring_nf
      _ = exp (2 * (I * z)) * (cos z - sin z * I) := by rw [cos_sub_sin_I]
      _ = cos z * (exp (2 * (I * z)) * (1 - tan z h * I)) := by
          rw [← tan_mul_cos h]
          ring
  unfold arctan
  simp only [hq]
  rw [log_exp, show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]
  all_goals rw [mul_left_comm, I_mul_im, show (2 : ℂ) = (2 : ℝ) by rfl, re_ofReal_mul]
  · rwa [← div_lt_iff₀' two_pos, neg_div₀]
  · rwa [← le_div_iff₀' two_pos]

theorem ofReal_ne_neg_I (x : ℝ) : (x : ℂ) ≠ -I := fun h ↦ by
  simpa using congrArg im h

theorem ofReal_ne_I (x : ℝ) : (x : ℂ) ≠ I := fun h ↦ by
  simpa using congrArg im h

@[simp, norm_cast]
theorem ofReal_arctan (x : ℝ) :
    (Real.arctan x : ℂ) = arctan x (ofReal_ne_I x) (ofReal_ne_neg_I x) := by
  have hc : Real.cos (Real.arctan x) ≠ 0 := (Real.cos_arctan_pos x).ne'
  conv_rhs => rw [← Real.tan_arctan x (h := hc)]
  simp only [ofReal_tan]
  rw [arctan_tan]
  all_goals norm_cast
  · intro h
    have he : (↑(π / (2 : ℝ)) : ℂ) = (↑π : ℂ) / 2 := by
      simpa only [ofReal_ofNat] using ofReal_div π 2
    exact (Real.arctan_lt_pi_div_two x).ne (ofReal_injective (h.trans he.symm))
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

/-- The argument of `1 + z` for `z` in the open unit disc is always in `(-π / 2, π / 2)`. -/
lemma arg_one_add_mem_Ioo {z : ℂ} (hz : ‖z‖ < 1) : (1 + z).arg ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.mem_Ioo, ← abs_lt, abs_arg_lt_pi_div_two_iff, add_re, one_re, ← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

/-- We can combine the logs in `log (1 + z * I) + -log (1 - z * I)` into one.
This is only used in `hasSum_arctan`. -/
theorem ne_neg_I_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ≠ -I := by
  rintro rfl
  simp at hz

theorem ne_I_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ≠ I := by
  rintro rfl
  simp at hz

lemma hasSum_arctan_aux {z : ℂ} (hz : ‖z‖ < 1) :
    log (1 + z * I) + -log (1 - z * I) =
      log (Checked.div (1 + z * I) (1 - z * I)
        (one_sub_mul_I_ne_zero (ne_neg_I_of_norm_lt_one hz)).isUnit) := by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ (hx₀ := z₂.2.isUnit) z₂.1,
    ← (log_mul_eq_add_log_iff z₁.2 (inv_ne_zero (ha := z₂.2.isUnit))).mpr,
    div_eq_mul_inv₀]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv _ (hx := z₂.2.isUnit), z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg,
      sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

set_option backward.defeqAttrib.useBackward true in
/-- The power series expansion of `Complex.arctan`, valid on the open unit disc. -/
theorem hasSum_arctan {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1))
      (arctan z (ne_I_of_norm_lt_one hz) (ne_neg_I_of_norm_lt_one hz)) := by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hodd : Odd (2 * k + 1 + 2) := ⟨k + 1, by omega⟩
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, heven.neg_one_pow, hodd.neg_one_pow,
    neg_add_cancel, zero_mul, zero_div, mul_zero, add_zero]
  simp only [Nat.cast_add, Nat.cast_one]
  let d : ℂ := ((2 * k : ℕ) : ℂ) + 1
  have hd : IsUnit d := (Nat.cast_add_one_ne_zero (2 * k)).isUnit
  change (-1 : ℂ) ^ k * z ^ (2 * k + 1) / d = -I / 2 * ((1 + 1) * (z * I) ^ (2 * k + 1) / d)
  calc
    _ = (-I / 2 * ((1 + 1) * (z * I) ^ (2 * k + 1))) / d := by
      congr 1
      rw [← mul_assoc, show -I / 2 * (1 + 1) = -I by ring]
      rw [mul_pow, pow_succ' I, pow_mul, I_sq,
        show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring, I_mul_I, neg_neg, one_mul]
    _ = _ := mul_div_assoc₀ _ _ _

end Complex

/-- The power series expansion of `Real.arctan`, valid on `-1 < x < 1`. -/
theorem Real.hasSum_arctan {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan x) := by
  have h := Complex.hasSum_arctan (z := x) (by simpa)
  rw [← Complex.ofReal_arctan] at h
  apply Complex.hasSum_ofReal.mp
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_natCast] using h

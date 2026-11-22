/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Convex.Deriv

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Collection of convex functions

In this file we prove that certain specific functions are strictly convex, including the following:

* `Even.strictConvexOn_pow` : For an even `n : ℕ` with `2 ≤ n`, `fun x => x ^ n` is strictly convex.
* `strictConvexOn_pow` : For `n : ℕ`, with `2 ≤ n`, `fun x => x ^ n` is strictly convex on $[0,+∞)$.
* `strictConvexOn_zpow` : For `m : ℤ` with `m ≠ 0, 1`, `fun x => x ^ m` is strictly convex on
  $(0, +∞)$, as a function on the positive elements.
* `strictConcaveOn_sin_Icc` : `sin` is strictly concave on $[0, π]$
* `strictConcaveOn_cos_Icc` : `cos` is strictly concave on $[-π/2, π/2]$

## TODO

These convexity lemmas are proved by checking the sign of the second derivative. If desired, most
of these could also be switched to elementary proofs, like in
`Analysis.Convex.SpecificFunctions.Basic`.

-/

public section


open Real Set

open scoped NNReal Topology

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
theorem strictConvexOn_pow {n : ℕ} (hn : 2 ≤ n) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  eta_expand
  simp_rw [deriv_pow_field, interior_Ici]
  exact fun x (hx : 0 < x) y _ hxy => mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ hxy hx.le <| Nat.sub_ne_zero_of_lt hn) (by positivity)

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
theorem Even.strictConvexOn_pow {n : ℕ} (hn : Even n) (h : n ≠ 0) :
    StrictConvexOn ℝ Set.univ fun x : ℝ => x ^ n := by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  eta_expand
  simp_rw [deriv_pow_field]
  replace h := Nat.pos_of_ne_zero h
  exact StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
    (Nat.cast_pos.2 h)

theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type*}
    [CommRing β] [LinearOrder β] [IsStrictOrderedRing β] {f : α → β}
    [DecidablePred fun x => f x ≤ 0] {s : Finset α} (h0 : Even (s.filter fun x => f x ≤ 0).card) :
    0 ≤ ∏ x ∈ s, f x :=
  calc
    0 ≤ ∏ x ∈ s, (if f x ≤ 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx
        · simp [hx]
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, neg_one_pow_eq_pow_mod_two, Nat.even_iff.1 h0, pow_zero, one_mul]

theorem int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : Even n) :
    0 ≤ ∏ k ∈ Finset.range n, (m - k) := by
  rcases hn with ⟨n, rfl⟩
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [← two_mul] at ihn
    rw [← two_mul, mul_add, mul_one, ← one_add_one_eq_two, ← add_assoc,
      Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]
    refine mul_nonneg ihn ?_; generalize (1 + 1) * n = k
    rcases le_or_gt m k with hmk | hmk
    · have : m ≤ k + 1 := hmk.trans (lt_add_one (k : ℤ)).le
      convert! mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
      convert! sub_nonpos_of_le this
    · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)

theorem int_prod_range_pos {m : ℤ} {n : ℕ} (hn : Even n) (hm : m ∉ Ico (0 : ℤ) n) :
    0 < ∏ k ∈ Finset.range n, (m - k) := by
  refine (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm ?_
  rw [eq_comm, Finset.prod_eq_zero_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 <| Finset.mem_range.1 ha⟩

/-- `x^m`, `m : ℤ` is strictly convex on `(0, +∞)` for all `m` except `0` and `1`. A negative power
exists only at invertible elements, so the function is defined on the positive elements `Ioi 0`
and is strictly convex in the coordinate `Subtype.val`. -/
theorem strictConvexOn_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
    StrictConvexOn ℝ univ (fun x : Ioi (0 : ℝ) ↦ Checked.zpow (x : ℝ) m fun _ ↦ x.2.ne'.isUnit)
      Subtype.val := by
  have himage : Convex ℝ ((Subtype.val : Ioi (0 : ℝ) → ℝ) '' univ) := by
    rw [image_univ, Subtype.range_coe]
    exact convex_Ioi 0
  refine ⟨himage, fun x _ y _ hxy a b ha hb hab z _ hz ↦ ?_⟩
  have hx : (0 : ℝ) < x := x.2
  have hy : (0 : ℝ) < y := y.2
  have hz₀ : (0 : ℝ) < z := z.2
  have hz' : (z : ℝ) = a * x + b * y := hz
  simp only [smul_eq_mul]
  rcases m with n | n
  · -- `x ^ n` with a natural `n ≥ 2` is strictly convex on `[0, +∞)`.
    have hn : 2 ≤ n := by rw [Int.ofNat_eq_natCast] at hm₀ hm₁; omega
    simp only [Int.ofNat_eq_natCast, zpow_natCast₀, hz']
    exact (strictConvexOn_pow hn).map_combo_lt hx.le hy.le hxy ha hb hab
  -- `x ^ -[n+1] = x⁻¹ ^ (n + 1)`: the inverse is strictly convex on `(0, +∞)`, and
  -- `t ↦ t ^ (n + 1)` is convex and strictly increasing on `[0, +∞)`.
  have hinv : (z : ℝ)⁻¹ < a * (x : ℝ)⁻¹ + b * (y : ℝ)⁻¹ := by
    obtain rfl : b = 1 - a := eq_sub_of_add_eq' hab
    have key : a * (x : ℝ)⁻¹ + (1 - a) * (y : ℝ)⁻¹ - (z : ℝ)⁻¹ =
        a * (1 - a) * ((x : ℝ) - y) ^ 2 / ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
      field_simp
      rw [hz']
      ring
    have hsq : 0 < ((x : ℝ) - y) ^ 2 := sq_pos_iff.2 (sub_ne_zero.2 hxy)
    have : 0 < a * (1 - a) * ((x : ℝ) - y) ^ 2 / ((x : ℝ) * (y : ℝ) * (z : ℝ)) :=
      div_pos (mul_pos (mul_pos ha hb) hsq) (by positivity)
    linarith
  have e : ∀ w : Ioi (0 : ℝ), Checked.zpow (w : ℝ) (Int.negSucc n) (fun _ ↦ w.2.ne'.isUnit) =
      Checked.inv (w : ℝ) w.2.ne'.isUnit ^ (n + 1) := fun w ↦ by
    rw [zpow_negSucc₀, inv_pow₀]
  have hp : (1 : ℝ) ≤ (↑(n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hconv : ConvexOn ℝ (Ici 0) (fun w : ℝ ↦ w ^ (n + 1)) := by
    simpa only [Real.rpow_natCast] using convexOn_rpow hp
  simp only [e]
  calc Checked.inv (z : ℝ) z.2.ne'.isUnit ^ (n + 1)
      < (a * (x : ℝ)⁻¹ + b * (y : ℝ)⁻¹) ^ (n + 1) := by gcongr
    _ ≤ a * (x : ℝ)⁻¹ ^ (n + 1) + b * (y : ℝ)⁻¹ ^ (n + 1) :=
      hconv.map_combo_le (inv_pos_of_pos hx).le (inv_pos_of_pos hy).le ha.le
        hb.le hab

section SqrtMulLog

theorem hasDerivAt_sqrt_mul_log {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => √x * log x) ((2 + log x) / (2 * √x)) x := by
  have hs : √x * √x = x := mul_self_sqrt hx.le
  have hxU := hx.ne'.isUnit
  have hden := isUnit_two_mul_sqrt hx
  have hsqrt : HasDerivAt (√·) (1 / (2 * √x)) x := by
    simpa only [dite_eq_left hx] using hasDerivAt_sqrt hx.ne'
  have hfrac : √x / x = 2 / (2 * √x) := by
    apply div_eq_div_iff.mpr
    linear_combination 2 * hs
  apply (hsqrt.mul (hasDerivAt_log (hx := hxU))).congr_deriv
  rw [one_div_mul_eq_div₀, ← div_eq_mul_inv₀, hfrac, ← add_div, add_comm]

theorem deriv_sqrt_mul_log {x : ℝ} (hx : 0 < x) :
    deriv (fun x => √x * log x) x = (2 + log x) / (2 * √x) :=
  (hasDerivAt_sqrt_mul_log hx).deriv

theorem deriv2_sqrt_mul_log {x : ℝ} (hx : 0 < x) :
    deriv^[2] (fun x => √x * log x) x = -log x / (4 * √x ^ 3) := by
  -- On `(0, +∞)`, the derivative `(2 + log y) / (2 * √y)` equals
  -- `(2 + log y) * exp (-(log y / 2)) / 2`, an expression defined on the whole line.
  have hexp : ∀ {y : ℝ}, 0 < y → exp (log y / 2) = √y := fun {y} hy ↦ by
    rw [← sqrt_sq (exp_pos _).le, ← exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀, exp_log hy]
  have hE : ∀ {y : ℝ}, 0 < y → exp (-(log y / 2)) * √y = 1 := fun {y} hy ↦ by
    rw [← hexp hy, ← exp_add, neg_add_cancel, exp_zero]
  have hderiv : deriv (fun y => √y * log y) =ᶠ[𝓝 x]
      fun y => (2 + log y) * exp (-(log y / 2)) / 2 := by
    filter_upwards [Ioi_mem_nhds hx] with y (hy : 0 < y)
    rw [deriv_sqrt_mul_log hy, div_eq_iff]
    linear_combination (-(2 + log y)) * hE hy
  have hlog := hasDerivAt_log (hx := hx.ne'.isUnit)
  have htwo := (two_ne_zero : (2 : ℝ) ≠ 0).isUnit
  have hg := ((hlog.const_add 2).mul (hlog.div_const 2 (hd := htwo)).neg.exp).div_const 2
    (hd := htwo)
  have hg' : HasDerivAt (fun y : ℝ ↦ (2 + log y) * exp (-(log y / 2)) / 2) _ x := hg
  simp only [Nat.iterate]
  rw [hderiv.deriv_eq, hg'.deriv]
  have hs : √x ^ 2 = x := sq_sqrt hx.le
  have hs₀ : 0 < √x := sqrt_pos.2 hx
  field_simp
  linear_combination (-4 * log x * √x ^ 2) * hE hx + (-4 * log x) * hs

theorem strictConcaveOn_sqrt_mul_log_Ioi :
    StrictConcaveOn ℝ (Set.Ioi 1) fun x => √x * log x := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => ?_
  · exact continuous_sqrt.continuousOn.mul
      (continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log (zero_lt_one.trans hx)]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))

end SqrtMulLog

open scoped Real

theorem strictConcaveOn_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  rw [interior_Icc] at hx
  change deriv (fun y ↦ deriv sin y) x < 0
  have hsin : (fun y ↦ deriv sin y _root_.id) = cos := Real.deriv_sin
  rw [hsin, Real.deriv_cos]
  exact neg_lt_zero.mpr (sin_pos_of_mem_Ioo hx)

theorem strictConcaveOn_cos_Icc : StrictConcaveOn ℝ (Icc (-(π / 2)) (π / 2)) cos := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  change deriv (fun y ↦ deriv cos y) x < 0
  have hcos : (fun y ↦ deriv cos y _root_.id) = fun y ↦ -sin y := Real.deriv_cos'
  rw [hcos]
  have h : deriv (fun y ↦ -sin y) x = -cos x := (hasDerivAt_sin x).fun_neg.deriv
  rw [h]
  exact neg_lt_zero.mpr (cos_pos_of_mem_Ioo hx)

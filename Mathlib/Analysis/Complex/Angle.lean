/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angle between complex numbers

This file relates the Euclidean geometric notion of angle between complex numbers to the argument of
their quotient.

It also shows that the arc and chord distances between two unit complex numbers are equivalent up to
a factor of `π / 2`.

## TODO

Prove the corresponding results for oriented angles.

## Tags

arc-length, arc-distance
-/

public section

open InnerProductGeometry Set
open scoped Real

namespace Complex
variable {a x y : ℂ}

/-- The angle between two non-zero complex numbers is the absolute value of the argument of their
quotient. -/
lemma angle_eq_abs_arg (hx : x ≠ 0) (hy : y ≠ 0) : angle x y = |(x / y).arg| := by
  let q : ℂ := x / y
  have hqy : q * y = x := div_mul_cancel₀ x
  have hq : q ≠ 0 := div_ne_zero hx
  have hd : ‖x‖ * ‖y‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)
  have hnorm : ‖x‖ = ‖q‖ * ‖y‖ := by rw [← norm_mul, hqy]
  have hinner : inner ℝ x y = q.re * ‖y‖ ^ 2 := by
    rw [← hqy, Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  change angle x y = |q.arg|
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs, Complex.cos_arg hq]
  apply mul_right_cancel₀ hd
  rw [div_mul_cancel₀, hinner]
  have hqr : (q.re / ‖q‖) * ‖q‖ = q.re := div_mul_cancel₀ _
  calc
    _ = ((q.re / ‖q‖) * ‖q‖) * ‖y‖ ^ 2 := by rw [hqr]
    _ = _ := by rw [hnorm]; ring

lemma angle_one_right (hx : x ≠ 0) : angle x 1 = |x.arg| := by
  simpa only [div_one₀] using angle_eq_abs_arg hx (one_ne_zero : (1 : ℂ) ≠ 0)

lemma angle_one_left (hy : y ≠ 0) : angle 1 y = |y.arg| :=
  (angle_comm 1 y).trans (angle_one_right hy)

@[simp] lemma angle_mul_left (ha : a ≠ 0) (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    angle (a * x) (a * y) = angle x y := by
  rw [angle_eq_abs_arg (mul_ne_zero ha hx) (mul_ne_zero ha hy), angle_eq_abs_arg hx hy,
    mul_div_mul_left]

@[simp] lemma angle_mul_right (ha : a ≠ 0) (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    angle (x * a) (y * a) = angle x y := by
  simpa only [mul_comm a x, mul_comm a y] using angle_mul_left ha x y hx hy

lemma angle_div_left_eq_angle_mul_right (a x y : ℂ) {ha : IsUnit a} (hx : x ≠ 0) (hy : y ≠ 0) :
    angle (x / a) y (hx := div_ne_zero hx) (hy := hy) = angle x (y * a) := by
  let q : ℂ := x / a
  have hq : q ≠ 0 := div_ne_zero hx
  have hqa : q * a = x := div_mul_cancel₀ x
  have hangle : angle (q * a) (y * a) = angle x (y * a) := by simp only [hqa]
  exact (angle_mul_right ha.ne_zero q y hq hy).symm.trans hangle

lemma angle_div_right_eq_angle_mul_left (a x y : ℂ) {ha : IsUnit a} (hx : x ≠ 0) (hy : y ≠ 0) :
    angle x (y / a) (hx := hx) (hy := div_ne_zero hy) = angle (x * a) y := by
  calc
    _ = angle (y / a) x (hx := div_ne_zero hy) (hy := hx) := angle_comm _ _
    _ = angle y (x * a) := angle_div_left_eq_angle_mul_right a y x hy hx
    _ = _ := angle_comm _ _

lemma angle_exp_exp (x y : ℝ) :
    angle (exp (x * I)) (exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)| := by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]

lemma angle_exp_one (x : ℝ) : angle (exp (x * I)) 1 = |toIocMod Real.two_pi_pos (-π) x| := by
  simpa using angle_exp_exp x 0

/-!
### Arc-length and chord-length are equivalent

This section shows that the arc and chord distances between two unit complex numbers are equivalent
up to a factor of `π / 2`.
-/

/-- Chord-length is a multiple of arc-length up to constants. -/
lemma norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ∈ Icc (2 / π * angle x y) (angle x y) := by
  wlog h : y = 1
  · have hnx : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
    have hny : y ≠ 0 := norm_ne_zero_iff.mp (hy.trans_ne one_ne_zero)
    have hq : ‖x / y‖ = 1 := by simp only [norm_div, hx, hy, div_one₀]
    have hchord : ‖x / y - 1‖ = ‖x - y‖ := by simp only [div_sub_one, norm_div, hy, div_one₀]
    have hangle : angle (x / y) 1 (hx := div_ne_zero hnx) = angle x y := by
      simpa only [one_mul] using angle_div_left_eq_angle_mul_right y x 1 hnx one_ne_zero
    simpa only [hchord, hangle] using (@this (x / y) 1 hq norm_one rfl)
  subst y
  obtain ⟨θ, hθ, rfl⟩ := norm_eq_one_iff'.mp hx
  rw [angle_exp_one, exp_mul_I, add_sub_right_comm, (toIocMod_eq_self _).2]
  · norm_cast
    rw [norm_add_mul_I]
    refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
    · rw [mul_pow, ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - (1 - 2 / π ^ 2 * θ ^ 2)) := by ring
        _ ≤ 2 * (1 - θ.cos) := by
            gcongr; exact Real.cos_le_one_sub_mul_cos_sq <| abs_le.2 <| Ioc_subset_Icc_self hθ
        _ = _ := by linear_combination -θ.cos_sq_add_sin_sq
    · rw [Real.sqrt_le_left (by positivity), ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - θ.cos) := by linear_combination θ.cos_sq_add_sin_sq
        _ ≤ 2 * (1 - (1 - θ ^ 2 / 2)) := by gcongr; exact Real.one_sub_sq_div_two_le_cos
        _ = _ := by ring
  · convert! hθ
    ring

/-- Chord-length is always less than arc-length. -/
lemma norm_sub_le_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ ≤ angle x y :=
  (norm_sub_mem_Icc_angle hx hy).2

/-- Chord-length is always greater than a multiple of arc-length. -/
lemma mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * angle x y ≤ ‖x - y‖ :=
  (norm_sub_mem_Icc_angle hx hy).1

/-- Arc-length is always less than a multiple of chord-length. -/
lemma angle_le_mul_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y ≤ π / 2 * ‖x - y‖ := by
  rw [← div_le_iff₀' (by positivity : 0 < π / 2), div_eq_inv_mul₀, inv_div₀]
  exact mul_angle_le_norm_sub hx hy

end Complex

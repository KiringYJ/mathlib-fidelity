/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`, we have
`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation Notes

The proof applies the Schwarz lemma to the transformed function `w z := f z / (2 * M - f z)`,
which maps the ball `|z| < R` into the unit disk provided that `(f z).re ≤ M` for all `|z| < R`.
After obtaining bounds on `w`, we invert the transformation to recover bounds on `f`.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric

namespace Complex

variable {f : ℂ → ℂ} {M R : ℝ} {z w : ℂ}

section SchwarzTransform

/-- If `w = z / (2M - z)`, then `z = 2M * w / (1 + w)`. This is the inverse of the
Schwarz transform used in the proof of the Borel-Carathéodory theorem. -/
lemma eq_mul_div_one_add_of_eq_div_sub {hd : IsUnit (2 * (M : ℂ) - z)} {hw : IsUnit (1 + w)}
    (h : w = z / (2 * M - z)) : z = 2 * M * w / (1 + w) := by
  apply eq_div_iff.mpr
  linear_combination -(eq_div_iff.mp h)

private lemma isUnit_one_add_of_norm_lt_one (hw : ‖w‖ < 1) : IsUnit (1 + w) := by
  have h : 1 - ‖w‖ ≤ ‖1 + w‖ := by simpa using norm_sub_le_norm_add (1 : ℂ) w
  exact (norm_pos_iff.mp ((sub_pos.mpr hw).trans_le h)).isUnit

/-- Norm inequality for the inverse Schwarz transform: if `‖w‖ < 1`, then
`‖2M * w / (1 + w)‖ ≤ 2M * ‖w‖ / (1 - ‖w‖)`. -/
lemma norm_two_mul_div_one_add_le (hM : 0 < M) (hw : ‖w‖ < 1) :
    ‖Checked.div (2 * ↑M * w) (1 + w) (isUnit_one_add_of_norm_lt_one hw)‖ ≤
      2 * M * ‖w‖ / (1 - ‖w‖) := by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr
  rw [← norm_one (α := ℂ)]; exact norm_sub_le_norm_add 1 w

/-- If `z.re ≤ M`, then `‖z‖ ≤ ‖2M - z‖`. This shows that the Schwarz transform
`z ↦ z / (2M - z)` has numerator smaller than denominator when the real part is bounded by M -/
lemma norm_le_norm_two_mul_sub (_ : 0 < M) (_ : z.re ≤ M) : ‖z‖ ≤ ‖2 * M - z‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re ≤ (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

private lemma isUnit_two_mul_sub (hM : 0 < M) (hz : z.re ≤ M) : IsUnit (2 * (M : ℂ) - z) := by
  apply Ne.isUnit
  intro h
  have he := congrArg re h
  simp at he
  linarith

/-- Application of the Schwarz lemma to the transformed function. If `f` is differentiable on
the ball, maps into `{z | z.re ≤ M}`, and satisfies `f 0 = 0`, then the Schwarz transform
satisfies the bound from the Schwarz lemma. -/
lemma schwarz_applied (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hz : z ∈ ball 0 R) (hf₂ : f 0 = 0) :
    ‖Checked.div (f z) (2 * M - f z) (isUnit_two_mul_sub hM (hf₁ hz))‖ ≤
      Checked.div 1 R (nonempty_ball.mp ⟨z, hz⟩).ne'.isUnit * ‖z‖ := by
  have hR : 0 < R := nonempty_ball.mp ⟨z, hz⟩
  -- Project onto the closed half-plane containing the image of the ball.
  let F (x : ℂ) : ℂ := ⟨min (f x).re M, (f x).im⟩
  have hF (x : ℂ) (hx : x ∈ ball 0 R) : F x = f x := by
    exact Complex.ext (min_eq_left (hf₁ hx)) rfl
  have hden (x : ℂ) : IsUnit (2 * (M : ℂ) - F x) := isUnit_two_mul_sub hM (min_le_right _ _)
  let g (x : ℂ) := Checked.div (F x) (2 * M - F x) (hden x)
  have hg₀ : g 0 = 0 := by simp [g, hF 0 (mem_ball_self hR), hf₂]
  have hdF := hf.congr hF
  have hdg : DifferentiableOn ℂ g (ball 0 R) := by
    intro x hx
    have hd := hdF.differentiableAt (isOpen_ball.mem_nhds hx)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.of_restrict (s := {y | IsUnit (2 * (M : ℂ) - F y)})
      (x := ⟨x, hden x⟩) _ (Filter.Eventually.of_forall hden)
    exact hd.div (hd.const_sub _) (hden x)
  have hm : Set.MapsTo g (ball 0 R) (closedBall (g 0) 1) := by
    intro x hx
    simp only [hg₀, mem_closedBall_zero_iff, g, norm_div]
    exact div_le_one_of_le₀ (norm_le_norm_two_mul_sub hM (min_le_right _ _)) (norm_nonneg _)
  simpa only [hg₀, dist_zero_right, g, hF z hz] using
    dist_le_div_mul_dist_of_mapsTo_ball hdg hm hz

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re ≤ M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory_zero (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) :
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  dsimp only
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  let w := Checked.div (f z) (2 * M - f z) (isUnit_two_mul_sub hM (hf₁ hz))
  have hwR : ‖w‖ ≤ ‖z‖ / R := by
    simpa only [mul_comm (1 / R), mul_one_div₀] using schwarz_applied hM hf hf₁ hz hf₂
  have hz' := (div_lt_one₀ hR).mpr hzR
  have hw := hwR.trans_lt hz'
  have hw₁ := isUnit_one_add_of_norm_lt_one hw
  calc
    ‖f z‖ = ‖2 * M * w / (1 + w)‖ :=
      congrArg norm (eq_mul_div_one_add_of_eq_div_sub (w := w) rfl)
    _ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := norm_two_mul_div_one_add_le hM hw
    _ ≤ 2 * M * (‖z‖ / R) / (1 - ‖z‖ / R) := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re ≤ M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  dsimp only
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hfz : ‖f z - f 0‖ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (f := fun x ↦ f x - f 0) (by positivity) (hf.sub_const _) ?_ hR hz
      (by simp)
    intro x hx
    simp only [Set.mem_ofPred_eq, sub_re]
    calc (f x).re - (f 0).re ≤ M - (f 0).re := by gcongr; exact hf₁ hx
      _ ≤ M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by field_simp; ring

end BorelCaratheodory

end Complex

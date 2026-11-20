/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Sign.Defs

/-!
# Normalized vector

Normalization sends a nonzero vector to the unit vector in its direction.
-/

@[expose] public section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The unit vector in the direction of a nonzero vector. -/
noncomputable def NormedSpace.normalize (x : V)
    (hx : x ≠ 0 := by
      first | checked_nonzero | (intro h; simp_all) | fail "a nonzero vector is required") : V :=
  ‖x‖⁻¹ • x

namespace NormedSpace

@[simp]
theorem norm_smul_normalize (x : V) {hx : x ≠ 0} : ‖x‖ • normalize x = x := by
  simp [normalize, smul_smul]

@[simp]
lemma norm_normalize (x : V) {hx : x ≠ 0} : ‖normalize x‖ = 1 := by
  simp [normalize, norm_smul]

@[simp]
theorem normalize_ne_zero (x : V) {hx : x ≠ 0} : normalize x ≠ 0 := by
  intro h
  have := norm_normalize x (hx := hx)
  simp only [h, norm_zero, zero_ne_one] at this

lemma normalize_eq_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) :
    normalize x (by intro hx; simp [hx] at h) = x := by
  simp [normalize, h]

@[simp]
theorem normalize_normalize (x : V) {hx : x ≠ 0} : normalize (normalize x) = normalize x := by
  exact normalize_eq_self_of_norm_eq_one (norm_normalize x)

@[simp]
theorem normalize_neg (x : V) {hx : x ≠ 0} : normalize (-x) = -normalize x := by
  simp [normalize]

theorem normalize_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) {hx : x ≠ 0} :
    normalize (r • x) = normalize x := by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr]

theorem normalize_smul_of_neg {r : ℝ} (hr : r < 0) (x : V) {hx : x ≠ 0} :
    normalize (r • x) = -normalize x := by
  simpa only [neg_smul, smul_neg, neg_neg, normalize_neg x (hx := hx)] using
    normalize_smul_of_pos (neg_pos.mpr hr) (-x) (hx := neg_ne_zero.mpr hx)

theorem normalize_smul (r : ℝ) (x : V) {hr : r ≠ 0} {hx : x ≠ 0} :
    normalize (r • x) = (SignType.sign r : ℝ) • normalize x := by
  rcases hr.lt_or_gt with h_neg | h_pos
  · rw [normalize_smul_of_neg h_neg x (hx := hx)]
    simp [h_neg]
  · rw [normalize_smul_of_pos h_pos x (hx := hx)]
    simp [h_pos]

end NormedSpace

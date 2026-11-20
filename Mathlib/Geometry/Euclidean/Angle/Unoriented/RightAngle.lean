/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Daniel Liao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Right-angled triangles

This file proves basic geometric results about distances and angles in
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem
* https://en.wikipedia.org/wiki/Geometric_mean_theorem

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V)
    {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, vector angle form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = π / 2) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V)
    {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = π / 2) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h


/-- An orthogonal sum has a nonzero norm if its first summand is nonzero. -/
theorem add_ne_zero_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (hx : x ≠ 0) : x + y ≠ 0 := by
  intro hxy
  have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  rw [hxy, norm_zero, zero_mul] at hnorm
  have hpos := norm_pos_iff.mpr hx
  exact (add_pos_of_pos_of_nonneg (mul_pos hpos hpos) (mul_self_nonneg ‖y‖)).ne' hnorm.symm

section Add

variable {x y : V} (h : ⟪x, y⟫ = 0) {hx : x ≠ 0}

/-- The norm of an orthogonal sum is invertible when its first summand is nonzero. -/
theorem isUnit_norm_add_of_inner_eq_zero
    (h : ⟪x, y⟫ = 0) {hx : x ≠ 0} : IsUnit ‖x + y‖ :=
  (norm_ne_zero_iff.mpr (add_ne_zero_of_inner_eq_zero h hx)).isUnit

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_angle_add_of_inner_eq_zero :
    Real.cos (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) =
      Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_inner_eq_zero h (hx := hx)) := by
  simp only [cos_angle, inner_add_right, h, add_zero, real_inner_self_eq_norm_mul_norm,
    mul_div_mul_left]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem angle_add_eq_arccos_of_inner_eq_zero :
    angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) =
      Real.arccos (Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_inner_eq_zero h (hx := hx))) := by
  rw [← cos_angle_add_of_inner_eq_zero h (hx := hx)]
  have hxy := add_ne_zero_of_inner_eq_zero h hx
  exact (Real.arccos_cos (angle_nonneg x (x + y) (hx := hx) (hy := hxy))
    (angle_le_pi x (x + y) (hx := hx) (hy := hxy))).symm

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_angle_add_of_inner_eq_zero :
    Real.sin (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) =
      Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_inner_eq_zero h (hx := hx)) := by
  rw [sin_angle_add (hx := hx) (hy := add_ne_zero_of_inner_eq_zero h hx), h, mul_zero, sub_zero,
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm]
  have hnorm : ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) = (‖x‖ * ‖y‖) ^ 2 := by ring
  rw [hnorm, Real.sqrt_sq (by positivity), mul_div_mul_left]

/-- The angle between an orthogonal sum and its nonzero first summand is less than `π / 2`. -/
theorem angle_add_lt_pi_div_two_of_inner_eq_zero :
    angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) < π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h (hx := hx), Real.arccos_lt_pi_div_two]
  exact div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr (add_ne_zero_of_inner_eq_zero h hx))

/-- The angle between an orthogonal sum and its nonzero first summand is at most `π / 2`. -/
theorem angle_add_le_pi_div_two_of_inner_eq_zero :
    angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) ≤ π / 2 :=
  (angle_add_lt_pi_div_two_of_inner_eq_zero h).le

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem angle_add_eq_arcsin_of_inner_eq_zero :
    angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) =
      Real.arcsin (Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_inner_eq_zero h (hx := hx))) := by
  rw [← sin_angle_add_of_inner_eq_zero h (hx := hx)]
  have hxy := add_ne_zero_of_inner_eq_zero h hx
  exact (Real.arcsin_sin (by linarith [Real.pi_pos, angle_nonneg x (x + y) (hx := hx) (hy := hxy)])
    (angle_add_le_pi_div_two_of_inner_eq_zero h (hx := hx))).symm

/-- The cosine of the angle between an orthogonal sum and its nonzero first summand is positive. -/
theorem cos_angle_add_pos_of_inner_eq_zero :
    0 < Real.cos (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) := by
  rw [cos_angle_add_of_inner_eq_zero h (hx := hx)]
  exact div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr (add_ne_zero_of_inner_eq_zero h hx))

/-- The sine of the angle between two orthogonal nonzero summands and their sum is positive. -/
theorem sin_angle_add_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < Real.sin (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) := by
  rw [sin_angle_add_of_inner_eq_zero h (hx := hx)]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr (add_ne_zero_of_inner_eq_zero h hx))

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_angle_add_of_inner_eq_zero :
    Real.tan (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_add_pos_of_inner_eq_zero h (hx := hx)).ne' = ‖y‖ / ‖x‖ := by
  simp only [Real.tan_eq_sin_div_cos, sin_angle_add_of_inner_eq_zero h (hx := hx),
    cos_angle_add_of_inner_eq_zero h (hx := hx), div_div_div_cancel_right₀]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem angle_add_eq_arctan_of_inner_eq_zero :
    angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← tan_angle_add_of_inner_eq_zero h (hx := hx)]
  have hxy := add_ne_zero_of_inner_eq_zero h hx
  exact (Real.arctan_tan (by linarith [Real.pi_pos, angle_nonneg x (x + y) (hx := hx) (hy := hxy)])
    (angle_add_lt_pi_div_two_of_inner_eq_zero h (hx := hx))).symm

/-- An angle in a right-angled triangle with nonzero legs is positive. -/
theorem angle_add_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx) := by
  have hxy := add_ne_zero_of_inner_eq_zero h hx
  apply (angle_nonneg x (x + y) (hx := hx) (hy := hxy)).lt_of_ne
  intro heq
  have hs := sin_angle_add_pos_of_inner_eq_zero h (hx := hx) hy
  rw [← heq, Real.sin_zero] at hs
  exact (lt_irrefl 0) hs

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_angle_add_mul_norm_of_inner_eq_zero :
    Real.cos (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) * ‖x + y‖ = ‖x‖ := by
  rw [cos_angle_add_of_inner_eq_zero h (hx := hx), div_mul_cancel₀]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_angle_add_mul_norm_of_inner_eq_zero :
    Real.sin (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)) * ‖x + y‖ = ‖y‖ := by
  rw [sin_angle_add_of_inner_eq_zero h (hx := hx), div_mul_cancel₀]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_angle_add_mul_norm_of_inner_eq_zero :
    Real.tan (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_add_pos_of_inner_eq_zero h (hx := hx)).ne' * ‖x‖ = ‖y‖ := by
  rw [tan_angle_add_of_inner_eq_zero h (hx := hx), div_mul_cancel₀]

/-- The tangent of the angle between an orthogonal sum and its first summand is positive
when both summands are nonzero. -/
theorem tan_angle_add_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < Real.tan (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_add_pos_of_inner_eq_zero h (hx := hx)).ne' := by
  rw [tan_angle_add_of_inner_eq_zero h (hx := hx)]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_angle_add_of_inner_eq_zero :
    Checked.div ‖x‖ (Real.cos (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)))
      (cos_angle_add_pos_of_inner_eq_zero h (hx := hx)).ne'.isUnit = ‖x + y‖ := by
  rw [div_eq_iff, mul_comm, cos_angle_add_mul_norm_of_inner_eq_zero h (hx := hx)]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_angle_add_of_inner_eq_zero (hy : y ≠ 0) :
    Checked.div ‖y‖ (Real.sin (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx)))
      (sin_angle_add_pos_of_inner_eq_zero h (hx := hx) hy).ne'.isUnit = ‖x + y‖ := by
  rw [div_eq_iff, mul_comm, sin_angle_add_mul_norm_of_inner_eq_zero h (hx := hx)]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_angle_add_of_inner_eq_zero (hy : y ≠ 0) :
    Checked.div ‖y‖ (Real.tan (angle x (x + y) hx (add_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_add_pos_of_inner_eq_zero h (hx := hx)).ne')
      (tan_angle_add_pos_of_inner_eq_zero h (hx := hx) hy).ne'.isUnit = ‖x‖ := by
  rw [div_eq_iff, mul_comm, tan_angle_add_mul_norm_of_inner_eq_zero h (hx := hx)]

end Add

private theorem inner_neg_right_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : ⟪x, -y⟫ = 0 := by
  simp only [inner_neg_right, h, neg_zero]

/-- The difference of two orthogonal vectors is nonzero if the first vector is nonzero. -/
theorem sub_ne_zero_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (hx : x ≠ 0) :
    x - y ≠ 0 := by
  simpa only [sub_eq_add_neg] using add_ne_zero_of_inner_eq_zero (inner_neg_right_eq_zero h) hx

/-- The norm of the difference of orthogonal vectors is invertible when the first is nonzero. -/
theorem isUnit_norm_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) {hx : x ≠ 0} :
    IsUnit ‖x - y‖ :=
  (norm_ne_zero_iff.mpr (sub_ne_zero_of_inner_eq_zero h hx)).isUnit

section Sub

variable {x y : V} (h : ⟪x, y⟫ = 0) {hx : x ≠ 0}

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem angle_sub_eq_arccos_of_inner_eq_zero :
    angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) =
      Real.arccos (Checked.div ‖x‖ ‖x - y‖ (isUnit_norm_sub_of_inner_eq_zero h (hx := hx))) := by
  simpa only [sub_eq_add_neg] using
    angle_add_eq_arccos_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem angle_sub_eq_arcsin_of_inner_eq_zero :
    angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) =
      Real.arcsin (Checked.div ‖y‖ ‖x - y‖ (isUnit_norm_sub_of_inner_eq_zero h (hx := hx))) := by
  simpa only [sub_eq_add_neg, norm_neg] using
    angle_add_eq_arcsin_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem angle_sub_eq_arctan_of_inner_eq_zero :
    angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) = Real.arctan (‖y‖ / ‖x‖) := by
  simpa only [sub_eq_add_neg, norm_neg] using
    angle_add_eq_arctan_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- An angle in a non-degenerate right-angled triangle is positive, version subtracting
vectors. -/
theorem angle_sub_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) := by
  simpa only [sub_eq_add_neg] using
    angle_add_pos_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx) (neg_ne_zero.mpr hy)

/-- An angle in a right-angled triangle is at most `π / 2`, version subtracting vectors. -/
theorem angle_sub_le_pi_div_two_of_inner_eq_zero :
    angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) ≤ π / 2 := by
  simpa only [sub_eq_add_neg] using
    angle_add_le_pi_div_two_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`, version subtracting
vectors. -/
theorem angle_sub_lt_pi_div_two_of_inner_eq_zero :
    angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx) < π / 2 := by
  simpa only [sub_eq_add_neg] using
    angle_add_lt_pi_div_two_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_angle_sub_of_inner_eq_zero :
    Real.cos (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) =
      Checked.div ‖x‖ ‖x - y‖ (isUnit_norm_sub_of_inner_eq_zero h (hx := hx)) := by
  simpa only [sub_eq_add_neg] using
    cos_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_angle_sub_of_inner_eq_zero :
    Real.sin (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) =
      Checked.div ‖y‖ ‖x - y‖ (isUnit_norm_sub_of_inner_eq_zero h (hx := hx)) := by
  simpa only [sub_eq_add_neg, norm_neg] using
    sin_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The cosine of an angle adjacent to a nonzero leg of a right triangle is positive. -/
theorem cos_angle_sub_pos_of_inner_eq_zero :
    0 < Real.cos (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) := by
  simpa only [sub_eq_add_neg] using
    cos_angle_add_pos_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The sine of an angle with nonzero opposite and adjacent legs is positive. -/
theorem sin_angle_sub_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < Real.sin (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) := by
  simpa only [sub_eq_add_neg] using
    sin_angle_add_pos_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx) (neg_ne_zero.mpr hy)

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_angle_sub_of_inner_eq_zero :
    Real.tan (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_sub_pos_of_inner_eq_zero h (hx := hx)).ne' = ‖y‖ / ‖x‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using
    tan_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_angle_sub_mul_norm_of_inner_eq_zero :
    Real.cos (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) * ‖x - y‖ = ‖x‖ := by
  simpa only [sub_eq_add_neg] using
    cos_angle_add_mul_norm_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_angle_sub_mul_norm_of_inner_eq_zero :
    Real.sin (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)) * ‖x - y‖ = ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using
    sin_angle_add_mul_norm_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_angle_sub_mul_norm_of_inner_eq_zero :
    Real.tan (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_sub_pos_of_inner_eq_zero h (hx := hx)).ne' * ‖x‖ = ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using
    tan_angle_add_mul_norm_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- The tangent of an angle with nonzero opposite and adjacent legs is positive. -/
theorem tan_angle_sub_pos_of_inner_eq_zero (hy : y ≠ 0) :
    0 < Real.tan (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_sub_pos_of_inner_eq_zero h (hx := hx)).ne' := by
  simpa only [sub_eq_add_neg] using
    tan_angle_add_pos_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx) (neg_ne_zero.mpr hy)

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_angle_sub_of_inner_eq_zero :
    Checked.div ‖x‖ (Real.cos (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)))
      (cos_angle_sub_pos_of_inner_eq_zero h (hx := hx)).ne'.isUnit = ‖x - y‖ := by
  simpa only [sub_eq_add_neg] using
    norm_div_cos_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_angle_sub_of_inner_eq_zero (hy : y ≠ 0) :
    Checked.div ‖y‖ (Real.sin (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx)))
      (sin_angle_sub_pos_of_inner_eq_zero h (hx := hx) hy).ne'.isUnit = ‖x - y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using
    norm_div_sin_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)
      (neg_ne_zero.mpr hy)

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_angle_sub_of_inner_eq_zero (hy : y ≠ 0) :
    Checked.div ‖y‖ (Real.tan (angle x (x - y) hx (sub_ne_zero_of_inner_eq_zero h hx))
      (cos_angle_sub_pos_of_inner_eq_zero h (hx := hx)).ne')
      (tan_angle_sub_pos_of_inner_eq_zero h (hx := hx) hy).ne'.isUnit = ‖x‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using
    norm_div_tan_angle_add_of_inner_eq_zero (inner_neg_right_eq_zero h) (hx := hx)
      (neg_ne_zero.mpr hy)

end Sub

end InnerProductGeometry

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P)
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by
  rw [dist_comm p₃ p₂, dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂,
    dist_eq_norm_vsub V p₂ p₃, angle, ← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
    vsub_sub_vsub_cancel_right p₁, ← neg_vsub_eq_vsub_rev p₂ p₃, norm_neg]

/-- The angle at `p₂` is at least `π / 2` if and only if the square of the opposite side is at
least the sum of the squares of the other two sides. -/
theorem dist_sq_add_dist_sq_le_dist_sq_iff_pi_div_two_le_angle {p₁ p₂ p₃ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ≤ dist p₁ p₃ * dist p₁ p₃ ↔
      π / 2 ≤ ∠ p₁ p₂ p₃ := by
  rw [angle, ← inner_nonpos_iff_pi_div_two_le_angle, dist_eq_norm_vsub V p₁ p₃,
    dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂,
    show (p₁ -ᵥ p₃ : V) = (p₁ -ᵥ p₂) - (p₃ -ᵥ p₂) from (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm,
    norm_sub_mul_self_real]
  constructor <;> intro h <;> linarith

/-- The endpoints of a right angle are distinct. -/
theorem left_ne_right_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} (h : ∠ p₁ p₂ p₃ = π / 2) : p₁ ≠ p₃ := by
  intro heq
  subst p₃
  rw [angle_self_of_ne (h := hp₁p₂)] at h
  linarith [Real.pi_pos]

section RightTriangle

variable {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} (h : ∠ p₁ p₂ p₃ = π / 2)

private theorem inner_right_angle_vsub (h : ∠ p₁ p₂ p₃ = π / 2) :
    ⟪p₂ -ᵥ p₃, p₁ -ᵥ p₂⟫ = 0 := by
  have hzero := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two
    (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) (hx := vsub_ne_zero.mpr hp₁p₂) (hy := vsub_ne_zero.mpr hp₃p₂)).mpr h
  have hs := (real_inner_comm (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)).trans hzero
  rw [← neg_vsub_eq_vsub_rev p₃ p₂, inner_neg_left, hs, neg_zero]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem angle_eq_arccos_of_angle_eq_pi_div_two :
    angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) =
      Real.arccos (Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.mpr (left_ne_right_of_angle_eq_pi_div_two h)).isUnit) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    angle_add_eq_arccos_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem angle_eq_arcsin_of_angle_eq_pi_div_two :
    angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) =
      Real.arcsin (Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.mpr (left_ne_right_of_angle_eq_pi_div_two h)).isUnit) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub V p₁ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    angle_add_eq_arcsin_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem angle_eq_arctan_of_angle_eq_pi_div_two :
    angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) =
      Real.arctan (Checked.div (dist p₁ p₂) (dist p₃ p₂) (dist_ne_zero.mpr hp₃p₂).isUnit) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₂] using
    angle_add_eq_arctan_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- An angle in a non-degenerate right-angled triangle is positive. -/
theorem angle_pos_of_angle_eq_pi_div_two :
    0 < angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    angle_add_pos_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm) (vsub_ne_zero.mpr hp₁p₂)

/-- An angle in a right-angled triangle is at most `π / 2`. -/
theorem angle_le_pi_div_two_of_angle_eq_pi_div_two :
    angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) ≤ π / 2 := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    angle_add_le_pi_div_two_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`. -/
theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two :
    angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h) < π / 2 := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    angle_add_lt_pi_div_two_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_angle_of_angle_eq_pi_div_two :
    Real.cos (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) =
      Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.mpr (left_ne_right_of_angle_eq_pi_div_two h)).isUnit := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    cos_angle_add_of_inner_eq_zero (inner_right_angle_vsub h) (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_angle_of_angle_eq_pi_div_two :
    Real.sin (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) =
      Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.mpr (left_ne_right_of_angle_eq_pi_div_two h)).isUnit := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub V p₁ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    sin_angle_add_of_inner_eq_zero (inner_right_angle_vsub h) (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The cosine of an acute angle of a right triangle is positive. -/
theorem cos_angle_pos_of_angle_eq_pi_div_two :
    0 < Real.cos (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    cos_angle_add_pos_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The sine of an acute angle of a right triangle is positive. -/
theorem sin_angle_pos_of_angle_eq_pi_div_two :
    0 < Real.sin (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    sin_angle_add_pos_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm) (vsub_ne_zero.mpr hp₁p₂)

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_angle_of_angle_eq_pi_div_two :
    Real.tan (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h))
      (cos_angle_pos_of_angle_eq_pi_div_two h).ne' =
      Checked.div (dist p₁ p₂) (dist p₃ p₂) (dist_ne_zero.mpr hp₃p₂).isUnit := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₂] using
    tan_angle_add_of_inner_eq_zero (inner_right_angle_vsub h) (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_angle_mul_dist_of_angle_eq_pi_div_two :
    Real.cos (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) * dist p₁ p₃ =
      dist p₃ p₂ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    cos_angle_add_mul_norm_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_angle_mul_dist_of_angle_eq_pi_div_two :
    Real.sin (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)) * dist p₁ p₃ =
      dist p₁ p₂ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub V p₁ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    sin_angle_add_mul_norm_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_angle_mul_dist_of_angle_eq_pi_div_two :
    Real.tan (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h))
      (cos_angle_pos_of_angle_eq_pi_div_two h).ne' * dist p₃ p₂ = dist p₁ p₂ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₂] using
    tan_angle_add_mul_norm_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- The tangent of an acute angle of a right triangle is positive. -/
theorem tan_angle_pos_of_angle_eq_pi_div_two :
    0 < Real.tan (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h))
      (cos_angle_pos_of_angle_eq_pi_div_two h).ne' := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel] using
    tan_angle_add_pos_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm) (vsub_ne_zero.mpr hp₁p₂)

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_angle_of_angle_eq_pi_div_two :
    Checked.div (dist p₃ p₂)
      (Real.cos (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)))
      (cos_angle_pos_of_angle_eq_pi_div_two h).ne'.isUnit = dist p₁ p₃ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    norm_div_cos_angle_add_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm)

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_angle_of_angle_eq_pi_div_two :
    Checked.div (dist p₁ p₂)
      (Real.sin (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h)))
      (sin_angle_pos_of_angle_eq_pi_div_two h).ne'.isUnit = dist p₁ p₃ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub V p₁ p₂, ← dist_eq_norm_vsub V p₁ p₃] using
    norm_div_sin_angle_add_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm) (vsub_ne_zero.mpr hp₁p₂)

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_angle_of_angle_eq_pi_div_two :
    Checked.div (dist p₁ p₂)
      (Real.tan (angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi_div_two h))
        (cos_angle_pos_of_angle_eq_pi_div_two h).ne')
      (tan_angle_pos_of_angle_eq_pi_div_two h).ne'.isUnit = dist p₃ p₂ := by
  simpa only [angle, add_comm (p₂ -ᵥ p₃ : V) (p₁ -ᵥ p₂), vsub_add_vsub_cancel,
    ← dist_eq_norm_vsub' V p₃ p₂, ← dist_eq_norm_vsub V p₁ p₂] using
    norm_div_tan_angle_add_of_inner_eq_zero (inner_right_angle_vsub h)
      (hx := vsub_ne_zero.mpr hp₃p₂.symm) (vsub_ne_zero.mpr hp₁p₂)

end RightTriangle

/-- An altitude whose foot is strictly between the endpoints has an apex distinct from the
right endpoint. -/
theorem right_ne_of_altitude {p₁ p₂ p₃ p₄ : P} {hp₂p₄ : p₂ ≠ p₄}
    (hf : Sbtw ℝ p₁ p₄ p₃) (hc : angle p₁ p₄ p₂ hf.left_ne hp₂p₄ = π / 2) :
    p₃ ≠ p₂ := by
  intro heq
  subst p₂
  linarith [hf.angle₁₂₃_eq_pi, Real.pi_pos]

/-- **Geometric mean theorem** (or right triangle altitude theorem), if-and-only-if form: if
`p₄` lies strictly between `p₁` and `p₃` and `∠ p₁ p₄ p₂` is a right angle (so that `p₄` is the
foot of the altitude from `p₂` in the triangle `p₁ p₂ p₃`), then the square of `dist p₂ p₄`
equals the product of `dist p₁ p₄` and `dist p₃ p₄` if and only if the angle at `p₂` is a right
angle. -/
theorem dist_sq_eq_dist_mul_dist_iff_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ : P}
    (hf : Sbtw ℝ p₁ p₄ p₃) {hp₂p₄ : p₂ ≠ p₄} (hc : angle p₁ p₄ p₂ hf.left_ne hp₂p₄ = π / 2) :
    dist p₂ p₄ ^ 2 = dist p₁ p₄ * dist p₃ p₄ ↔
      angle p₁ p₂ p₃ (left_ne_right_of_angle_eq_pi_div_two hc)
        (right_ne_of_altitude hf hc) = π / 2 := by
  have hOrth := hc
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two] at hOrth ⊢
  obtain ⟨-, r, hr, hw⟩ := angle_eq_pi_iff.mp hf.angle₁₂₃_eq_pi
  rw [dist_eq_norm_vsub V p₂ p₄, dist_eq_norm_vsub V p₁ p₄, dist_eq_norm_vsub V p₃ p₄,
    ← vsub_sub_vsub_cancel_right p₁ p₂ p₄, ← vsub_sub_vsub_cancel_right p₃ p₂ p₄, hw]
  set u := p₁ -ᵥ p₄
  set v := p₂ -ᵥ p₄
  have hOrth' : ⟪v, u⟫ = 0 := (real_inner_comm u v).trans hOrth
  have hexp : ⟪u - v, r • u - v⟫ = ‖v‖ ^ 2 - ‖u‖ * (-r * ‖u‖) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, hOrth, hOrth',
      real_inner_self_eq_norm_sq]
    ring
  rw [hexp, norm_smul, Real.norm_eq_abs, abs_of_neg hr, sub_eq_zero, eq_comm]

/-- **Geometric mean theorem** (or right triangle altitude theorem): in a right-angled triangle
`p₁ p₂ p₃` with the right angle at `p₂`, the square of the altitude `dist p₂ p₄` to the
hypotenuse is the product of the two segments `dist p₁ p₄` and `dist p₃ p₄` into which its foot
`p₄` divides the hypotenuse. -/
theorem dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ : P} (hf : Sbtw ℝ p₁ p₄ p₃)
    {hp₂p₄ : p₂ ≠ p₄} (hc : angle p₁ p₄ p₂ hf.left_ne hp₂p₄ = π / 2)
    (h : angle p₁ p₂ p₃ (left_ne_right_of_angle_eq_pi_div_two hc)
      (right_ne_of_altitude hf hc) = π / 2) :
    dist p₂ p₄ ^ 2 = dist p₁ p₄ * dist p₃ p₄ :=
  (dist_sq_eq_dist_mul_dist_iff_angle_eq_pi_div_two hf hc).mpr h

/-- Geometric mean relation for a leg of a right-angled triangle: under the hypotheses of the
geometric mean theorem, the square of the leg `dist p₁ p₂` is the product of the hypotenuse
`dist p₁ p₃` and its segment `dist p₁ p₄` adjacent to that leg. -/
theorem dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two' {p₁ p₂ p₃ p₄ : P} (hf : Sbtw ℝ p₁ p₄ p₃)
    {hp₂p₄ : p₂ ≠ p₄} (hc : angle p₁ p₄ p₂ hf.left_ne hp₂p₄ = π / 2)
    (h : angle p₁ p₂ p₃ (left_ne_right_of_angle_eq_pi_div_two hc)
      (right_ne_of_altitude hf hc) = π / 2) :
    dist p₁ p₂ ^ 2 = dist p₁ p₃ * dist p₁ p₄ := by
  rw [pow_two, (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₄ p₂
    (hp₁p₂ := hf.left_ne) (hp₃p₂ := hp₂p₄)).mpr hc,
    ← pow_two (dist p₂ p₄), dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two hf hc h,
    dist_eq_add_dist_of_angle_eq_pi hf.angle₁₂₃_eq_pi]
  ring

end EuclideanGeometry

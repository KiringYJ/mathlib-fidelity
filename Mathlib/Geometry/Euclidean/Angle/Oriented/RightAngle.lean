/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometric results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [hd2 : Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

private theorem oangle_neg_orientation_rev (x y : V) :
    (-o).oangle y x = o.oangle x y := by
  rw [oangle_neg_orientation_eq_neg, oangle_rev, neg_neg]

private theorem oangle_add_right_eq_angle {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = InnerProductGeometry.angle x (x + y)
      (o.left_ne_zero_of_oangle_eq_pi_div_two h)
      (InnerProductGeometry.add_ne_zero_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
        (o.left_ne_zero_of_oangle_eq_pi_div_two h)) :=
  o.oangle_eq_angle_of_sign_eq_one (by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two])

private theorem oangle_sub_right_eq_angle {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = InnerProductGeometry.angle y (y - x)
      (o.right_ne_zero_of_oangle_eq_pi_div_two h)
      (InnerProductGeometry.sub_ne_zero_of_inner_eq_zero
        (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
        (o.right_ne_zero_of_oangle_eq_pi_div_two h)) :=
  o.oangle_eq_angle_of_sign_eq_one (by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two])

/-- The hypotenuse length of a positively oriented right triangle is invertible. -/
theorem isUnit_norm_add_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : IsUnit ‖x + y‖ :=
  InnerProductGeometry.isUnit_norm_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
    (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)

/-- The hypotenuse length of a positively oriented right triangle is invertible. -/
theorem isUnit_norm_sub_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : IsUnit ‖x - y‖ :=
  InnerProductGeometry.isUnit_norm_sub_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
    (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)

/-- The hypotenuse length of a positively oriented right triangle is invertible. -/
theorem isUnit_norm_sub_rev_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : IsUnit ‖y - x‖ :=
  InnerProductGeometry.isUnit_norm_sub_of_inner_eq_zero
    (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
    (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)

/-- The cosine of this acute angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_add_right_pos {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.cos (o.oangle x (x + y)) := by
  rw [oangle_add_right_eq_angle o h, Real.Angle.cos_coe]
  exact InnerProductGeometry.cos_angle_add_pos_of_inner_eq_zero
    (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)

/-- The cosine of this acute angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_add_left_pos {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.cos (o.oangle (x + y) y) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using cos_oangle_add_right_pos (-o) h'

/-- The cosine of this acute angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_sub_right_pos {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.cos (o.oangle y (y - x)) := by
  rw [oangle_sub_right_eq_angle o h, Real.Angle.cos_coe]
  exact InnerProductGeometry.cos_angle_sub_pos_of_inner_eq_zero
    (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
    (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)

/-- The cosine of this acute angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_sub_left_pos {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.cos (o.oangle (x - y) x) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using cos_oangle_sub_right_pos (-o) h'

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arccos
      (Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h)) := by
  rw [oangle_add_right_eq_angle o h,
    InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos
      (Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h)) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using
    (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h'

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin
      (Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h)) := by
  rw [oangle_add_right_eq_angle o h,
    InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin
      (Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h)) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using
    (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h'

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan
      (Checked.div ‖y‖ ‖x‖
        (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit) := by
  rw [oangle_add_right_eq_angle o h,
    InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan
      (Checked.div ‖x‖ ‖y‖
        (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using
    (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h'

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) =
      Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h) := by
  rw [oangle_add_right_eq_angle o h, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) =
      Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using
    (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h'

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) =
      Checked.div ‖y‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h) := by
  rw [oangle_add_right_eq_angle o h, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (hx := o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) =
      Checked.div ‖x‖ ‖x + y‖ (isUnit_norm_add_of_oangle_eq_pi_div_two o h) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev, add_comm y x] using
    (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h'

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) (cos_oangle_add_right_pos o h).ne' =
      Checked.div ‖y‖ ‖x‖
        (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit := by
  rw [Real.Angle.tan_eq_sin_div_cos]
  apply div_eq_div_iff.2
  rw [sin_oangle_add_right_of_oangle_eq_pi_div_two o h,
    cos_oangle_add_right_of_oangle_eq_pi_div_two o h]
  field

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) (cos_oangle_add_left_pos o h).ne' =
      Checked.div ‖x‖ ‖y‖
        (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit := by
  rw [Real.Angle.tan_eq_sin_div_cos]
  apply div_eq_div_iff.2
  rw [sin_oangle_add_left_of_oangle_eq_pi_div_two o h,
    cos_oangle_add_left_of_oangle_eq_pi_div_two o h]
  field

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_add_of_oangle_eq_pi_div_two o h))).1
    (cos_oangle_add_right_of_oangle_eq_pi_div_two o h)

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_add_of_oangle_eq_pi_div_two o h))).1
    (cos_oangle_add_left_of_oangle_eq_pi_div_two o h)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_add_of_oangle_eq_pi_div_two o h))).1
    (sin_oangle_add_right_of_oangle_eq_pi_div_two o h)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_add_of_oangle_eq_pi_div_two o h))).1
    (sin_oangle_add_left_of_oangle_eq_pi_div_two o h)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) (cos_oangle_add_right_pos o h).ne' * ‖x‖ = ‖y‖ := by
  exact (eq_div_iff
    (hb := (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit)).1
    (tan_oangle_add_right_of_oangle_eq_pi_div_two o h)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) (cos_oangle_add_left_pos o h).ne' * ‖y‖ = ‖x‖ := by
  exact (eq_div_iff
    (hb := (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit)).1
    (tan_oangle_add_left_of_oangle_eq_pi_div_two o h)

/-- The sine of this acute angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_add_right_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : 0 < Real.Angle.sin (o.oangle x (x + y)) := by
  rw [sin_oangle_add_right_of_oangle_eq_pi_div_two o h]
  have hden : 0 < ‖x + y‖ := lt_of_le_of_ne (norm_nonneg _)
    (isUnit_norm_add_of_oangle_eq_pi_div_two o h).ne_zero.symm
  exact div_pos (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)) hden

/-- The sine of this acute angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_add_left_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : 0 < Real.Angle.sin (o.oangle (x + y) y) := by
  rw [sin_oangle_add_left_of_oangle_eq_pi_div_two o h]
  have hden : 0 < ‖x + y‖ := lt_of_le_of_ne (norm_nonneg _)
    (isUnit_norm_add_of_oangle_eq_pi_div_two o h).ne_zero.symm
  exact div_pos (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)) hden

/-- The tangent of this acute angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_add_right_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.tan (o.oangle x (x + y)) (cos_oangle_add_right_pos o h).ne' := by
  rw [tan_oangle_add_right_of_oangle_eq_pi_div_two o h]
  exact div_pos (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h))
    (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h))

/-- The tangent of this acute angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_add_left_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.tan (o.oangle (x + y) y) (cos_oangle_add_left_pos o h).ne' := by
  rw [tan_oangle_add_left_of_oangle_eq_pi_div_two o h]
  exact div_pos (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h))
    (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h))

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.cos (o.oangle x (x + y)))
      (cos_oangle_add_right_pos o h).ne'.isUnit = ‖x + y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.cos (o.oangle (x + y) y))
      (cos_oangle_add_left_pos o h).ne'.isUnit = ‖x + y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.sin (o.oangle x (x + y)))
      (sin_oangle_add_right_pos o h).ne'.isUnit = ‖x + y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.sin (o.oangle (x + y) y))
      (sin_oangle_add_left_pos o h).ne'.isUnit = ‖x + y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.tan (o.oangle x (x + y)) (cos_oangle_add_right_pos o h).ne')
      (tan_oangle_add_right_pos o h).ne'.isUnit = ‖x‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.tan (o.oangle (x + y) y) (cos_oangle_add_left_pos o h).ne')
      (tan_oangle_add_left_pos o h).ne'.isUnit = ‖y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arccos
      (Checked.div ‖y‖ ‖y - x‖ (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h)) := by
  rw [oangle_sub_right_eq_angle o h,
    InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arccos
      (Checked.div ‖x‖ ‖x - y‖ (isUnit_norm_sub_of_oangle_eq_pi_div_two o h)) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using
    (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h'

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arcsin
      (Checked.div ‖x‖ ‖y - x‖ (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h)) := by
  rw [oangle_sub_right_eq_angle o h,
    InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arcsin
      (Checked.div ‖y‖ ‖x - y‖ (isUnit_norm_sub_of_oangle_eq_pi_div_two o h)) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using
    (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h'

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arctan
      (Checked.div ‖x‖ ‖y‖
        (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit) := by
  rw [oangle_sub_right_eq_angle o h,
    InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arctan
      (Checked.div ‖y‖ ‖x‖
        (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using
    (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h'

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) =
      Checked.div ‖y‖ ‖y - x‖ (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h) := by
  rw [oangle_sub_right_eq_angle o h, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) =
      Checked.div ‖x‖ ‖x - y‖ (isUnit_norm_sub_of_oangle_eq_pi_div_two o h) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h'

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle y (y - x)) =
      Checked.div ‖x‖ ‖y - x‖ (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h) := by
  rw [oangle_sub_right_eq_angle o h, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (hx := o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) =
      Checked.div ‖y‖ ‖x - y‖ (isUnit_norm_sub_of_oangle_eq_pi_div_two o h) := by
  have h' := (oangle_neg_orientation_rev o x y).trans h
  simpa only [oangle_neg_orientation_rev] using (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h'

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) (cos_oangle_sub_right_pos o h).ne' =
      Checked.div ‖x‖ ‖y‖
        (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit := by
  rw [Real.Angle.tan_eq_sin_div_cos]
  apply div_eq_div_iff.2
  rw [sin_oangle_sub_right_of_oangle_eq_pi_div_two o h,
    cos_oangle_sub_right_of_oangle_eq_pi_div_two o h]
  field

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) (cos_oangle_sub_left_pos o h).ne' =
      Checked.div ‖y‖ ‖x‖
        (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit := by
  rw [Real.Angle.tan_eq_sin_div_cos]
  apply div_eq_div_iff.2
  rw [sin_oangle_sub_left_of_oangle_eq_pi_div_two o h,
    cos_oangle_sub_left_of_oangle_eq_pi_div_two o h]
  field

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h))).1
    (cos_oangle_sub_right_of_oangle_eq_pi_div_two o h)

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_sub_of_oangle_eq_pi_div_two o h))).1
    (cos_oangle_sub_left_of_oangle_eq_pi_div_two o h)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h))).1
    (sin_oangle_sub_right_of_oangle_eq_pi_div_two o h)

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ := by
  exact (eq_div_iff (hb := (isUnit_norm_sub_of_oangle_eq_pi_div_two o h))).1
    (sin_oangle_sub_left_of_oangle_eq_pi_div_two o h)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) (cos_oangle_sub_right_pos o h).ne' * ‖y‖ = ‖x‖ := by
  exact (eq_div_iff
    (hb := (norm_ne_zero_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)).isUnit)).1
    (tan_oangle_sub_right_of_oangle_eq_pi_div_two o h)

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) (cos_oangle_sub_left_pos o h).ne' * ‖x‖ = ‖y‖ := by
  exact (eq_div_iff
    (hb := (norm_ne_zero_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)).isUnit)).1
    (tan_oangle_sub_left_of_oangle_eq_pi_div_two o h)

/-- The sine of this acute angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_sub_right_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : 0 < Real.Angle.sin (o.oangle y (y - x)) := by
  rw [sin_oangle_sub_right_of_oangle_eq_pi_div_two o h]
  have hden : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _)
    (isUnit_norm_sub_rev_of_oangle_eq_pi_div_two o h).ne_zero.symm
  exact div_pos (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h)) hden

/-- The sine of this acute angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_sub_left_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : 0 < Real.Angle.sin (o.oangle (x - y) x) := by
  rw [sin_oangle_sub_left_of_oangle_eq_pi_div_two o h]
  have hden : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _)
    (isUnit_norm_sub_of_oangle_eq_pi_div_two o h).ne_zero.symm
  exact div_pos (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h)) hden

/-- The tangent of this acute angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_sub_right_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.tan (o.oangle y (y - x)) (cos_oangle_sub_right_pos o h).ne' := by
  rw [tan_oangle_sub_right_of_oangle_eq_pi_div_two o h]
  exact div_pos (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h))
    (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h))

/-- The tangent of this acute angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_sub_left_pos {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    0 < Real.Angle.tan (o.oangle (x - y) x) (cos_oangle_sub_left_pos o h).ne' := by
  rw [tan_oangle_sub_left_of_oangle_eq_pi_div_two o h]
  exact div_pos (norm_pos_iff.2 (o.right_ne_zero_of_oangle_eq_pi_div_two h))
    (norm_pos_iff.2 (o.left_ne_zero_of_oangle_eq_pi_div_two h))

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.cos (o.oangle y (y - x)))
      (cos_oangle_sub_right_pos o h).ne'.isUnit = ‖y - x‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.cos (o.oangle (x - y) x))
      (cos_oangle_sub_left_pos o h).ne'.isUnit = ‖x - y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.sin (o.oangle y (y - x)))
      (sin_oangle_sub_right_pos o h).ne'.isUnit = ‖y - x‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.sin (o.oangle (x - y) x))
      (sin_oangle_sub_left_pos o h).ne'.isUnit = ‖x - y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖x‖ (Real.Angle.tan (o.oangle y (y - x)) (cos_oangle_sub_right_pos o h).ne')
      (tan_oangle_sub_right_pos o h).ne'.isUnit = ‖y‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) :
    Checked.div ‖y‖ (Real.Angle.tan (o.oangle (x - y) x) (cos_oangle_sub_left_pos o h).ne')
      (tan_oangle_sub_left_pos o h).ne'.isUnit = ‖x‖ := by
  apply div_eq_iff.2
  simpa only [mul_comm] using (tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two o h).symm

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
theorem oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle x (x + r • o.rotation (π / 2 : ℝ) x) = Real.arctan r := by
  have hratio : Checked.div ‖r • o.rotation (π / 2 : ℝ) x‖ ‖x‖
      (norm_ne_zero_iff.2 h).isUnit = |r| := by
    apply div_eq_iff.2
    rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = -(π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_neg _ _ hr, o.oangle_neg_right h, o.oangle_rotation_self_right h, ←
        sub_eq_zero, add_comm, sub_neg_eq_add, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
        add_assoc, add_halves, ← two_mul, Real.Angle.coe_two_pi]
      simpa using h
    rw [← neg_inj, ← oangle_neg_orientation_eq_neg, neg_neg] at ha
    have H := (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha
    rw [oangle_neg_orientation_eq_neg, hratio, abs_of_neg hr, Real.arctan_neg,
      Real.Angle.coe_neg] at H
    exact neg_inj.mp H
  · simp
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = (π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right h]
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, hratio, abs_of_pos hr]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
theorem oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)
      = Real.arctan (Checked.inv r hr.isUnit) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, ←
    neg_neg ((π / 2 : ℝ) : Real.Angle), ← rotation_neg_orientation_eq_neg, add_comm]
  have hx : x = Checked.inv r hr.isUnit •
      (-o).rotation (π / 2 : ℝ) (r • (-o).rotation (-(π / 2 : ℝ)) x) := by simp
  nth_rw 3 [hx]
  refine (-o).oangle_add_right_smul_rotation_pi_div_two ?_ _
  simp [hr, h]

/-- The cosine after adding a multiple of a quarter turn is positive. -/
theorem cos_oangle_add_right_smul_rotation_pi_div_two_pos {x : V} (h : x ≠ 0) (r : ℝ) :
    0 < Real.Angle.cos (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x)) := by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h, Real.Angle.cos_coe]
  exact Real.cos_arctan_pos _

/-- The cosine of the angle to the nonzero rotated leg is positive. -/
theorem cos_oangle_add_left_smul_rotation_pi_div_two_pos {x : V} (h : x ≠ 0)
    (r : ℝ) (hr : r ≠ 0) :
    0 < Real.Angle.cos
      (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)) := by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h r hr, Real.Angle.cos_coe]
  exact Real.cos_arctan_pos _

private theorem tan_eq_of_eq_arctan {θ : Real.Angle} {r : ℝ} (h : θ = ↑(Real.arctan r))
    {hc : Real.Angle.cos θ ≠ 0} : Real.Angle.tan θ hc = r := by
  subst θ
  rw [Real.Angle.tan_coe, Real.tan_arctan]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x))
      (o.cos_oangle_add_right_smul_rotation_pi_div_two_pos h r).ne' = r :=
  tan_eq_of_eq_arctan (o.oangle_add_right_smul_rotation_pi_div_two h r)

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x))
      (o.cos_oangle_add_left_smul_rotation_pi_div_two_pos h r hr).ne' = Checked.inv r hr.isUnit :=
  tan_eq_of_eq_arctan (o.oangle_add_left_smul_rotation_pi_div_two h r hr)

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    o.oangle (r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x - x)
      = Real.arctan (Checked.inv r hr.isUnit) := by
  have hx : -x = Checked.inv r hr.isUnit •
      o.rotation (π / 2 : ℝ) (r • o.rotation (π / 2 : ℝ) x) := by
    simp [← Real.Angle.coe_add]
  rw [sub_eq_add_neg, hx, o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x - r • o.rotation (π / 2 : ℝ) x) x = Real.arctan r := by
  rw [oangle_rev, sub_eq_add_neg, ← neg_smul, o.oangle_add_right_smul_rotation_pi_div_two h,
    Real.arctan_neg, Real.Angle.coe_neg, neg_neg]

end Orientation

namespace EuclideanGeometry

open Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

private theorem oangle_sub_right_vsub (p₁ p₂ p₃ : P) :
    o.oangle (p₃ -ᵥ p₂) (p₃ -ᵥ p₁) = ∡ p₂ p₃ p₁ := by
  rw [← o.oangle_neg_neg (p₃ -ᵥ p₂) (p₃ -ᵥ p₁), neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  rfl

private theorem oangle_sub_left_vsub (p₁ p₂ p₃ : P) :
    o.oangle (p₁ -ᵥ p₃) (p₁ -ᵥ p₂) = ∡ p₃ p₁ p₂ := by
  rw [← o.oangle_neg_neg (p₁ -ᵥ p₃) (p₁ -ᵥ p₂), neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  rfl

/-- The cosine of this angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_right_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.cos (∡ p₂ p₃ p₁) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_right_vsub] using o.cos_oangle_sub_right_pos hv

/-- The cosine of this angle in a positively oriented right triangle is positive. -/
theorem cos_oangle_left_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.cos (∡ p₃ p₁ p₂) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_left_vsub] using o.cos_oangle_sub_left_pos hv

/-- The sine of this angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_right_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.sin (∡ p₂ p₃ p₁) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_right_vsub] using o.sin_oangle_sub_right_pos hv

/-- The sine of this angle in a positively oriented right triangle is positive. -/
theorem sin_oangle_left_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.sin (∡ p₃ p₁ p₂) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_left_vsub] using o.sin_oangle_sub_left_pos hv

/-- The tangent of this angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_right_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.tan (∡ p₂ p₃ p₁) (cos_oangle_right_pos h).ne' := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_right_vsub] using o.tan_oangle_sub_right_pos hv

/-- The tangent of this angle in a positively oriented right triangle is positive. -/
theorem tan_oangle_left_pos {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    0 < Real.Angle.tan (∡ p₃ p₁ p₂) (cos_oangle_left_pos h).ne' := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [vsub_sub_vsub_cancel_right, oangle_sub_left_vsub] using o.tan_oangle_sub_left_pos hv

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arccos
      (Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two hv

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arccos
      (Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two hv

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arcsin
      (Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two hv

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arcsin
      (Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two hv

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arctan
      (Checked.div (dist p₁ p₂) (dist p₃ p₂)
        (dist_ne_zero.2 (right_ne_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two hv

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arctan
      (Checked.div (dist p₃ p₂) (dist p₁ p₂)
        (dist_ne_zero.2 (left_ne_of_oangle_eq_pi_div_two h)).isUnit) := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two hv

/-- An acute oriented angle in a right triangle has absolute value less than `π / 2`,
regardless of orientation. -/
lemma abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₃₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2 := by
  rw [← angle_eq_abs_oangle_toReal hp₃₂.symm (left_ne_right_of_angle_eq_pi_div_two h)]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h

/-- Two oriented angles in right-angled triangles are equal if twice those angles are equal. -/
lemma oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₃₂ : p₃ ≠ p₂} {hp₄₅ : p₄ ≠ p₅} {hp₆₅ : p₆ ≠ p₅}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₅ p₆ p₄)
    (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₅ p₆ p₄ := by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

/-- Two oriented angles in oppositely-oriented right-angled triangles are equal if twice those
angles are equal. -/
lemma oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₃₂ : p₃ ≠ p₂} {hp₄₅ : p₄ ≠ p₅} {hp₆₅ : p₆ ≠ p₅}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₄ p₆ p₅)
    (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₄ p₆ p₅ := by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev, Real.Angle.abs_toReal_neg]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) =
      Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.cos_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) =
      Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.cos_oangle_sub_left_of_oangle_eq_pi_div_two hv

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) =
      Checked.div (dist p₁ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.sin_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) =
      Checked.div (dist p₃ p₂) (dist p₁ p₃)
        (dist_ne_zero.2 (left_ne_right_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.sin_oangle_sub_left_of_oangle_eq_pi_div_two hv

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) (cos_oangle_right_pos h).ne' =
      Checked.div (dist p₁ p₂) (dist p₃ p₂)
        (dist_ne_zero.2 (right_ne_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.tan_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) (cos_oangle_left_pos h).ne' =
      Checked.div (dist p₃ p₂) (dist p₁ p₂)
        (dist_ne_zero.2 (left_ne_of_oangle_eq_pi_div_two h)).isUnit := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.tan_oangle_sub_left_of_oangle_eq_pi_div_two hv

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two hv

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two hv

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two hv

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two hv

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) (cos_oangle_right_pos h).ne' * dist p₃ p₂ = dist p₁ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two hv

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) (cos_oangle_left_pos h).ne' * dist p₁ p₂ = dist p₃ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₃ p₂) (Real.Angle.cos (∡ p₂ p₃ p₁))
      (cos_oangle_right_pos h).ne'.isUnit = dist p₁ p₃ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₁ p₂) (Real.Angle.cos (∡ p₃ p₁ p₂))
      (cos_oangle_left_pos h).ne'.isUnit = dist p₁ p₃ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₁ p₂) (Real.Angle.sin (∡ p₂ p₃ p₁))
      (sin_oangle_right_pos h).ne'.isUnit = dist p₁ p₃ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₃ p₂) (Real.Angle.sin (∡ p₃ p₁ p₂))
      (sin_oangle_left_pos h).ne'.isUnit = dist p₁ p₃ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₁ p₂) (Real.Angle.tan (∡ p₂ p₃ p₁) (cos_oangle_right_pos h).ne')
      (tan_oangle_right_pos h).ne'.isUnit = dist p₃ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_right_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two hv

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Checked.div (dist p₃ p₂) (Real.Angle.tan (∡ p₃ p₁ p₂) (cos_oangle_left_pos h).ne')
      (tan_oangle_left_pos h).ne'.isUnit = dist p₁ p₂ := by
  have hv : o.oangle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂) = ↑(π / 2) := h
  simpa only [oangle_sub_left_vsub, vsub_sub_vsub_cancel_right,
    ← dist_eq_norm_vsub V, dist_comm p₃ p₁] using
    o.norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two hv

end EuclideanGeometry

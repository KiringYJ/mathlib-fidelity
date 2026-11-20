/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle
* https://en.wikipedia.org/wiki/Law_of_sines

-/

public section

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Law of cosines** (cosine rule), vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring,
    cos_angle_mul_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, ←
    real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self,
    sub_add_eq_add_sub]

/-- **Law of sines** (sine rule), vector angle form. -/
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V)
    {hx : x ≠ 0} {hy : y ≠ 0} {hxy : x - y ≠ 0} :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by
  rw [sin_angle, sin_angle]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm x y]
  field_simp
  ring_nf

/-- A variant of the law of sines, (two given sides are nonzero), vector angle form. -/
theorem sin_angle_div_norm_eq_sin_angle_div_norm (x y : V)
    {hx : x ≠ 0} {hy : y ≠ 0} {hxy : x - y ≠ 0} :
    Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖ := by
  exact div_eq_div_iff.2 (sin_angle_mul_norm_eq_sin_angle_mul_norm x y)

/-- **Pons asinorum**, vector angle form. -/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V}
    {hx : x ≠ 0} {hxy : x ≠ y} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle, cos_angle]
  apply div_eq_div_iff.2
  simp only [norm_sub_rev y x, inner_sub_right, real_inner_self_eq_norm_mul_norm,
    h, real_inner_comm x y]

/-- **Converse of pons asinorum**, vector angle form. -/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hxy : x ≠ y}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ := by
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hxy)
  have hc := congrArg Real.cos h
  simp only [cos_angle, norm_sub_rev y x] at hc
  have hc' := div_eq_div_iff.mp hc
  have hinner : ‖y‖ * ⟪x, x - y⟫ = ‖x‖ * ⟪y, y - x⟫ := by
    apply mul_right_cancel₀ hd
    nlinarith only [hc']
  simp only [inner_sub_right, real_inner_self_eq_norm_mul_norm,
    real_inner_comm x y] at hinner
  have hprod : (‖x‖ - ‖y‖) * (‖x‖ * ‖y‖ + ⟪x, y⟫) = 0 := by
    linear_combination hinner
  rcases mul_eq_zero.mp hprod with heq | hinner
  · exact sub_eq_zero.mp heq
  · exact (hpi (inner_eq_neg_mul_norm_iff_angle_eq_pi.mp (by linarith))).elim

/-- Changing the second vector by equality preserves its angle with a fixed nonzero vector. -/
private theorem angle_congr_right {x y z : V} {hx : x ≠ 0} {hy : y ≠ 0} {hz : z ≠ 0}
    (h : y = z) : angle x y = angle x z := by
  subst z
  rfl

private theorem angle_congr {x y x' y' : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hx' : x' ≠ 0} {hy' : y' ≠ 0}
    (h₁ : x = x') (h₂ : y = y') : angle x y = angle x' y' := by
  subst x' y'
  rfl

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
private theorem cos_angle_eq_cos_angle_add_add_angle_add {x y : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hsum : x + y ≠ 0} :
    Real.cos (angle x y) = Real.cos (angle x (x + y) +
      angle y (y + x) hy (by simpa only [add_comm] using hsum)) := by
  have hyx : y + x ≠ 0 := by simpa only [add_comm] using hsum
  rw [Real.cos_add, cos_angle, cos_angle, cos_angle, sin_angle_add,
    sin_angle_add, mul_comm ⟪y, y⟫ ⟪x, x⟫, real_inner_comm x y]
  field_simp [norm_ne_zero_iff.2 hx, norm_ne_zero_iff.2 hy,
    norm_ne_zero_iff.2 hsum, norm_ne_zero_iff.2 hyx]
  rw [add_comm y x]
  have hs : 0 ≤ ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2 := by
    simpa only [sq] using sub_nonneg_of_le (real_inner_mul_inner_self_le x y)
  rw [Real.sq_sqrt hs]
  simp only [inner_add_right, real_inner_comm x y, real_inner_self_eq_norm_sq]
  ring_nf
  simp only [norm_add_sq_real]
  ring

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
private theorem sin_angle_eq_sin_angle_add_add_angle_add {x y : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hsum : x + y ≠ 0} :
    Real.sin (angle x y) = Real.sin (angle x (x + y) +
      angle y (y + x) hy (by simpa only [add_comm] using hsum)) := by
  have hyx : y + x ≠ 0 := by simpa only [add_comm] using hsum
  rw [Real.sin_add, cos_angle, cos_angle, sin_angle_add,
    sin_angle_add, sin_angle]
  field_simp [norm_ne_zero_iff.2 hx, norm_ne_zero_iff.2 hy,
    norm_ne_zero_iff.2 hsum, norm_ne_zero_iff.2 hyx]
  rw [add_comm y x, real_inner_comm x y]
  simp only [inner_add_right, real_inner_comm x y, real_inner_self_eq_norm_sq]
  ring_nf
  simp only [norm_add_sq_real]
  ring

/-- In a parallelogram, the two parts of the inner angle add to the inner angle,
vector angle form. -/
theorem angle_eq_angle_add_add_angle_add (x : V) {y : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hsum : x + y ≠ 0} :
    angle x y = angle x (x + y) + angle y (x + y) := by
  have h := Real.Angle.cos_sin_inj
    (cos_angle_eq_cos_angle_add_add_angle_add (x := x) (y := y) (hx := hx) (hy := hy)
      (hsum := hsum))
    (sin_angle_eq_sin_angle_add_add_angle_add (x := x) (y := y) (hx := hx) (hy := hy)
      (hsum := hsum))
  rw [angle_congr_right (hx := hy) (hz := hsum) (add_comm y x)] at h
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp h
  simp only at h
  have : -1 < n := by
    replace h := h.ge
    contrapose! h
    grw [h, neg_smul, one_smul, angle_le_pi, ← angle_nonneg, ← angle_nonneg]
    linear_combination Real.pi_pos
  have : n < 1 := by
    by_contra! hn
    have hsum_ge : 2 * π ≤ angle x (x + y) + angle y (x + y) := by
      have hh := h.le
      grw [← hn, one_smul, ← angle_nonneg x y, zero_add] at hh
      exact hh
    have hx_le := angle_le_pi x (x + y) (hx := hx) (hy := hsum)
    have hy_le := angle_le_pi y (x + y) (hx := hy) (hy := hsum)
    have h₁ : angle (x + y) x = π := by
      rw [angle_comm]
      linarith only [hsum_ge, hx_le, hy_le]
    have h₂ : angle (x + y) y = π := by
      rw [angle_comm]
      linarith only [hsum_ge, hx_le, hy_le]
    obtain ⟨-, r₁, hr₁_neg, hr₁⟩ := angle_eq_pi_iff.mp h₁
    obtain ⟨-, r₂, hr₂_neg, hr₂⟩ := angle_eq_pi_iff.mp h₂
    have : (r₁ + r₂ - 1) • (x + y) = 0 := by
      rw [sub_smul, add_smul, one_smul, ← hr₁, ← hr₂, sub_eq_zero]
    cases smul_eq_zero.1 this
    · linarith
    · contradiction
  obtain rfl : n = 0 := by lia
  simpa using h

/-- The sum of the angles of a possibly degenerate triangle (where one of the
two given sides is nonzero), vector angle form. -/
theorem angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V}
    {hx : x ≠ 0} {hy : y ≠ 0} {hxy : x - y ≠ 0} :
    angle x y + angle x (x - y) +
      angle y (y - x) hy (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hxy))) = π := by
  have h := angle_eq_angle_add_add_angle_add (x - y) (y := y)
    (hx := hxy) (hy := hy) (hsum := by simpa only [sub_add_cancel] using hx)
  rw [angle_congr_right (hx := hxy) (hz := hx) (sub_add_cancel x y),
    angle_congr_right (hx := hy) (hz := hx) (sub_add_cancel x y),
    angle_comm (x - y) y, angle_comm (x - y) x, angle_comm y x] at h
  rw [angle_congr_right (hx := hy) (hz := neg_ne_zero.mpr hxy) (neg_sub x y).symm,
    angle_neg_right y (x - y) (hx := hy) (hy := hxy)]
  linarith

end InnerProductGeometry

namespace Orientation

open Module InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
variable (o : Orientation ℝ V (Fin 2))

/-- **Converse of pons asinorum**, oriented vector angle form (given equality of angles mod `π`). -/
theorem norm_eq_of_two_zsmul_oangle_sub_eq {x y : V}
    (h : (2 : ℤ) • o.oangle x (x - y) = (2 : ℤ) • o.oangle (y - x) y) (h0 : o.oangle x y ≠ 0)
    (hpi : o.oangle x y ≠ π) : ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x - y)).sign = (o.oangle (y - x) y).sign := by simp
  rw [Real.Angle.two_zsmul_eq_iff] at h
  rcases h with h | h
  · rw [← o.angle_eq_iff_oangle_eq_of_sign_eq (o.left_ne_zero_of_oangle_ne_zero h0)
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0))
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0).symm)
      (o.right_ne_zero_of_oangle_ne_zero h0) hs, angle_comm (y - x)] at h
    refine norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
      (hxy := o.ne_of_oangle_ne_zero h0) h ?_
    rw [ne_eq, ← o.oangle_eq_pi_iff_angle_eq_pi]
    exact hpi
  · rw [h, Real.Angle.sign_add_pi, SignType.neg_eq_self_iff, oangle_sign_sub_left_swap,
      o.oangle_rev, Real.Angle.sign_neg, SignType.neg_eq_zero_iff,
      Real.Angle.sign_eq_zero_iff] at hs
    simp [h0, hpi] at hs

end Orientation

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P)
    {hp₁ : p₁ ≠ p₂} {hp₃ : p₃ ≠ p₂} :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by
  rw [dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  rw [← vsub_sub_vsub_cancel_right p₁ p₃ p₂]
  exact norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V) (hx := vsub_ne_zero.2 hp₁) (hy := vsub_ne_zero.2 hp₃)

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

/-- **Law of sines** (sine rule), angle-at-point form. -/
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P)
    {hp₁₂ : p₁ ≠ p₂} {hp₃₂ : p₃ ≠ p₂} {hp₃₁ : p₃ ≠ p₁} :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by
  let x : V := p₃ -ᵥ p₂
  let y : V := p₁ -ᵥ p₂
  have hx : x ≠ 0 := vsub_ne_zero.2 hp₃₂
  have hy : y ≠ 0 := vsub_ne_zero.2 hp₁₂
  have hxy : x - y = p₃ -ᵥ p₁ := vsub_sub_vsub_cancel_right ..
  have hd : x - y ≠ 0 := hxy.symm ▸ vsub_ne_zero.2 hp₃₁
  have hn : -y = p₂ -ᵥ p₁ := neg_vsub_eq_vsub_rev ..
  have ha : InnerProductGeometry.angle y (x - y) hy hd = π - ∠ p₃ p₁ p₂ := calc
    _ = InnerProductGeometry.angle (x - y) y hd hy := InnerProductGeometry.angle_comm ..
    _ = π - InnerProductGeometry.angle (x - y) (-y) hd (neg_ne_zero.mpr hy) := by
      rw [angle_neg_right (x - y) y (hx := hd) (hy := hy)]
      ring
    _ = _ := by
      unfold angle
      congr 1
      exact InnerProductGeometry.angle_congr hxy hn
  have h := sin_angle_mul_norm_eq_sin_angle_mul_norm x y (hx := hx) (hy := hy) (hxy := hd)
  rw [ha, Real.sin_pi_sub, hxy, InnerProductGeometry.angle_comm x y] at h
  rw [dist_comm p₂ p₃, dist_eq_norm_vsub V p₃ p₂, dist_eq_norm_vsub V p₃ p₁]
  exact h

alias law_sin := sin_angle_mul_dist_eq_sin_angle_mul_dist

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- A variant of the law of sines, angle-at-point form. -/
theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} {h12 : p₁ ≠ p₂}
    (h23 : p₂ ≠ p₃) (h31 : p₃ ≠ p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by
  exact div_eq_div_iff.2 (law_sin p₁ p₂ p₃ (hp₁₂ := h12) (hp₃₂ := h23.symm) (hp₃₁ := h31))

/-- A variant of the law of sines, requiring that the points not be collinear. -/
theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = Checked.div
      (dist p₃ p₁ * Real.sin (angle p₂ p₃ p₁ (ne₂₃_of_not_collinear h) (ne₁₃_of_not_collinear h)))
      (Real.sin (angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm))
      (sin_pos_of_not_collinear h).ne'.isUnit := by
  have h₁₂ := ne₁₂_of_not_collinear h
  have h₁₃ := ne₁₃_of_not_collinear h
  have h₂₃ := ne₂₃_of_not_collinear h
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  apply (eq_div_iff (hb := sin_gt_zero.ne'.isUnit)).2
  simpa only [mul_comm, dist_comm p₂ p₁, dist_comm p₁ p₃,
    EuclideanGeometry.angle_comm p₃ p₂ p₁, EuclideanGeometry.angle_comm p₁ p₃ p₂] using
    law_sin p₃ p₂ p₁ (hp₁₂ := h₂₃.symm) (hp₃₂ := h₁₂) (hp₃₁ := h₁₃)

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  let x : V := p₁ -ᵥ p₂
  let y : V := p₁ -ᵥ p₃
  have hd : x - y = p₃ -ᵥ p₂ := vsub_sub_vsub_cancel_left ..
  have hxy : x ≠ y := sub_ne_zero.1 (hd.symm ▸ vsub_ne_zero.2 hp₂₃.symm)
  have ha := angle_sub_eq_angle_sub_rev_of_norm_eq (hx := vsub_ne_zero.2 hp₁₂) (hxy := hxy) h
  rw [angle_congr_right (hx := vsub_ne_zero.2 hp₁₂) (hz := vsub_ne_zero.2 hp₂₃.symm)
      (vsub_sub_vsub_cancel_left p₃ p₂ p₁),
    angle_congr_right (hx := vsub_ne_zero.2 hp₁₃) (hz := vsub_ne_zero.2 hp₂₃)
      (vsub_sub_vsub_cancel_left p₂ p₃ p₁)] at ha
  exact ha

/-- Converse of pons asinorum, angle-at-point form. -/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm = angle p₁ p₃ p₂ hp₁₃ hp₂₃)
    (hpi : angle p₂ p₁ p₃ hp₁₂.symm hp₁₃.symm ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  let x : V := p₁ -ᵥ p₂
  let y : V := p₁ -ᵥ p₃
  have hx : x ≠ 0 := vsub_ne_zero.2 hp₁₂
  have hy : y ≠ 0 := vsub_ne_zero.2 hp₁₃
  have hd : x - y = p₃ -ᵥ p₂ := vsub_sub_vsub_cancel_left ..
  have hd' : y - x = p₂ -ᵥ p₃ := vsub_sub_vsub_cancel_left ..
  have hxy : x ≠ y := sub_ne_zero.1 (hd.symm ▸ vsub_ne_zero.2 hp₂₃.symm)
  have hangle : InnerProductGeometry.angle x (x - y) hx (sub_ne_zero.2 hxy) =
      InnerProductGeometry.angle y (y - x) hy (sub_ne_zero.2 hxy.symm) := by
    rw [angle_congr_right (hx := hx) (hz := vsub_ne_zero.2 hp₂₃.symm) hd,
      angle_congr_right (hx := hy) (hz := vsub_ne_zero.2 hp₂₃) hd']
    exact h
  have hα : InnerProductGeometry.angle x y hx hy = angle p₂ p₁ p₃ hp₁₂.symm hp₁₃.symm :=
    (angle_neg_neg x y (hx := hx) (hy := hy)).symm.trans
      (InnerProductGeometry.angle_congr (neg_vsub_eq_vsub_rev ..) (neg_vsub_eq_vsub_rev ..))
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃]
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi (hxy := hxy) hangle
    (fun hπ ↦ hpi (hα.symm.trans hπ))

/-- Converse of pons asinorum, oriented angle-at-point form (given equality of angles mod `π`). -/
theorem dist_eq_of_two_zsmul_oangle_eq [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₂ p₃ p₁)
    (h0 : ∡ p₃ p₁ p₂ ≠ 0) (hpi : ∡ p₃ p₁ p₂ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  convert!
    (Orientation.norm_eq_of_two_zsmul_oangle_sub_eq (x := p₃ -ᵥ p₁) (y := p₂ -ᵥ p₁) ?_ ?_ h0
        hpi).symm
  · rw [dist_eq_norm_vsub']
  · rw [dist_eq_norm_vsub']
  · rw [eq_comm, o.oangle_rev, ← o.oangle_neg_neg]
    nth_rw 2 [o.oangle_rev, ← o.oangle_neg_neg]
    simp_rw [smul_neg, neg_inj]
    simp_rw [oangle] at h
    convert! h <;> simp

/-- The **sum of the angles of a triangle** with distinct vertices, angle-at-point. -/
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁)
    {hp₃₁ : p₃ ≠ p₁} {hp₃₂ : p₃ ≠ p₂} :
    angle p₁ p₂ p₃ h.symm hp₃₂ + angle p₂ p₃ p₁ hp₃₂.symm hp₃₁.symm +
      angle p₃ p₁ p₂ hp₃₁ h = π := by
  let x : V := p₃ -ᵥ p₁
  let y : V := p₂ -ᵥ p₁
  have hx : x ≠ 0 := vsub_ne_zero.2 hp₃₁
  have hy : y ≠ 0 := vsub_ne_zero.2 h
  have hxy : x - y = p₃ -ᵥ p₂ := vsub_sub_vsub_cancel_right ..
  have hyx : y - x = p₂ -ᵥ p₃ := vsub_sub_vsub_cancel_right ..
  have hd : x - y ≠ 0 := hxy.symm ▸ vsub_ne_zero.2 hp₃₂
  have hd' : y - x ≠ 0 := hyx.symm ▸ vsub_ne_zero.2 hp₃₂.symm
  have h₁ : InnerProductGeometry.angle x y hx hy = angle p₃ p₁ p₂ hp₃₁ h := rfl
  have h₂ : InnerProductGeometry.angle x (x - y) hx hd = angle p₂ p₃ p₁ hp₃₂.symm hp₃₁.symm := by
    rw [EuclideanGeometry.angle_comm p₂ p₃ p₁]
    exact (angle_neg_neg x (x - y) (hx := hx) (hy := hd)).symm.trans
      (InnerProductGeometry.angle_congr (neg_vsub_eq_vsub_rev ..)
        ((congrArg Neg.neg hxy).trans (neg_vsub_eq_vsub_rev ..)))
  have h₃ : InnerProductGeometry.angle y (y - x) hy hd' = angle p₁ p₂ p₃ h.symm hp₃₂ :=
    (angle_neg_neg y (y - x) (hx := hy) (hy := hd')).symm.trans
      (InnerProductGeometry.angle_congr (neg_vsub_eq_vsub_rev ..)
        ((congrArg Neg.neg hyx).trans (neg_vsub_eq_vsub_rev ..)))
  have hsum := angle_add_angle_sub_add_angle_sub_eq_pi x (y := y)
    (hx := hx) (hy := hy) (hxy := hd)
  rw [h₁, h₂, h₃] at hsum
  linarith only [hsum]

/-- The **Exterior angle theorem**. an exterior angle of a triangle is equal to the sum of the
measures of the remote interior angles. -/
theorem exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂)
    {hp₃₁ : p₃ ≠ p₁} {hp₃₂ : p₃ ≠ p₂} :
    angle p₃ p₁ p hp₃₁ h.ne_left.symm =
      angle p₁ p₃ p₂ hp₃₁.symm hp₃₂.symm + angle p₃ p₂ p₁ hp₃₂ h.ne_right := by
  have hsum := angle_add_angle_add_angle_eq_pi p₃ h.right_ne (hp₃₁ := hp₃₁) (hp₃₂ := hp₃₂)
  rw [EuclideanGeometry.angle_comm p₁ p₂ p₃, EuclideanGeometry.angle_comm p₂ p₃ p₁] at hsum
  linarith only [hsum, angle_add_angle_eq_pi_of_angle_eq_pi p₃ (hp₁p₃ := hp₃₁) h.angle₁₂₃_eq_pi]

/-- The **sum of the angles of a triangle** (possibly degenerate, where the triangle is a line),
oriented angles at point. -/
theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ ≠ p₁) (h32 : p₃ ≠ p₂)
    (h13 : p₁ ≠ p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by
  simpa only [neg_vsub_eq_vsub_rev] using!
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

/-- Given a triangle `ABC` with `A ≠ B` and `A ≠ C` and a point `P` on `BC`,
`∠ B A P + ∠ P A C = ∠ B A C`. -/
lemma angle_add_of_ne_of_ne {a b c p : P} (hb : a ≠ b) (hc : a ≠ c) {hpa : p ≠ a}
    (hp : Wbtw ℝ b p c) :
    angle b a p hb.symm hpa + angle p a c hpa hc.symm = angle b a c hb.symm hc.symm := by
  rcases eq_or_ne p b with rfl | pb
  · rw [angle_self_of_ne (h := hb.symm), zero_add]
  rcases eq_or_ne p c with rfl | pc
  · rw [angle_self_of_ne (h := hc.symm), add_zero]
  have hcb : c ≠ b := by
    rintro rfl
    exact pb ((wbtw_self_iff ℝ).1 hp)
  have ea := angle_add_angle_add_angle_eq_pi c hb (hp₃₁ := hcb) (hp₃₂ := hc.symm)
  have eb := angle_add_angle_add_angle_eq_pi p hb (hp₃₁ := pb) (hp₃₂ := hpa)
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm (hp₃₁ := hpa) (hp₃₂ := pc)
  have hπ : angle b p c pb.symm pc.symm = π := angle_eq_pi_iff_sbtw.mpr ⟨hp, pb, pc⟩
  have hπ' : angle c p b pc.symm pb.symm = π := (angle_comm c p b).trans hπ
  rw [angle_comm p b a, angle_eq_angle_of_angle_eq_pi a (hp₁p₂ := hb) hπ,
    angle_comm a b c] at eb
  rw [angle_eq_angle_of_angle_eq_pi a (hp₁p₂ := hc) hπ', angle_comm c p a] at ec
  have ep := angle_add_angle_eq_pi_of_angle_eq_pi a (hp₁p₃ := hpa.symm) hπ
  linarith only [ea, eb, ec, ep]

/-- If `X` lies strictly between `A` and `C`, then `∠ A P X + ∠ X P C = ∠ A P C`
whenever the angles at `P` are defined. -/
lemma angle_add_angle_eq_of_sbtw {a c p x : P} (hx : Sbtw ℝ a x c)
    {hap : a ≠ p} {hcp : c ≠ p} {hxp : x ≠ p} :
    ∠ a p x + ∠ x p c = ∠ a p c := by
  exact angle_add_of_ne_of_ne hap.symm hcp.symm (hpa := hxp) hx.wbtw

/-- If `B` lies on the same ray from `P` as a point `X` strictly between `A` and `C`,
then `∠ A P B + ∠ B P C = ∠ A P C`. -/
theorem angle_add_angle_eq_of_sbtw_of_sameRay {a b c p x : P}
    (hx : Sbtw ℝ a x c) (hxb : SameRay ℝ (x -ᵥ p) (b -ᵥ p)) (hb : b ≠ p)
    {hap : a ≠ p} {hcp : c ≠ p} :
    ∠ a p b + ∠ b p c = ∠ a p c := by
  rcases eq_or_ne p x with rfl | hpx
  · have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi, angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  have hxp := hpx.symm
  obtain ⟨r, hr, hrb⟩ :=
    (exists_pos_left_iff_sameRay (vsub_ne_zero.2 hxp) (vsub_ne_zero.2 hb)).2 hxb
  have hab : ∠ a p b = ∠ a p x := angle_smul_right_of_pos a hr hrb
  have hbc : ∠ b p c = ∠ x p c := angle_smul_left_of_pos c hr hrb
  rw [hab, hbc]
  exact angle_add_angle_eq_of_sbtw hx (hap := hap) (hcp := hcp) (hxp := hxp)

/-- **Stewart's Theorem**. -/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) {hbp : b ≠ p} {hcp : c ≠ p}
    (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  by_cases hap : a = p
  · subst a
    rw [dist_self, zero_pow two_ne_zero, zero_add, dist_eq_add_dist_of_angle_eq_pi h]
    simp only [dist_comm p b, dist_comm p c]
    ring
  rw [pow_two, pow_two, law_cos a p b (hp₁ := hap) (hp₃ := hbp),
    law_cos a p c (hp₁ := hap) (hp₃ := hcp),
    eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a (hp₁p₃ := hap) h), Real.cos_pi_sub,
    dist_eq_add_dist_of_angle_eq_pi h]
  ring

/-- **Apollonius's Theorem**. -/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint ℝ b c
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm
    calc
      dist a b ^ 2 + dist a c ^ 2 = 2 / dist b c * (dist a b ^ 2 *
        ((2 : ℝ)⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) := by
        field
      _ = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        field

theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ)
    {hab₀ : a ≠ b} {hcb₀ : c ≠ b} {hab₀' : a' ≠ b'} {hcb₀' : c' ≠ b'}
    (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c' (hp₁ := hab₀') (hp₃ := hcb₀')]
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h, hab, hcb]; ring
    _ = (r * dist a c) ^ 2 := by
      simp [pow_two, ← law_cos a b c (hp₁ := hab₀) (hp₃ := hcb₀)]
      ring
  have h1 : 0 ≤ r * dist a b := hab ▸ dist_nonneg
  have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₀)
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

/-- In a triangle, the smaller angle is opposite the smaller side. -/
theorem dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    angle a c b (ne₁₃_of_not_collinear h) (ne₂₃_of_not_collinear h) <
      angle a b c (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm →
      dist a b < dist a c := by
  have hab := ne₁₂_of_not_collinear h
  have hac' := ne₁₃_of_not_collinear h
  have hbc := ne₂₃_of_not_collinear h
  let α := angle a b c hab hbc.symm
  let β := angle a c b hac' hbc
  change β < α → _
  have hsin := law_sin c b a (hp₁₂ := hbc.symm) (hp₃₂ := hab) (hp₃₁ := hac')
  rw [dist_comm b a, angle_comm c b a] at hsin
  change Real.sin α * dist a b = Real.sin β * dist a c at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hnonneg : 0 ≤ β := angle_nonneg a c b
  have hsinabc : Real.sin α ≥ 0 :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg a b c) (angle_le_pi a b c)
  intro h1
  by_cases! h2 : α ≤ π / 2
  · have h3 : Real.sin β < Real.sin α := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hnonneg, Real.pi_pos]) h2 h1
    by_contra! w
    have h4 : Real.sin β * dist a c < Real.sin α * dist a b := by
      exact mul_lt_mul h3 w hac hsinabc
    linarith
  · by_contra! w
    have h3 : Real.sin α ≤ Real.sin β := by
      by_contra! w1
      have h4 : Real.sin β * dist a c < Real.sin α * dist a b := by
        exact mul_lt_mul w1 w hac hsinabc
      linarith
    rw [← Real.sin_pi_sub α] at h3
    have h5 : π - α < π / 2 := by linarith
    have h6 : π - α ≤ β := by
      by_contra! w1
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hnonneg, Real.pi_pos])
        h5.le w1
      linarith
    have h7 := angle_add_angle_add_angle_eq_pi c hab.symm (hp₃₁ := hac'.symm) (hp₃₂ := hbc.symm)
    rw [angle_comm b c a] at h7
    change α + β + angle c a b hac'.symm hab.symm = π at h7
    have h8 : 0 < angle c a b hac'.symm hab.symm := by
      rw [angle_comm]
      exact angle_pos_of_not_collinear ((Set.insert_comm a b {c}) ▸ h)
    linarith

theorem angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    angle a c b (ne₁₃_of_not_collinear h) (ne₂₃_of_not_collinear h) <
      angle a b c (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm ↔
      dist a b < dist a c := by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        exact (angle_lt_pi_of_not_collinear ((Set.insert_comm a b {c}) ▸ h)).ne
      linarith
    · have h' : ¬Collinear ℝ ({a, c, b} : Set P) :=
        (congrArg (insert a) (Set.pair_comm b c)) ▸ h
      have h5 := dist_lt_of_angle_lt h' h3
      linarith

theorem angle_le_iff_dist_le {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    angle a c b (ne₁₃_of_not_collinear h) (ne₂₃_of_not_collinear h) ≤
      angle a b c (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm ↔
      dist a b ≤ dist a c := by
  have h' : ¬Collinear ℝ ({a, c, b} : Set P) :=
    (congrArg (insert a) (Set.pair_comm b c)) ▸ h
  simpa only [not_lt] using (angle_lt_iff_dist_lt h').not

/-- The greatest angle of a triangle with distinct vertices is at least `π / 3`. -/
lemma pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h₂₃₁ : angle p₂ p₃ p₁ hp₂₃ hp₁₃ ≤ angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm)
    (h₃₁₂ : angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm ≤ angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm) :
    π / 3 ≤ angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm := by
  linarith [angle_add_angle_add_angle_eq_pi p₃ hp₁₂.symm (hp₃₁ := hp₁₃.symm) (hp₃₂ := hp₂₃.symm)]

/-- The greatest angle of a triangle with distinct vertices is more than `π / 3`, unless all angles
are equal. -/
lemma pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h₂₃₁ : angle p₂ p₃ p₁ hp₂₃ hp₁₃ ≤ angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm)
    (h₃₁₂ : angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm ≤ angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm)
    (hne : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≠ angle p₂ p₃ p₁ hp₂₃ hp₁₃ ∨
      angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≠ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm ∨
      angle p₂ p₃ p₁ hp₂₃ hp₁₃ ≠ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm) :
    π / 3 < angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm := by
  have hsum := angle_add_angle_add_angle_eq_pi p₃ hp₁₂.symm (hp₃₁ := hp₁₃.symm) (hp₃₂ := hp₂₃.symm)
  rcases hne with hne | hne | hne <;> rcases hne.lt_or_gt with hne | hne <;> linarith

/-- The least angle of a triangle with distinct vertices is at most `π / 3`. -/
lemma angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h₂₃₁ : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≤ angle p₂ p₃ p₁ hp₂₃ hp₁₃)
    (h₃₁₂ : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≤ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm) :
    angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≤ π / 3 := by
  linarith [angle_add_angle_add_angle_eq_pi p₃ hp₁₂.symm (hp₃₁ := hp₁₃.symm) (hp₃₂ := hp₂₃.symm)]

/-- The least angle of a triangle with distinct vertices is less than `π / 3`, unless all angles are
equal. -/
lemma angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P}
    {hp₁₂ : p₁ ≠ p₂} {hp₁₃ : p₁ ≠ p₃} {hp₂₃ : p₂ ≠ p₃}
    (h₂₃₁ : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≤ angle p₂ p₃ p₁ hp₂₃ hp₁₃)
    (h₃₁₂ : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≤ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm)
    (hne : angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≠ angle p₂ p₃ p₁ hp₂₃ hp₁₃ ∨
      angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm ≠ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm ∨
      angle p₂ p₃ p₁ hp₂₃ hp₁₃ ≠ angle p₃ p₁ p₂ hp₁₃.symm hp₁₂.symm) :
    angle p₁ p₂ p₃ hp₁₂ hp₂₃.symm < π / 3 := by
  have hsum := angle_add_angle_add_angle_eq_pi p₃ hp₁₂.symm (hp₃₁ := hp₁₃.symm) (hp₃₂ := hp₂₃.symm)
  rcases hne with hne | hne | hne <;> rcases hne.lt_or_gt with hne | hne <;> linarith

end EuclideanGeometry

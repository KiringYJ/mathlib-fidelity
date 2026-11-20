/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

/-!
# Poles and polars

This file defines poles and polars for spheres in Euclidean spaces.

## Main definitions

* `EuclideanGeometry.Sphere.pole`: the inversion in the sphere of the point in an affine subspace
  closest to the center. It is defined for subspaces that do not contain the center.

* `EuclideanGeometry.Sphere.polar`: the affine subspace orthogonal to the radius vector at a point
  and passing through its inversion in the sphere. It is defined away from the center.

## Main theorems

* `EuclideanGeometry.Sphere.mem_polar_iff_mem_polar`: La Hire's theorem.

-/

@[expose] public noncomputable section

namespace EuclideanGeometry

namespace Sphere

open AffineSubspace Function
open scoped RealInnerProductSpace

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The pole of an affine subspace is the inversion in the sphere of the point in that subspace
closest to the center. -/
def pole (s : Sphere P) (as : AffineSubspace ℝ P) [Nonempty as]
    [as.direction.HasOrthogonalProjection] (has : s.center ∉ as := by aesop) : P :=
  inversion s.center s.radius (orthogonalProjection as s.center)
    (orthogonalProjection_eq_self_iff.not.2 has)

/-- The polar of a point is the affine subspace orthogonal to the radius vector at that point
and passing through its inversion in the sphere. -/
def polar (s : Sphere P) (p : P) (hp : p ≠ s.center := by aesop) : AffineSubspace ℝ P :=
  s.orthRadius (inversion s.center s.radius p hp)

instance (s : Sphere P) (p : P) {hp : p ≠ s.center} :
    (s.polar p hp).direction.HasOrthogonalProjection := by
  rw [polar]
  infer_instance

instance (s : Sphere P) (p : P) {hp : p ≠ s.center} : Nonempty (s.polar p hp) := by
  rw [polar]
  infer_instance

@[simp] lemma direction_polar {s : Sphere P} (hs : s.radius ≠ 0) (p : P) {hp : p ≠ s.center} :
    (s.polar p hp).direction = (ℝ ∙ (p -ᵥ s.center))ᗮ := by
  rw [polar, direction_orthRadius, inversion_vsub_center,
    Submodule.orthogonalComplement_eq_orthogonalComplement]
  exact Submodule.span_singleton_smul_eq (pow_ne_zero 2 (div_ne_zero hs)).isUnit _

@[simp] lemma center_mem_polar_iff {s : Sphere P} {p : P} {hp : p ≠ s.center} :
    s.center ∈ s.polar p hp ↔ s.radius = 0 := by
  rw [polar, center_mem_orthRadius_iff, inversion_eq_center]

@[simp] lemma pole_polar {s : Sphere P} (hs : s.radius ≠ 0) (p : P) {hp : p ≠ s.center} :
    s.pole (s.polar p hp) (center_mem_polar_iff.not.2 hs) = p := by
  simp! [pole, polar, hs]

lemma orthRadius_eq_polar_inversion {s : Sphere P} (hs : s.radius ≠ 0) (p : P)
    {hp : p ≠ s.center} :
    s.orthRadius p = s.polar (inversion s.center s.radius p hp)
      (inversion_ne_center (hx := hp) hs) := by
  simp [polar, hs]

theorem pole_ne_center {s : Sphere P} {as : AffineSubspace ℝ P} [Nonempty as]
    [as.direction.HasOrthogonalProjection] {hp : s.center ∉ as} (hs : s.radius ≠ 0) :
    s.pole as hp ≠ s.center :=
  inversion_ne_center (hx := orthogonalProjection_eq_self_iff.not.2 hp) hs

@[simp] lemma polar_pole_orthRadius {s : Sphere P} (hs : s.radius ≠ 0) (p : P)
    {hp : p ≠ s.center} :
    s.polar (s.pole (s.orthRadius p) (center_mem_orthRadius_iff.not.2 hp))
      (pole_ne_center hs) = s.orthRadius p := by
  simp [polar, pole, hs]

@[simp] lemma polar_zero_radius {s : Sphere P} (hs : s.radius = 0) (p : P)
    {hp : p ≠ s.center} : s.polar p hp = ⊤ := by
  simp [polar, hs]

@[simp] lemma polar_eq_orthRadius_self_iff {s : Sphere P} (hs : 0 ≤ s.radius) {p : P}
    {hp : p ≠ s.center} : s.polar p hp = s.orthRadius p ↔ p ∈ s := by
  have hd : 0 < dist p s.center := dist_pos.2 hp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have he := orthRadius_eq_orthRadius_iff.mp h
    have hd' := congrArg (dist · s.center) he
    rw [dist_inversion_center, div_eq_iff] at hd'
    have heq : s.radius = dist p s.center := by nlinarith
    exact heq.symm
  · rw [polar, inversion_of_mem_sphere h]

lemma mem_polar_iff_inner {s : Sphere P} {p₁ p₂ : P} {hp₂ : p₂ ≠ s.center} :
    p₁ ∈ s.polar p₂ hp₂ ↔
      s.radius = 0 ∨ ⟪p₁ -ᵥ s.center, p₂ -ᵥ s.center⟫ = s.radius ^ 2 := by
  by_cases hr : s.radius = 0
  · simp [hr]
  have hd : dist p₂ s.center ≠ 0 := dist_ne_zero.2 hp₂
  simp only [hr, false_or]
  simp_rw [polar, mem_orthRadius_iff_inner_left, inversion_vsub_center, inversion,
    vsub_vadd_eq_vsub_sub, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub]
  rw [← mul_eq_zero_iff_left (a := (dist p₂ s.center) ^ 2 / s.radius ^ 2)
    (div_ne_zero (pow_ne_zero 2 hd))]
  nth_rw 2 [← sub_eq_zero]
  convert Iff.rfl using 2
  field [dist_ne_zero.2 hp₂]

/-- **La Hire's theorem**: `p₁` lies on the polar of `p₂` if and only if `p₂` lies on the polar of
`p₁`. -/
theorem mem_polar_iff_mem_polar {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ≠ s.center)
    (hp₂ : p₂ ≠ s.center) : p₁ ∈ s.polar p₂ hp₂ ↔ p₂ ∈ s.polar p₁ hp₁ := by
  simp [mem_polar_iff_inner, real_inner_comm]

lemma mem_orthRadius_iff_mem_polar_of_mem {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ≠ s.center)
    (hp₂ : p₂ ∈ s) : p₁ ∈ s.orthRadius p₂ ↔ p₂ ∈ s.polar p₁ hp₁ := by
  by_cases hr : s.radius = 0
  · rw [mem_sphere, hr, dist_eq_zero] at hp₂
    simp [hr, hp₂]
  have hp₂' : p₂ ≠ s.center := by
    rintro rfl
    rw [mem_sphere, dist_self] at hp₂
    exact hr hp₂.symm
  rw [← (polar_eq_orthRadius_self_iff (hp := hp₂') (radius_nonneg_of_mem hp₂)).2 hp₂]
  exact mem_polar_iff_mem_polar hp₁ hp₂'

lemma mem_polar_of_mem_of_mem_orthRadius {s : Sphere P} {p₁ p₂ : P} {hp₁ : p₁ ≠ s.center}
    (hp₂ : p₂ ∈ s) (h : p₁ ∈ s.orthRadius p₂) : p₂ ∈ s.polar p₁ hp₁ :=
  (mem_orthRadius_iff_mem_polar_of_mem hp₁ hp₂).1 h

lemma ncard_inter_polar_eq_two_of_radius_lt_dist [Fact (Module.finrank ℝ V = 2)] {s : Sphere P}
    (hs : 0 < s.radius) {p : P} (hp : s.radius < dist p s.center) :
    (s ∩ s.polar p (dist_pos.1 (hs.trans hp)) : Set P).ncard = 2 := by
  refine ncard_inter_orthRadius_eq_two_of_dist_lt_radius ?_ ?_
  · simpa [dist_inversion_center, div_lt_iff₀ (hs.trans hp), pow_two, hs]
  · exact inversion_ne_center hs.ne'

end Sphere

end EuclideanGeometry

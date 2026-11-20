/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Image of a hyperplane under inversion

In this file we prove that the inversion with center `c` and radius `R ≠ 0` maps a sphere passing
through the center to a hyperplane, and vice versa. More precisely, it maps a sphere with center
`y ≠ c` and radius `dist y c` to the hyperplane
`AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R y)`.

The set equalities are on the complement of the center. Inversion also preserves the punctured
affine subspaces through the center.

## Keywords

inversion
-/

public section

open Metric AffineMap Set AffineSubspace
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {c x y : P} {R : ℝ}

namespace EuclideanGeometry

/-- The inversion with center `c` and radius `R` maps a sphere passing through the center to a
hyperplane. -/
theorem inversion_mem_perpBisector_inversion_iff (hR : R ≠ 0) (hx : x ≠ c) (hy : y ≠ c) :
    inversion c R x hx ∈ perpBisector c (inversion c R y hy) ↔ dist x y = dist y c := by
  have hdx : dist x c ≠ 0 := dist_ne_zero.2 hx
  have hdy : dist y c ≠ 0 := dist_ne_zero.2 hy
  rw [mem_perpBisector_iff_dist_eq, dist_inversion_inversion hx hy, dist_inversion_center]
  rw [div_mul_eq_mul_div₀, div_eq_div_iff]
  rw [show R ^ 2 * (dist x c * dist y c) =
    (R ^ 2 * dist y c) * dist x c by ring, mul_left_inj' hdx,
    mul_right_inj' (pow_ne_zero 2 hR)]
  exact eq_comm

theorem preimage_inversion_perpBisector_inversion (hR : R ≠ 0) (hy : y ≠ c) :
    inversionEquiv c hR ⁻¹' (Subtype.val ⁻¹' (perpBisector c (inversion c R y hy) : Set P)) =
      Subtype.val ⁻¹' sphere y (dist y c) :=
  Set.ext fun x ↦ inversion_mem_perpBisector_inversion_iff hR x.2 hy

theorem preimage_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversionEquiv c hR ⁻¹' (Subtype.val ⁻¹' (perpBisector c y : Set P)) =
      Subtype.val ⁻¹' sphere (inversion c R y hy) (R ^ 2 / dist y c) := by
  rw [← dist_inversion_center c y R (hx := hy),
    ← preimage_inversion_perpBisector_inversion hR (inversion_ne_center (hx := hy) hR),
    inversion_inversion c hR y (hx := hy)]

theorem image_inversion_perpBisector (hR : R ≠ 0) (hy : y ≠ c) :
    inversionEquiv c hR '' (Subtype.val ⁻¹' (perpBisector c y : Set P)) =
      Subtype.val ⁻¹' sphere (inversion c R y hy) (R ^ 2 / dist y c) := by
  rw [Equiv.image_eq_preimage_symm, inversionEquiv_symm, preimage_inversion_perpBisector hR hy]

theorem preimage_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversionEquiv c hR ⁻¹' (Subtype.val ⁻¹' sphere y (dist y c)) =
      Subtype.val ⁻¹' (perpBisector c (inversion c R y hy) : Set P) := by
  rw [← preimage_inversion_perpBisector_inversion hR hy, ← preimage_comp]
  simp only [(inversion_involutive c hR).comp_self, preimage_id]

theorem image_inversion_sphere_dist_center (hR : R ≠ 0) (hy : y ≠ c) :
    inversionEquiv c hR '' (Subtype.val ⁻¹' sphere y (dist y c)) =
      Subtype.val ⁻¹' (perpBisector c (inversion c R y hy) : Set P) := by
  rw [Equiv.image_eq_preimage_symm, inversionEquiv_symm,
    preimage_inversion_sphere_dist_center hR hy]

/-- Inversion maps the punctured part of an affine subspace through the center into that
subspace. -/
theorem mapsTo_inversion_affineSubspace_of_mem {p : AffineSubspace ℝ P} (hp : c ∈ p) :
    MapsTo (fun x : {x : P // x ≠ c} ↦ inversion c R x x.2) (Subtype.val ⁻¹' (p : Set P)) p :=
  fun _ ↦ AffineMap.lineMap_mem _ hp

/-- Inversion fixes the punctured part of an affine subspace through the center as a set. -/
theorem image_inversion_affineSubspace_of_mem {p : AffineSubspace ℝ P} (hR : R ≠ 0) (hp : c ∈ p) :
    inversionEquiv c hR '' (Subtype.val ⁻¹' (p : Set P)) = Subtype.val ⁻¹' (p : Set P) := by
  have hm : MapsTo (inversionEquiv c hR) (Subtype.val ⁻¹' (p : Set P))
      (Subtype.val ⁻¹' (p : Set P)) := mapsTo_inversion_affineSubspace_of_mem hp
  exact hm.image_subset.antisymm fun x hx ↦
    ⟨inversionEquiv c hR x, hm hx, inversion_involutive c hR x⟩

end EuclideanGeometry

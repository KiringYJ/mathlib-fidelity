/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Nine-point circle

This file defines the nine-point circle of a triangle, and its higher dimension analogue, the
3(n+1)-point sphere of a simplex. Specifically for triangles, we show that it passes through nine
specific points as desired.

## Main definitions
* `Affine.Simplex.ninePointCircle`: the 3(n+1)-point sphere of a simplex.
* `Affine.Simplex.eulerPoint`: a vertex vector scaled by $1/n$ about the nine-point center;
  in dimensions at least two, this is $1/n$ of the way from the Monge point to the vertex.
* `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`: the 3(n+1)-point sphere passes through
  the centroid of each face of the simplex
* `Affine.Simplex.eulerPoint_mem_ninePointCircle`: the 3(n+1)-point sphere passes through all Euler
  points.
* `Affine.Triangle.altitudeFoot_mem_ninePointCircle`: the nine-point circle passes through all
  three altitude feet of the triangle.

## References
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)
-/

@[expose] public section

noncomputable section

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

/--
The 3(n+1)-point sphere of a simplex of positive dimension. Due to the lack of a better name and
to avoid numbers in the identifier, we still use "nine-point circle" in higher dimensions.
Its center $N$ satisfies $N-O=((n+1)/n)(G-O)$, where $O$ is the circumcenter and $G$ the centroid.
The radius is $1/n$ of the circumradius.
-/
def ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n) : Sphere P where
  center := ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : ℝ)

theorem ninePointCircle_center {n : ℕ} [NeZero n] (s : Simplex ℝ P n) : s.ninePointCircle.center =
    ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter := rfl

theorem ninePointCircle_center_vsub_circumcenter {n : ℕ} [NeZero n]
    (s : Simplex ℝ P n) :
    s.ninePointCircle.center -ᵥ s.circumcenter =
      (n : ℝ)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) := by
  rw [ninePointCircle_center, vadd_vsub]
  have h : ((n + 1) / n : ℝ) = (n : ℝ)⁻¹ + 1 := by
    rw [Checked.div_eq_mul_inv, add_mul, Checked.mul_inv_cancel, one_mul, add_comm]
  rw [h, add_smul, one_smul]

theorem smul_ninePointCircle_center_vsub_circumcenter {n : ℕ} [NeZero n]
    (s : Simplex ℝ P n) :
    (n : ℝ) • (s.ninePointCircle.center -ᵥ s.circumcenter) =
      (n + 1 : ℝ) • (s.centroid -ᵥ s.circumcenter) := by
  rw [ninePointCircle_center, vadd_vsub, smul_smul, mul_comm, Checked.div_mul_cancel]

theorem ninePointCircle_center_mem_affineSpan {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    s.ninePointCircle.center ∈ affineSpan ℝ (Set.range s.points) := by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan

theorem ninePointCircle_radius {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    s.ninePointCircle.radius = s.circumradius / (n : ℝ) := rfl

@[simp]
theorem ninePointCircle_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).ninePointCircle = s.ninePointCircle := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]

theorem ninePointCircle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).ninePointCircle =
    { center := f s.ninePointCircle.center, radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]

theorem ninePointCircle_restrict {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]

theorem faceOppositeCentroid_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.faceOppositeCentroid i ∈ s.ninePointCircle := by
  rw [mem_sphere, ninePointCircle_center, ninePointCircle_radius,
    ← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [Checked.eq_div_iff_mul_eq, mul_comm]
  nth_rw 1 [show (n : ℝ) = ‖(n : ℝ)‖ by simp]
  rw [← norm_smul, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul,
    mul_comm (n : ℝ), Checked.div_mul_cancel, add_smul, one_smul, ← sub_sub, ← smul_sub,
    vsub_sub_vsub_cancel_right, ← centroid_vsub_point_eq_smul_vsub, vsub_sub_vsub_cancel_left]

theorem ninePointCircle_eq_circumsphere_medial {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    s.ninePointCircle = s.medial.circumsphere := by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

/-- Euler points are obtained by scaling the vectors from the circumcenter to the vertices by
`1/n` and placing them at the nine-point center. In dimension at least two this is the point
`1/n` of the way from the Monge point to the corresponding vertex. In dimension one it is the
vertex itself, without requiring a Monge point. -/
def eulerPoint {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :=
  (n : ℝ)⁻¹ • (s.points i -ᵥ s.circumcenter) +ᵥ s.ninePointCircle.center

@[simp]
theorem eulerPoint_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).eulerPoint = s.eulerPoint ∘ e.symm := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]
theorem eulerPoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).eulerPoint i = f (s.eulerPoint i) := by
  simp [eulerPoint, ninePointCircle_map, circumcenter_map]

@[simp]
theorem eulerPoint_restrict {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  simp [eulerPoint, ninePointCircle_restrict, circumcenter_restrict]

/-- In dimension one the Euler points are the original vertices. -/
@[simp] theorem eulerPoint_one (s : Simplex ℝ P 1) (i : Fin 2) :
    s.eulerPoint i = s.points i := by
  simp [eulerPoint, ninePointCircle, circumcenter_eq_centroid]

/-- In dimensions at least two, an Euler point is `1/n` of the way from the Monge point to
its vertex. The circumcenter-based definition also retains the meaningful dimension-one case. -/
theorem eulerPoint_eq_smul_vsub_vadd_mongePoint {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) (hn : 2 ≤ n := by omega) :
    s.eulerPoint i = (n : ℝ)⁻¹ • (s.points i -ᵥ s.mongePoint (by omega)) +ᵥ
      s.mongePoint (by omega) := by
  have hm := s.smul_mongePoint_vsub_circumcenter_eq_smul_centroid_vsub hn
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, Nat.cast_add, Nat.cast_one,
    sub_smul, one_smul] at hm
  have he : (n : ℝ) • (s.eulerPoint i -ᵥ s.circumcenter) =
      (s.points i -ᵥ s.circumcenter) +
        (n : ℝ) • (s.ninePointCircle.center -ᵥ s.circumcenter) := by
    rw [eulerPoint, vadd_vsub_assoc, smul_add, smul_smul,
      Checked.mul_inv_cancel, one_smul]
  apply vsub_left_cancel (p := s.mongePoint (by omega))
  rw [vadd_vsub]
  apply (GroupWithZero.isUnit_of_ne_zero (by checked_nonzero : (n : ℝ) ≠ 0)).smul_left_cancel.mp
  rw [smul_smul, Checked.mul_inv_cancel, one_smul,
    ← vsub_sub_vsub_cancel_right (s.eulerPoint i) (s.mongePoint (by omega)) s.circumcenter,
    ← vsub_sub_vsub_cancel_right (s.points i) (s.mongePoint (by omega)) s.circumcenter,
    smul_sub, he, smul_ninePointCircle_center_vsub_circumcenter, ← hm]
  abel

theorem points_vsub_eulerPoint {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1))
    (hn : 2 ≤ n := by omega) :
    s.points i -ᵥ s.eulerPoint i = (((n : ℝ) - 1) / n) •
      (s.points i -ᵥ s.mongePoint (by omega)) := by
  rw [eulerPoint_eq_smul_vsub_vadd_mongePoint s i hn, vsub_vadd_eq_vsub_sub,
    Checked.div_eq_mul_inv, sub_mul, Checked.mul_inv_cancel, one_mul, sub_smul, one_smul]

theorem midpoint_faceOppositeCentroid_eulerPoint {n : ℕ} [hn : NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    midpoint ℝ (s.faceOppositeCentroid i) (s.eulerPoint i) = s.ninePointCircle.center := by
  have hsum : (s.faceOppositeCentroid i -ᵥ s.circumcenter) +
      (s.eulerPoint i -ᵥ s.circumcenter) =
        (2 : ℝ) • (s.ninePointCircle.center -ᵥ s.circumcenter) := by
    rw [faceOppositeCentroid_eq_smul_vsub_vadd_point, eulerPoint,
      vadd_vsub_assoc, vadd_vsub_assoc,
      ← vsub_sub_vsub_cancel_right s.centroid (s.points i) s.circumcenter,
      smul_sub, ninePointCircle_center_vsub_circumcenter, two_smul ℝ]
    abel
  apply vsub_left_cancel (p := s.circumcenter)
  rw [midpoint_vsub, ← smul_add, hsum, smul_smul, invOf_mul_self, one_smul]

theorem isDiameter_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.ninePointCircle.IsDiameter (s.faceOppositeCentroid i) (s.eulerPoint i) where
  left_mem := s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i

theorem eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.eulerPoint i ∈ s.ninePointCircle :=
  (s.isDiameter_ninePointCircle i).right_mem

theorem orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle {n : ℕ} [NeZero n]
    (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    ((s.faceOpposite i).orthogonalProjectionSpan (s.eulerPoint i)).val ∈ s.ninePointCircle := by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i), orthogonalProjectionSpan]
  exact angle_orthogonalProjection_self _ <| faceOppositeCentroid_mem_affineSpan_face s i

end Affine.Simplex

namespace Affine.Triangle

theorem eulerPoint_eq_midpoint (s : Triangle ℝ P) (i : Fin 3) :
    s.eulerPoint i = midpoint ℝ s.orthocenter (s.points i) := by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint, Simplex.points_vsub_eulerPoint, vsub_midpoint]
  norm_num

theorem altitudeFoot_mem_ninePointCircle (s : Triangle ℝ P) (i : Fin 3) :
    s.altitudeFoot i ∈ s.ninePointCircle := by
  convert! s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem,
    Simplex.points_vsub_eulerPoint, Submodule.smul_mem_iff _ (by norm_num),
    ← orthocenter_eq_mongePoint, direction_affineSpan, Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

end Affine.Triangle

end

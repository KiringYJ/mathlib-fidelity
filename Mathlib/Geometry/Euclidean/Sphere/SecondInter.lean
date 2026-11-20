/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.StrictCombination
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `EuclideanGeometry.Sphere.secondInter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/

@[expose] public section


noncomputable section

open scoped RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

/-- The second intersection of the line through `p` in the nonzero direction `v` with the sphere
centered at `s.center` and passing through `p`. For a tangent line the result is `p`. -/
def Sphere.secondInter (s : Sphere P) (p : P) (v : V) (hv : v ≠ 0) : P :=
  Checked.div (-2 * ⟪v, p -ᵥ s.center⟫) ⟪v, v⟫ (inner_self_ne_zero.2 hv).isUnit • v +ᵥ p

@[simp] lemma Sphere.secondInter_map (s : Sphere P) (p : P) (v : V) (f : P →ᵃⁱ[ℝ] P₂)
    (hv : v ≠ 0) :
    Sphere.secondInter ⟨f s.center, s.radius⟩ (f p) (f.linearIsometry v)
      (fun h ↦ hv (f.linearIsometry.injective (h.trans (map_zero _).symm))) =
      f (s.secondInter p v hv) := by
  simp [secondInter, ← AffineIsometry.map_vsub]

lemma Sphere.coe_secondInter (as : AffineSubspace ℝ P) [Nonempty as] (s : Sphere as)
    (p : as) (v : as.direction) (hv : v ≠ 0) :
    s.secondInter p v hv = Sphere.secondInter ⟨(s.center : P), s.radius⟩ (p : P) (v : V)
      (fun h ↦ hv (Subtype.ext h)) :=
  rfl

/-- The distance between `secondInter` and the center equals the distance between the original
point and the center. -/
@[simp]
theorem Sphere.secondInter_dist (s : Sphere P) (p : P) (v : V) {hv : v ≠ 0} :
    dist (s.secondInter p v hv) s.center = dist p s.center := by
  rw [Sphere.secondInter]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl

/-- The point given by `secondInter` lies on the sphere. -/
@[simp]
theorem Sphere.secondInter_mem {s : Sphere P} {p : P} (v : V) {hv : v ≠ 0} :
    s.secondInter p v hv ∈ s ↔ p ∈ s := by
  simp_rw [mem_sphere, Sphere.secondInter_dist]

/-- The point given by `secondInter` equals the original point if and only if the line is
orthogonal to the radius vector. -/
theorem Sphere.secondInter_eq_self_iff {s : Sphere P} {p : P} {v : V} {hv : v ≠ 0} :
    s.secondInter p v hv = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, mul_eq_zero,
      or_iff_right (by simp : (-2 : ℝ) ≠ 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]

/-- A point on a line through a point on a sphere equals that point or `secondInter`. -/
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P} {p : P}
    (hp : p ∈ s) {v : V} (hv : v ≠ 0) {p' : P} (hp' : p' ∈ AffineSubspace.mk' p (ℝ ∙ v)) :
    p' = p ∨ p' = s.secondInter p v hv ↔ p' ∈ s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, Sphere.secondInter_mem]
  · rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    subst hr
    rw [Sphere.secondInter]
    rw [mem_sphere] at h hp
    rw [← hp, dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]

/-- The intersection with the affine span of a direction consists of the starting point and,
when the direction is nonzero, its second intersection. -/
theorem Sphere.eq_or_exists_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P}
    {p : P} (hp : p ∈ s) {v : V} {p' : P} (hp' : p' ∈ AffineSubspace.mk' p (ℝ ∙ v)) :
    p' = p ∨ (∃ hv : v ≠ 0, p' = s.secondInter p v hv) ↔ p' ∈ s := by
  by_cases hv : v = 0
  · subst v
    rw [AffineSubspace.mem_mk', Submodule.span_zero_singleton, Submodule.mem_bot,
      vsub_eq_zero_iff_eq] at hp'
    simp [hp', hp]
  · simpa only [exists_prop_of_true hv] using
      s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp hv hp'

/-- A point on a line through a point on a sphere and a second point equals that point or
`secondInter`. -/
lemma Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair {s : Sphere P} {p q : P}
    (hp : p ∈ s) (hq : q ≠ p) {p' : P} (hp' : p' ∈ affineSpan ℝ {p, q}) :
    p' = p ∨ p' = s.secondInter p (q -ᵥ p) (vsub_ne_zero.2 hq) ↔ p' ∈ s := by
  convert! s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp (vsub_ne_zero.2 hq) ?_
  convert! hp'
  rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineSubspace.self_mem_mk' p _)
    (left_mem_affineSpan_pair _ _ _)]
  simp [direction_affineSpan, vectorSpan_pair_rev]

/-- `secondInter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp]
theorem Sphere.secondInter_smul (s : Sphere P) (p : P) (v : V) {r : ℝ} (hr : r ≠ 0) (hv : v ≠ 0) :
    s.secondInter p (r • v) (smul_ne_zero hr hv) = s.secondInter p v hv := by
  simp only [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul]
  congr 2
  rw [div_mul_eq_mul_div₀, div_eq_div_iff]
  ring

/-- `secondInter` is unchanged by negating the vector. -/
@[simp]
theorem Sphere.secondInter_neg (s : Sphere P) (p : P) (v : V) (hv : v ≠ 0) :
    s.secondInter p (-v) (neg_ne_zero.mpr hv) = s.secondInter p v hv := by
  simpa only [neg_one_smul] using s.secondInter_smul p v (neg_ne_zero.mpr one_ne_zero) hv

/-- Applying `secondInter` twice returns the original point. -/
@[simp]
theorem Sphere.secondInter_secondInter (s : Sphere P) (p : P) (v : V) {hv : v ≠ 0} :
    s.secondInter (s.secondInter p v hv) v hv = p := by
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel₀]
  rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, ← add_smul, ← add_div]
  convert! zero_smul ℝ _
  rw [div_eq_zero_iff]
  ring

/-- The difference between the second intersections of two spheres along a common
direction `v` is `(2 * ⟪v, s₁.center -ᵥ s₂.center⟫ / ⟪v, v⟫) • v`. -/
theorem Sphere.secondInter_vsub_secondInter (s₁ s₂ : Sphere P) (p : P) (v : V) {hv : v ≠ 0} :
    s₁.secondInter p v hv -ᵥ s₂.secondInter p v hv =
      (2 * ⟪v, s₁.center -ᵥ s₂.center⟫ / ⟪v, v⟫) • v := by
  rw [Sphere.secondInter, Sphere.secondInter, vadd_vsub_vadd_cancel_right, ← sub_smul,
    ← vsub_sub_vsub_cancel_left s₁.center s₂.center p, inner_sub_right]
  rw [← sub_div]
  congr 2
  ring

/-- The difference between the second intersections of two spheres along a common
unit direction `v` is `(2 * ⟪v, s₁.center -ᵥ s₂.center⟫) • v`. -/
theorem Sphere.secondInter_vsub_secondInter_of_norm_eq_one (s₁ s₂ : Sphere P) (p : P) {v : V}
    (hv : ‖v‖ = 1) :
    s₁.secondInter p v (by rintro rfl; simp at hv) -ᵥ
      s₂.secondInter p v (by rintro rfl; simp at hv) = (2 * ⟪v, s₁.center -ᵥ s₂.center⟫) • v := by
  simp [hv, secondInter_vsub_secondInter]

/-- The distance between the second intersections of two spheres along a common
direction `v` is `2 * |⟪v, s₁.center -ᵥ s₂.center⟫| / ‖v‖`. -/
theorem Sphere.dist_secondInter_secondInter (s₁ s₂ : Sphere P) (p : P) (v : V) {hv : v ≠ 0} :
    dist (s₁.secondInter p v hv) (s₂.secondInter p v hv) =
      2 * |⟪v, s₁.center -ᵥ s₂.center⟫| / ‖v‖ := by
  rw [dist_eq_norm_vsub V, secondInter_vsub_secondInter, norm_smul, Real.norm_eq_abs, abs_div,
    abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  simp only [real_inner_self_eq_norm_sq, pow_two,
    abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg v))]
  rw [div_mul_eq_mul_div₀, mul_div_mul_right]

/-- The distance between the second intersections of two spheres along a common
unit direction `v` is `2 * |⟪v, s₁.center -ᵥ s₂.center⟫|`. -/
theorem Sphere.dist_secondInter_secondInter_of_norm_eq_one (s₁ s₂ : Sphere P) (p : P) {v : V}
    (hv : ‖v‖ = 1) :
    dist (s₁.secondInter p v (by rintro rfl; simp at hv))
      (s₂.secondInter p v (by rintro rfl; simp at hv)) = 2 * |⟪v, s₁.center -ᵥ s₂.center⟫| := by
  simp only [dist_secondInter_secondInter, hv, div_one₀]

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result of `secondInter` may be expressed using `lineMap`. -/
theorem Sphere.secondInter_eq_lineMap (s : Sphere P) (p p' : P) (hp : p' ≠ p) :
    s.secondInter p (p' -ᵥ p) (vsub_ne_zero.2 hp) =
      AffineMap.lineMap p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
  rfl

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result lies in the span of the two points. -/
theorem Sphere.secondInter_vsub_mem_affineSpan (s : Sphere P) (p₁ p₂ : P) (hp : p₂ ≠ p₁) :
    s.secondInter p₁ (p₂ -ᵥ p₁) (vsub_ne_zero.2 hp) ∈ affineSpan ℝ {p₁, p₂} :=
  smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the three points are collinear. -/
theorem Sphere.secondInter_collinear (s : Sphere P) (p p' : P) (hp : p' ≠ p) :
    Collinear ℝ ({p, p', s.secondInter p (p' -ᵥ p) (vsub_ne_zero.2 hp)} : Set P) := by
  rw [Set.pair_comm, Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _ hp)).2
      (collinear_pair ℝ _ _)

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is not outside the sphere, the second point is weakly
between the first point and the result of `secondInter`. -/
theorem Sphere.wbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center ≤ s.radius) (h : p' ≠ p) :
    Wbtw ℝ p p' (s.secondInter p (p' -ᵥ p) (vsub_ne_zero.2 h)) := by
  refine
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p' h) hp hp'
      ((Sphere.secondInter_mem _).2 hp) ?_
  intro he
  rw [eq_comm, Sphere.secondInter_eq_self_iff, ← neg_neg (p' -ᵥ p), inner_neg_left,
    neg_vsub_eq_vsub_rev, neg_eq_zero, eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he

/-- A point strictly inside a sphere differs from every point on the sphere. -/
theorem Sphere.ne_of_mem_of_dist_center_lt_radius {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center < s.radius) : p' ≠ p := by
  rintro rfl
  exact hp'.ne (mem_sphere.1 hp)

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is inside the sphere, the second point is strictly between
the first point and the result of `secondInter`. -/
theorem Sphere.sbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center < s.radius) :
    Sbtw ℝ p p' (s.secondInter p (p' -ᵥ p)
      (vsub_ne_zero.2 (Sphere.ne_of_mem_of_dist_center_lt_radius hp hp'))) := by
  have hn := Sphere.ne_of_mem_of_dist_center_lt_radius hp hp'
  refine ⟨Sphere.wbtw_secondInter hp hp'.le hn, hn, ?_⟩
  exact Sphere.ne_of_mem_of_dist_center_lt_radius ((Sphere.secondInter_mem _).2 hp) hp'

/-- If the point passed to `secondInter` is a vertex of a simplex, lying on the sphere, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is given by a
subtraction involving that vertex and a point in the interior of the opposite face, the given
vertex and the result of `secondInter` are on opposite sides of that face. -/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite {s : Sphere P}
    {n : ℕ} [NeZero n] {sx : Affine.Simplex ℝ P n} {i : Fin (n + 1)} (hi : sx.points i ∈ s)
    (hsx : ∀ j, dist (sx.points j) s.center ≤ s.radius) {p : P}
    (hp : p ∈ (sx.faceOpposite i).interior) :
    (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i)) (vsub_ne_zero.2
        (Sphere.ne_of_mem_of_dist_center_lt_radius hi
          ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
            (fun _ ↦ hsx _))))) :=
  Sbtw.sOppSide_of_notMem_of_mem
    (s.sbtw_secondInter hi ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
      (fun j ↦ hsx _)))
    (by simp)
    (Set.mem_of_mem_of_subset hp ((sx.faceOpposite i).interior_subset_closedInterior.trans
      (sx.faceOpposite i).closedInterior_subset_affineSpan))

attribute [local instance] Nat.AtLeastTwo.neZero_sub_one

/-- If the point passed to `secondInter` is a vertex of a simplex, lying on the sphere, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is given by a
subtraction involving that vertex and a point in the interior of the simplex, the given vertex
and the result of `secondInter` are on opposite sides of the face opposite that vertex. -/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior {s : Sphere P}
    {n : ℕ} [Nat.AtLeastTwo n] {sx : Affine.Simplex ℝ P n} {i : Fin (n + 1)} (hi : sx.points i ∈ s)
    (hsx : ∀ j, dist (sx.points j) s.center ≤ s.radius) {p : P}
    (hp : p ∈ sx.interior) :
    (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i)) (vsub_ne_zero.2
        (Sphere.ne_of_mem_of_dist_center_lt_radius hi
          (sx.dist_lt_of_mem_interior_of_strictConvexSpace hp hsx)))) := by
  have hpne := Sphere.ne_of_mem_of_dist_center_lt_radius hi
    (sx.dist_lt_of_mem_interior_of_strictConvexSpace hp hsx)
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  have hwi : 0 < 1 - w i := sub_pos.mpr (hw01 i).2
  let r : ℝ := (1 - w i)⁻¹
  have hrpos : 0 < r := inv_pos.2 hwi
  let p' : P := AffineMap.lineMap (sx.points i) (Finset.univ.affineCombination ℝ sx.points w) r
  have hp' : (p' -ᵥ (sx.points i)) =
      r • (Finset.univ.affineCombination ℝ sx.points w -ᵥ (sx.points i)) := by simp [p']
  have hp'int : p' ∈ (sx.faceOpposite i).interior := by
    simp_rw [p', ← Finset.univ.affineCombination_piSingle ℝ (sx.points)
      (Finset.mem_univ i), AffineMap.lineMap_apply, Finset.affineCombination_vsub,
      ← LinearMap.map_smul, Finset.weightedVSub_vadd_affineCombination,
      Affine.Simplex.faceOpposite]
    rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos]
    · simp only [Finset.mem_compl, Finset.mem_singleton, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Decidable.not_not, forall_eq, Pi.single_eq_same]
      refine ⟨fun j hj ↦ ?_, ?_⟩
      · simp [hj, hrpos, (hw01 j).1]
      · rw [show w i - 1 = -(1 - w i) from by ring, mul_neg, inv_mul_cancel₀, neg_add_cancel]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw]
  have h := s.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite hi hsx hp'int
  simpa only [hp', s.secondInter_smul _ _ hrpos.ne' (vsub_ne_zero.2 hpne)] using h

end EuclideanGeometry

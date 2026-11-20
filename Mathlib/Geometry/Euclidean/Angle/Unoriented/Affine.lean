/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.
-/

@[expose] public section


noncomputable section

open Real

namespace EuclideanGeometry

open InnerProductGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {p p₀ : P}

/-- The undirected angle at `p₂` between the nonconstant line segments to `p₁` and `p₃`.
Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation. -/
nonrec def angle (p₁ p₂ p₃ : P)
    (hp₁p₂ : p₁ ≠ p₂ := by first | assumption | (intro h; simp_all) |
      fail "the first endpoint must differ from the vertex")
    (hp₃p₂ : p₃ ≠ p₂ := by first | assumption | (intro h; simp_all) |
      fail "the second endpoint must differ from the vertex") : ℝ :=
  angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)
    (vsub_ne_zero.mpr hp₁p₂) (vsub_ne_zero.mpr hp₃p₂)

@[inherit_doc] scoped notation:max "∠ " p₁:arg p₂:arg p₃:arg =>
  EuclideanGeometry.angle p₁ p₂ p₃

theorem continuousAt_angle
    {x : {p : P × P × P // p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.2.1}} :
    ContinuousAt (fun y : {p : P × P × P // p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.2.1} ↦
      angle y.1.1 y.1.2.1 y.1.2.2 y.2.1 y.2.2) x := by
  let f : {p : P × P × P // p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.2.1} →
      {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0} := fun y ↦
    ⟨(y.1.1 -ᵥ y.1.2.1, y.1.2.2 -ᵥ y.1.2.1),
      vsub_ne_zero.mpr y.2.1, vsub_ne_zero.mpr y.2.2⟩
  have hf : Continuous f := by
    unfold f
    fun_prop
  exact (InnerProductGeometry.continuousAt_angle (x := f x)).comp hf.continuousAt

@[simp]
theorem _root_.AffineIsometry.angle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    angle (f p₁) (f p₂) (f p₃) (fun h ↦ hp₁p₂ (f.injective h)) (fun h ↦ hp₃p₂ (f.injective h)) =
      ∠ p₁ p₂ p₃ := by
  simpa only [angle, AffineIsometry.map_vsub] using
    f.linearIsometry.angle_map (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
      (hu := vsub_ne_zero.mpr hp₁p₂) (hv := vsub_ne_zero.mpr hp₃p₂)

@[simp, norm_cast]
theorem _root_.AffineSubspace.angle_coe {s : AffineSubspace ℝ P} (p₁ p₂ p₃ : s)
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃

/-- A homothety with a nonzero scale factor preserves angles. -/
@[simp] lemma angle_homothety (p p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    {r : ℝ} (h : r ≠ 0) :
    ∠ (AffineMap.homothety p r p₁) (AffineMap.homothety p r p₂) (AffineMap.homothety p r p₃) =
      ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  exact InnerProductGeometry.angle_smul_smul h (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
    (hx := vsub_ne_zero.mpr hp₁p₂) (hy := vsub_ne_zero.mpr hp₃p₂)

/-- Angles are translation invariant. -/
@[simp]
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVAdd ℝ P v).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
theorem angle_const_vsub (p p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVSub ℝ p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
theorem angle_vsub_const (p₁ p₂ p₃ p : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry.angle_map _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
theorem angle_neg (v₁ v₂ v₃ : V) {h₁₂ : v₁ ≠ v₂} {h₃₂ : v₃ ≠ v₂} :
    ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

theorem angle_smul_right_of_pos (p₁ : P) {p₂ p₃ p₄ : P} {r : ℝ} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂)
    {hp₁p₂ : p₁ ≠ p₂} {hp₄p₂ : p₄ ≠ p₂} :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_right_of_pos (p₁ -ᵥ p₂) (p₄ -ᵥ p₂) hr

theorem angle_smul_left_of_pos {p₁ p₂ p₄ : P} (p₃ : P) {r : ℝ} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂)
    {hp₃p₂ : p₃ ≠ p₂} {hp₄p₂ : p₄ ≠ p₂} :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₂ p₃ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_left_of_pos (p₄ -ᵥ p₂) (p₃ -ᵥ p₂) hr

/-- The angle at a point does not depend on the order of the other two
points. -/
nonrec theorem angle_comm (p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₁ :=
  angle_comm _ _

/-- The angle at a point is nonnegative. -/
nonrec theorem angle_nonneg (p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} : 0 ≤ ∠ p₁ p₂ p₃ :=
  angle_nonneg _ _

/-- The angle at a point is at most π. -/
nonrec theorem angle_le_pi (p₁ p₂ p₃ : P) {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} : ∠ p₁ p₂ p₃ ≤ π :=
  angle_le_pi _ _

/-- The angle ∠ABA for distinct points `A` and `B` is `0`. -/
theorem angle_self_of_ne {h : p ≠ p₀} : ∠ p p₀ p = 0 :=
  InnerProductGeometry.angle_self (hx := vsub_ne_zero.mpr h)

/-- The endpoints of a straight angle are distinct. -/
theorem left_ne_right_of_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π) : p₁ ≠ p₃ := by
  intro hp₁p₃
  subst p₃
  exact Real.pi_ne_zero (h.symm.trans (angle_self_of_ne (h := hp₁p₂)))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_left {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π) :
    angle p₂ p₁ p₃ hp₁p₂.symm (left_ne_right_of_angle_eq_pi h).symm = 0 := by
  have hpi := h
  unfold angle at hpi
  obtain ⟨_, r, hr, hpr⟩ := angle_eq_pi_iff.mp hpi
  unfold angle
  rw [angle_eq_zero_iff]
  use vsub_ne_zero.mpr hp₁p₂.symm, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul, ← neg_vsub_eq_vsub_rev p₁ p₂, smul_neg]
  simp [← hpr]

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_right {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π) : angle p₂ p₃ p₁ hp₃p₂.symm (left_ne_right_of_angle_eq_pi h) = 0 :=
  angle_eq_zero_of_angle_eq_pi_left ((angle_comm p₃ p₂ p₁).trans h)

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
theorem angle_eq_angle_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₂p₃ : p₂ ≠ p₃} {hp₄p₃ : p₄ ≠ p₃} (h : ∠ p₂ p₃ p₄ = π) :
    angle p₁ p₂ p₃ hp₁p₂ hp₂p₃.symm =
      angle p₁ p₂ p₄ hp₁p₂ (left_ne_right_of_angle_eq_pi h).symm := by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  replace hpr : (-r + 1) • (p₃ -ᵥ p₂) = p₄ -ᵥ p₂ := by
    rw [add_smul, ← neg_vsub_eq_vsub_rev p₂ p₃, smul_neg, neg_smul, ← hpr]
    simp
  replace hr : 0 < -r + 1 := by linarith
  exact angle_smul_right_of_pos p₁ hr hpr (hp₁p₂ := hp₁p₂) (hp₄p₂ := hp₂p₃.symm)

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
nonrec theorem angle_add_angle_eq_pi_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P}
    {hp₁p₃ : p₁ ≠ p₃} {hp₂p₃ : p₂ ≠ p₃} {hp₄p₃ : p₄ ≠ p₃} (h : ∠ p₂ p₃ p₄ = π) :
    ∠ p₁ p₃ p₂ + ∠ p₁ p₃ p₄ = π := by
  unfold angle at h
  rw [angle_comm p₁ p₃ p₂, angle_comm p₁ p₃ p₄]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h

/-- **Vertical Angles Theorem**: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p₁ p₂ p₃ p₄ p₅ : P}
    {hp₁p₅ : p₁ ≠ p₅} {hp₂p₅ : p₂ ≠ p₅} {hp₃p₅ : p₃ ≠ p₅} {hp₄p₅ : p₄ ≠ p₅}
    (hapc : ∠ p₁ p₅ p₃ = π)
    (hbpd : ∠ p₂ p₅ p₄ = π) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₁ hbpd (hp₁p₃ := hp₁p₅),
    angle_comm p₄ p₅ p₁ (hp₁p₂ := hp₄p₅) (hp₃p₂ := hp₁p₅),
    angle_add_angle_eq_pi_of_angle_eq_pi p₄ hapc (hp₁p₃ := hp₄p₅),
    angle_comm p₄ p₅ p₃ (hp₁p₂ := hp₄p₅) (hp₃p₂ := hp₃p₅)]

/-- If ∠ABC = π then dist A B ≠ 0. -/
theorem left_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (_h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₂ ≠ 0 :=
  dist_ne_zero.mpr hp₁p₂

/-- If ∠ABC = π then dist C B ≠ 0. -/
theorem right_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (_h : ∠ p₁ p₂ p₃ = π) : dist p₃ p₂ ≠ 0 :=
  dist_ne_zero.mpr hp₃p₂

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_of_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_iff_angle_eq_pi {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ ≠ p₂) (hp₃p₂ : p₃ ≠ p₂) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ ↔ ∠ p₁ p₂ p₃ = π := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (hx := vsub_ne_zero.2 hp₁p₂) (hy := vsub_ne_zero.2 hp₃p₂)

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = 0) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ ≠ p₂) (hp₃p₂ : p₃ ≠ p₂) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| ↔ ∠ p₁ p₂ p₃ = 0 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (hx := vsub_ne_zero.2 hp₁p₂)
      (hy := vsub_ne_zero.2 hp₃p₂)

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
theorem angle_midpoint_eq_pi (p₁ p₂ : P) (hp₁p₂ : p₁ ≠ p₂) :
    angle p₁ (midpoint ℝ p₁ p₂) p₂
      (fun h ↦ hp₁p₂ ((midpoint_eq_left_iff ℝ).mp h.symm))
      (fun h ↦ hp₁p₂ ((midpoint_eq_right_iff ℝ).mp h.symm)) = π := by
  rw [← dist_eq_add_dist_iff_angle_eq_pi
      (fun h ↦ hp₁p₂ ((midpoint_eq_left_iff ℝ).mp h.symm))
      (fun h ↦ hp₁p₂ ((midpoint_eq_right_iff ℝ).mp h.symm)), dist_comm p₂]
  simp [dist_eq_norm_vsub V, left_vsub_midpoint, midpoint_vsub_right, norm_smul, ← two_mul]

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂}
    {hp₃m : p₃ ≠ midpoint ℝ p₁ p₂} (h : dist p₃ p₁ = dist p₃ p₂) :
    angle p₃ (midpoint ℝ p₁ p₂) p₁ hp₃m
      (fun e ↦ hp₁p₂ ((midpoint_eq_left_iff ℝ).mp e.symm)) = π / 2 := by
  let m : P := midpoint ℝ p₁ p₂
  have h1 : p₃ -ᵥ p₁ = p₃ -ᵥ m - (p₁ -ᵥ m) := (vsub_sub_vsub_cancel_right p₃ p₁ m).symm
  have h2 : p₃ -ᵥ p₂ = p₃ -ᵥ m + (p₁ -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p₃ p₁, dist_eq_norm_vsub V p₃ p₂, h1, h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p₃ -ᵥ m) (p₁ -ᵥ m)
    (hx := vsub_ne_zero.2 hp₃m)
    (hy := vsub_ne_zero.2 (fun e ↦ hp₁p₂ ((midpoint_eq_left_iff ℝ).mp e.symm)))).mp h.symm

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂}
    {hp₃m : p₃ ≠ midpoint ℝ p₁ p₂} (h : dist p₃ p₁ = dist p₃ p₂) :
    angle p₃ (midpoint ℝ p₁ p₂) p₂ hp₃m
      (fun e ↦ hp₁p₂ ((midpoint_eq_right_iff ℝ).mp e.symm)) = π / 2 := by
  simpa only [midpoint_comm p₂ p₁] using
    angle_left_midpoint_eq_pi_div_two_of_dist_eq (hp₁p₂ := hp₁p₂.symm)
      (hp₃m := by simpa only [midpoint_comm p₂ p₁] using hp₃m) h.symm

/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
theorem _root_.Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₁ p₂ p₃ h.left_ne h.right_ne = π := by
  rw [angle, angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r ≠ 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simp at hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  replace hr1 := hr1.lt_of_ne hr1'
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r,
    div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, ?_⟩
  rw [← hp₂, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
    zero_sub, smul_neg, smul_smul, div_mul_cancel₀ _, neg_smul, neg_neg, sub_eq_iff_eq_add, ←
    add_smul, sub_add_cancel, one_smul]

/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
theorem _root_.Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₃ p₂ p₁ h.right_ne h.left_ne = π :=
  (angle_comm p₃ p₂ p₁ (hp₁p₂ := h.right_ne) (hp₃p₂ := h.left_ne)).trans h.angle₁₂₃_eq_pi

/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle, angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  have hdenom : 0 < 1 - r := sub_pos.2 (hr.trans zero_lt_one)
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one hdenom.le,
    (div_le_one hdenom).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub_ne_zero.1 hp₁p₂).symm, ?_⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    rw [AffineMap.lineMap_apply, hp₃p₂, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p₂ p₁, smul_neg, ←
      neg_smul, smul_add, smul_smul, ← add_smul, eq_comm, eq_vadd_iff_vsub_eq]
    convert! (one_smul ℝ (p₂ -ᵥ p₁)).symm
    field [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm]
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    exact ⟨hr.ne, hp₁p₂⟩

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    angle p₂ p₁ p₃ hp₂p₁ (h.left_ne_right_of_ne_left hp₂p₁).symm = 0 := by
  rw [angle, angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul,
    inv_mul_cancel₀, one_smul]

/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
theorem _root_.Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₂ p₁ p₃ h.ne_left h.left_ne_right.symm = 0 :=
  h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    angle p₃ p₁ p₂ (h.left_ne_right_of_ne_left hp₂p₁).symm hp₂p₁ = 0 :=
  (angle_comm p₃ p₁ p₂ (hp₁p₂ := (h.left_ne_right_of_ne_left hp₂p₁).symm)).trans
    (h.angle₂₁₃_eq_zero_of_ne hp₂p₁)

/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
theorem _root_.Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₃ p₁ p₂ h.left_ne_right.symm h.ne_left = 0 :=
  h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    angle p₂ p₃ p₁ hp₂p₃ (h.left_ne_right_of_ne_right hp₂p₃) = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
theorem _root_.Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₂ p₃ p₁ h.ne_right h.left_ne_right = 0 :=
  h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    angle p₁ p₃ p₂ (h.left_ne_right_of_ne_right hp₂p₃) hp₂p₃ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
theorem _root_.Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    angle p₁ p₃ p₂ h.left_ne_right h.ne_right = 0 :=
  h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ := by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_gt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply, hp₃p₂, smul_smul, inv_mul_cancel₀, one_smul,
        vsub_vadd]
    · refine Or.inr ⟨?_, r, ⟨hr0.le, hr1.le⟩, ?_⟩
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        exact ⟨hr0.ne.symm, hp₁p₂⟩
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂

/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨ Sbtw ℝ p₂ p₁ p₃ ∨ Sbtw ℝ p₂ p₃ p₁ := by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

/-- An Unoriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
theorem _root_.Sbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) {hp₁p₂ : p₁ ≠ p₂} (h : Sbtw ℝ p₂ p₃ p) :
    angle p₁ p₂ p₃ hp₁p₂ h.ne_left = angle p₁ p₂ p hp₁p₂ h.left_ne_right.symm :=
  angle_eq_angle_of_angle_eq_pi _ h.angle₁₂₃_eq_pi

/-- An Unoriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
theorem _root_.Sbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) {hp₃p₂ : p₃ ≠ p₂} (h : Sbtw ℝ p₂ p₁ p) :
    angle p₁ p₂ p₃ h.ne_left hp₃p₂ = angle p p₂ p₃ h.left_ne_right.symm hp₃p₂ :=
  (angle_comm p₁ p₂ p₃ (hp₁p₂ := h.ne_left) (hp₃p₂ := hp₃p₂)).trans <|
    (h.angle_eq_right p₃ (hp₁p₂ := hp₃p₂)).trans <|
      angle_comm p₃ p₂ p (hp₁p₂ := hp₃p₂) (hp₃p₂ := h.left_ne_right.symm)

/-- An Unoriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
theorem _root_.Wbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) {hp₁p₂ : p₁ ≠ p₂}
    (h : Wbtw ℝ p₂ p₃ p) (hp₃p₂ : p₃ ≠ p₂) :
    angle p₁ p₂ p₃ hp₁p₂ hp₃p₂ = angle p₁ p₂ p hp₁p₂ (h.left_ne_right_of_ne_left hp₃p₂).symm := by
  by_cases hp₃p : p₃ = p; · simp [hp₃p]
  exact Sbtw.angle_eq_right _ ⟨h, hp₃p₂, hp₃p⟩

/-- An Unoriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
theorem _root_.Wbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) {hp₃p₂ : p₃ ≠ p₂}
    (h : Wbtw ℝ p₂ p₁ p) (hp₁p₂ : p₁ ≠ p₂) :
    angle p₁ p₂ p₃ hp₁p₂ hp₃p₂ = angle p p₂ p₃ (h.left_ne_right_of_ne_left hp₁p₂).symm hp₃p₂ :=
  (angle_comm p₁ p₂ p₃ (hp₁p₂ := hp₁p₂) (hp₃p₂ := hp₃p₂)).trans <|
    (h.angle_eq_right p₃ hp₁p₂ (hp₁p₂ := hp₃p₂)).trans <|
      angle_comm p₃ p₂ p (hp₁p₂ := hp₃p₂) (hp₃p₂ := (h.left_ne_right_of_ne_left hp₁p₂).symm)

lemma angle_pointReflection_right {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    angle p₁ p₂ (AffineEquiv.pointReflection ℝ p₂ p₃) hp₁p₂
      (sbtw_pointReflection_of_ne ℝ hp₃p₂.symm).right_ne = π - ∠ p₁ p₂ p₃ := by
  rw [eq_sub_iff_add_eq]
  apply EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
  exact (sbtw_pointReflection_of_ne ℝ hp₃p₂.symm).symm.angle₁₂₃_eq_pi

/-- Three points are collinear if and only if the first or third point equals the second or the
angle between them is 0 or π. -/
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨
      ∃ (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂),
        angle p₁ p₂ p₃ h₁₂ h₃₂ = 0 ∨ angle p₁ p₂ p₃ h₁₂ h₃₂ = π := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    refine Or.inr (Or.inr ⟨h₁₂, h₃₂, ?_⟩)
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
  · rcases h with (rfl | rfl | ⟨h₁₂, h₃₂, h | h⟩)
    · simpa using collinear_pair ℝ p₁ p₃
    · simpa using collinear_pair ℝ p₁ p₃
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      · rw [Set.insert_comm]
        exact h.collinear
      · rw [Set.insert_comm, Set.pair_comm]
        exact h.collinear
    · rw [angle_eq_pi_iff_sbtw] at h
      exact h.wbtw.collinear

/-- If the angle between three points is 0, they are collinear. -/
theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2
    (Or.inr (Or.inr ⟨hp₁p₂, hp₃p₂, Or.inl h⟩))

/-- If the angle between three points is π, they are collinear. -/
theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : ∠ p₁ p₂ p₃ = π) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2
    (Or.inr (Or.inr ⟨hp₁p₂, hp₃p₂, Or.inr h⟩))

/-- If three points are not collinear, the angle between them is nonzero. -/
theorem angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm ≠ 0 :=
  mt collinear_of_angle_eq_zero h

/-- If three points are not collinear, the angle between them is not π. -/
theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm ≠ π :=
  mt collinear_of_angle_eq_pi h

/-- If three points are not collinear, the angle between them is positive. -/
theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

/-- If three points are not collinear, the angle between them is less than π. -/
theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm < π :=
  (angle_le_pi _ _ _).lt_of_ne <| angle_ne_pi_of_not_collinear h

/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
nonrec theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
nonrec theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
nonrec theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
nonrec theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
nonrec theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two

/-- Three points are collinear if and only if the first or third point equals the second or
the sine of the angle between three points is zero. -/
theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨
      ∃ (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂), Real.sin (angle p₁ p₂ p₃ h₁₂ h₃₂) = 0 := by
  simp only [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi,
    collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

/-- If three points are not collinear, the sine of the angle between them is positive. -/
theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

/-- If three points are not collinear, the sine of the angle between them is nonzero. -/
theorem sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    Real.sin (angle p₁ p₂ p₃ (ne₁₂_of_not_collinear h) (ne₂₃_of_not_collinear h).symm) ≠ 0 :=
  ne_of_gt (sin_pos_of_not_collinear h)

/-- If the sine of the angle between three points is 0, they are collinear. -/
theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} {hp₁p₂ : p₁ ≠ p₂} {hp₃p₂ : p₃ ≠ p₂}
    (h : Real.sin (∠ p₁ p₂ p₃) = 0) : Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_sin_eq_zero.2 (Or.inr (Or.inr ⟨hp₁p₂, hp₃p₂, h⟩))

end EuclideanGeometry

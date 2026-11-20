/-
Copyright (c) 2025 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Topology.MetricSpace.Similarity

/-!
# Triangle Similarity

This file contains theorems about similarity of triangles, including conditions
for similarity based on sides and angles.

-/

public section

open scoped Congruent EuclideanGeometry

open Similar

namespace EuclideanGeometry

variable {V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {a b c : P₁} {a' b' c' : P₂}

/-- Two equal angles determine the similarity class of a noncollinear triangle. -/
theorem similar_of_angle_angle {hab' : a' ≠ b'} {hcb' : c' ≠ b'} {hac' : a' ≠ c'}
    (h_not_col : ¬Collinear ℝ {a, b, c})
    (h₁ : angle a b c (ne₁₂_of_not_collinear h_not_col) (ne₂₃_of_not_collinear h_not_col).symm =
      angle a' b' c' hab' hcb')
    (h₂ : angle b c a (ne₂₃_of_not_collinear h_not_col) (ne₁₃_of_not_collinear h_not_col) =
      angle b' c' a' hcb'.symm hac') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have hab := ne₁₂_of_not_collinear h_not_col
  have hac := ne₁₃_of_not_collinear h_not_col
  have hbc := ne₂₃_of_not_collinear h_not_col
  have hsum := angle_add_angle_add_angle_eq_pi c hab.symm (hp₃₁ := hac.symm) (hp₃₂ := hbc.symm)
  have hsum' := angle_add_angle_add_angle_eq_pi c' hab'.symm (hp₃₁ := hac'.symm) (hp₃₂ := hcb')
  have h₃ : angle c a b hac.symm hab.symm = angle c' a' b' hac'.symm hab'.symm := by
    rw [h₁, h₂] at hsum
    linarith
  have hc : Real.sin (angle b c a hbc hac) ≠ 0 := sin_ne_zero_of_not_collinear
    (by rwa [Set.insert_comm, Set.pair_comm] at h_not_col)
  apply similar_of_side_side (dist_ne_zero.mpr hab) (dist_ne_zero.mpr hab')
  · have hl := law_sin c a b (hp₁₂ := hac.symm) (hp₃₂ := hab.symm) (hp₃₁ := hbc)
    have hr := law_sin c' a' b' (hp₁₂ := hac'.symm) (hp₃₂ := hab'.symm) (hp₃₁ := hcb'.symm)
    rw [← h₃, ← h₂] at hr
    apply mul_left_cancel₀ hc
    linear_combination (dist a' b') * hl - (dist a b) * hr
  · have hl := law_sin b c a (hp₁₂ := hbc) (hp₃₂ := hac) (hp₃₁ := hab)
    have hr := law_sin b' c' a' (hp₁₂ := hcb'.symm) (hp₃₂ := hac') (hp₃₁ := hab')
    rw [← h₁, ← h₂] at hr
    apply mul_left_cancel₀ hc
    linear_combination (dist a b) * hr - (dist a' b') * hl

/-- With a positive common scale for the adjacent sides, SAS also applies when an incident
side vanishes. The angle comparison is required only when both rays exist. -/
theorem similar_of_scaled_adjacent {k : ℝ} (hk : 0 < k)
    (h_ab : dist a b = k * dist a' b') (h_cb : dist c b = k * dist c' b')
    (h : ∀ (hab : a ≠ b) (hcb : c ≠ b) (hab' : a' ≠ b') (hcb' : c' ≠ b'),
      angle a b c hab hcb = angle a' b' c' hab' hcb') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have h_ac : dist a c = k * dist a' c' := by
    rcases eq_or_ne a b with rfl | hab
    · have e : a' = b' := dist_eq_zero.mp <| (mul_eq_zero.mp
        (by simpa only [dist_self] using h_ab.symm)).resolve_left hk.ne'
      subst a'
      simpa [dist_comm] using h_cb
    rcases eq_or_ne c b with rfl | hcb
    · have e : c' = b' := dist_eq_zero.mp <| (mul_eq_zero.mp
        (by simpa only [dist_self] using h_cb.symm)).resolve_left hk.ne'
      simpa only [e] using h_ab
    have hab' : a' ≠ b' := fun e ↦ (dist_ne_zero.mpr hab) (by simpa [e] using h_ab)
    have hcb' : c' ≠ b' := fun e ↦ (dist_ne_zero.mpr hcb) (by simpa [e] using h_cb)
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg hk.le dist_nonneg)).mp
    have hl := law_cos a b c (hp₁ := hab) (hp₃ := hcb)
    rw [h_ab, h_cb, h hab hcb hab' hcb'] at hl
    have hr := law_cos a' b' c' (hp₁ := hab') (hp₃ := hcb')
    linear_combination hl - k ^ 2 * hr
  apply Similar.of_exists_pos_dist_eq
  refine ⟨k, hk, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- Proportional adjacent sides and equal included angles imply similarity.
The third side may vanish, and the vertices may be collinear. -/
theorem similar_of_side_angle_side {hab : a ≠ b} {hcb : c ≠ b} {hab' : a' ≠ b'} {hcb' : c' ≠ b'}
    (h : angle a b c hab hcb = angle a' b' c' hab' hcb')
    (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have ha := dist_pos.mpr hab
  have ha' := dist_pos.mpr hab'
  let k := dist a b / dist a' b'
  have hk := div_pos ha ha'
  have h_ab : dist a b = k * dist a' b' := div_mul_cancel₀ _ |>.symm
  have h_cb : dist c b = k * dist c' b' := by
    rw [show k = dist a b / dist a' b' from rfl, div_mul_eq_mul_div₀, eq_div_iff]
    simpa only [dist_comm c b, dist_comm c' b'] using hd.symm
  exact similar_of_scaled_adjacent hk h_ab h_cb (fun _ _ _ _ ↦ h)

/-- Similarity preserves each angle whose two incident sides are nonzero. -/
theorem _root_.Similar.angle_eq (h : ![a, b, c] ∼ ![a', b', c']) (hab : a ≠ b) (hcb : c ≠ b) :
    angle a b c hab hcb =
      angle a' b' c' (h.ne_of_ne (i := 0) (j := 1) hab) (h.ne_of_ne (i := 2) (j := 1) hcb) := by
  have hab' : a' ≠ b' := h.ne_of_ne (i := 0) (j := 1) hab
  have hcb' : c' ≠ b' := h.ne_of_ne (i := 2) (j := 1) hcb
  obtain ⟨r, hr, hd⟩ := h.exists_pos_dist_eq
  have h_ab : dist a b = r * dist a' b' := hd 0 1
  have h_cb : dist c b = r * dist c' b' := hd 2 1
  have h_ac : dist a c = r * dist a' c' := hd 0 2
  have hl := law_cos a b c (hp₁ := hab) (hp₃ := hcb)
  have hr' := law_cos a' b' c' (hp₁ := hab') (hp₃ := hcb')
  rw [h_ab, h_cb, h_ac] at hl
  apply Real.injOn_cos ⟨angle_nonneg .., angle_le_pi ..⟩ ⟨angle_nonneg .., angle_le_pi ..⟩
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    (pow_ne_zero 2 hr.ne')) (dist_ne_zero.mpr hab')) (dist_ne_zero.mpr hcb'))
  linear_combination hl - r ^ 2 * hr'

/-- In similar triangles with three distinct vertices, all three angles agree. -/
theorem _root_.Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) (hab : a ≠ b)
    (hcb : c ≠ b) (hac : a ≠ c) :
    angle a b c hab hcb =
      angle a' b' c' (h.ne_of_ne (i := 0) (j := 1) hab) (h.ne_of_ne (i := 2) (j := 1) hcb) ∧
    angle b c a hcb.symm hac =
      angle b' c' a' (h.ne_of_ne (i := 1) (j := 2) hcb.symm) (h.ne_of_ne (i := 0) (j := 2) hac) ∧
    angle c a b hac.symm hab.symm =
      angle c' a' b' (h.ne_of_ne (i := 2) (j := 0) hac.symm)
        (h.ne_of_ne (i := 1) (j := 0) hab.symm) :=
  ⟨h.angle_eq hab hcb, h.comm_left.comm_right.angle_eq hcb.symm hac,
    h.comm_right.comm_left.angle_eq hac.symm hab.symm⟩

end EuclideanGeometry

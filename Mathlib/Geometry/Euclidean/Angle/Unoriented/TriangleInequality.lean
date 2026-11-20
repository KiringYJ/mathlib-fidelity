/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg, Jovan Gerbscheid
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

import Mathlib.Geometry.Euclidean.Triangle

/-!
# The Triangle Inequality for Angles

This file contains the proof that angles obey the triangle inequality.
-/

open InnerProductGeometry
open NormedSpace

open scoped Real NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

section UnitVectorAngles

/-- Gets the orthogonal direction of one vector relative to another. -/
noncomputable def ortho (x y : V) : V := y - (ℝ ∙ x).starProjection y

lemma ortho_eq_sub_inner (x : V) {y : V} (hy : ‖y‖ = 1) : ortho y x = x - inner ℝ y x • y := by
  rw [ortho, Submodule.starProjection_unit_singleton _ hy]

lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho_eq_sub_inner x hy, inner_sub_right,
    inner_self_eq_one_of_norm_eq_one hx, real_inner_smul_right, real_inner_comm, sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]

lemma inner_ortho_right (x y : V) : ⟪y, ortho y x⟫ = 0 := by
  rw [ortho, real_inner_comm, Submodule.starProjection_inner_eq_zero]
  exact Submodule.mem_span_singleton_self y

lemma inner_normalize_ortho (x y : V) {h : ortho y x ≠ 0} :
    ⟪y, normalize (ortho y x)⟫ = 0 := by
  simp only [NormedSpace.normalize, real_inner_smul_right, inner_ortho_right, mul_zero]

omit [InnerProductSpace ℝ V] in
private lemma ne_zero_of_norm_eq_one {x : V} (h : ‖x‖ = 1) : x ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)

variable {x y z : V}
variable (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)

include hx hy

private lemma ortho_decomposition :
    x = Real.cos (angle x y) • y + ortho y x := by
  rw [← inner_eq_cos_angle_of_norm_eq_one hx hy, ← real_inner_comm x y, ortho_eq_sub_inner x hy]
  abel

private lemma norm_ortho_sq :
    ‖ortho y x‖ ^ 2 = 1 - ⟪x, y⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ortho_eq_sub_inner x hy]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x y, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, hx, hy,
    mul_one, one_pow, sq_abs]
  ring

private lemma norm_ortho_eq_sin_angle : ‖ortho y x‖ = Real.sin (angle x y) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sin_angle_nonneg x y
    (hx := ne_zero_of_norm_eq_one hx) (hy := ne_zero_of_norm_eq_one hy))).mp
  rw [norm_ortho_sq hx hy, inner_eq_cos_angle_of_norm_eq_one hx hy, Real.sin_sq]

lemma inner_ortho_right_eq_sin_angle {h : ortho y x ≠ 0} :
    ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have hh : ⟪x, ortho y x⟫ = ‖ortho y x‖ ^ 2 := by
    calc
      ⟪x, ortho y x⟫ =
          ⟪Real.cos (angle x y) • y + ortho y x, ortho y x⟫ :=
        congrArg (fun v : V ↦ ⟪v, ortho y x⟫) (ortho_decomposition hx hy)
      _ = _ := by
        rw [inner_add_left, real_inner_smul_left, inner_ortho_right, mul_zero, zero_add,
          real_inner_self_eq_norm_sq]
  rw [← norm_ortho_eq_sin_angle hx hy, NormedSpace.normalize, real_inner_smul_right, hh,
    pow_two, inv_mul_cancel_left₀]

lemma inner_normalized_ortho_sq_add_inner_sq_eq_one {h : ortho y x ≠ 0} :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [inner_ortho_right_eq_sin_angle hx hy (h := h),
    inner_eq_cos_angle_of_norm_eq_one hx hy, Real.sin_sq_add_cos_sq]

lemma angle_le_angle_add_angle_aux {h : ortho y x ≠ 0} :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalize (ortho y x) := by
  rw [← norm_ortho_eq_sin_angle hx hy, norm_smul_normalize (ortho y x) (hx := h)]
  exact ortho_decomposition hx hy

include hz in
private lemma inner_eq_cos_and_ortho :
    ⟪x, z⟫ = Real.cos (angle x y) * Real.cos (angle y z) + ⟪ortho y x, ortho y z⟫ := by
  have hx₀ := ne_zero_of_norm_eq_one hx
  have hy₀ := ne_zero_of_norm_eq_one hy
  have hz₀ := ne_zero_of_norm_eq_one hz
  have hzy := angle_comm z y (hx := hz₀) (hy := hy₀)
  have hdecz := (ortho_decomposition hz hy)
  rw [hzy] at hdecz
  have horth : ⟪ortho y x, y⟫ = 0 := (real_inner_comm y (ortho y x)).trans (inner_ortho_right x y)
  calc
    ⟪x, z⟫ = ⟪Real.cos (angle x y hx₀ hy₀) • y + ortho y x,
        Real.cos (angle y z hy₀ hz₀) • y + ortho y z⟫ :=
      congrArg₂ (inner ℝ) (ortho_decomposition hx hy) hdecz
    _ = _ := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        horth, inner_ortho_right, inner_self_eq_one_of_norm_eq_one hy, mul_one, mul_zero, zero_add,
        add_zero]
      ring

include hz in
lemma angle_le_angle_add_angle_of_norm_eq_one : angle x z ≤ angle x y + angle y z := by
  have hx₀ := ne_zero_of_norm_eq_one hx
  have hy₀ := ne_zero_of_norm_eq_one hy
  have hz₀ := ne_zero_of_norm_eq_one hz
  rcases lt_or_ge π (angle x y + angle y z) with hπ | hπ
  · exact (angle_le_pi x z (hx := hx₀) (hy := hz₀)).trans hπ.le
  have hn := add_nonneg (angle_nonneg x y (hx := hx₀) (hy := hy₀))
    (angle_nonneg y z (hx := hy₀) (hy := hz₀))
  apply (Real.strictAntiOn_cos.le_iff_ge ⟨hn, hπ⟩
    ⟨angle_nonneg x z (hx := hx₀) (hy := hz₀), angle_le_pi x z (hx := hx₀) (hy := hz₀)⟩).mp
  have hinner := (abs_le.mp (abs_real_inner_le_norm (ortho y x) (ortho y z))).1
  rw [norm_ortho_eq_sin_angle hx hy, norm_ortho_eq_sin_angle hz hy,
    angle_comm z y (hx := hz₀) (hy := hy₀)] at hinner
  rw [Real.cos_add, ← inner_eq_cos_angle_of_norm_eq_one hx hz,
    inner_eq_cos_and_ortho hx hy hz, sub_eq_add_neg]
  exact add_le_add_right hinner _

lemma ortho_ne_zero_of_not_collinear
    (hxy1 : angle x y (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hy) ≠ 0)
    (hxy2 : angle x y (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hy) ≠ π) :
    ortho x y ≠ 0 := by
  intro heq
  have hx₀ := ne_zero_of_norm_eq_one hx
  have hy₀ := ne_zero_of_norm_eq_one hy
  have hnorm : ‖ortho x y‖ = 0 := by rw [heq, norm_zero]
  have hsin : Real.sin (angle x y hx₀ hy₀) = 0 :=
    (congrArg Real.sin (angle_comm x y (hx := hx₀) (hy := hy₀))).trans
      ((norm_ortho_eq_sin_angle hy hx).symm.trans hnorm)
  rcases sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi.mp hsin with h₁ | h₂
  · exact hxy1 h₁
  · exact hxy2 h₂

lemma eq_of_angle_eq_zero (hxy : angle x y = 0) : x = y :=
  eq_of_angle_eq_zero_of_norm_eq hxy (hx.trans hy.symm)

include hz in
lemma angle_expression_of_angle_eq_angle_sum
    (_hπ : angle x z (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hz) ≠ π)
    (h : angle x z (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hz) =
      angle x y (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hy) +
        angle y z (ne_zero_of_norm_eq_one hy) (ne_zero_of_norm_eq_one hz)) :
    Real.sin (angle x z (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hz)) • y =
      Real.sin (angle y z (ne_zero_of_norm_eq_one hy) (ne_zero_of_norm_eq_one hz)) • x +
        Real.sin (angle x y (ne_zero_of_norm_eq_one hx) (ne_zero_of_norm_eq_one hy)) • z := by
  have hx₀ := ne_zero_of_norm_eq_one hx
  have hy₀ := ne_zero_of_norm_eq_one hy
  have hz₀ := ne_zero_of_norm_eq_one hz
  have hzy := angle_comm z y (hx := hz₀) (hy := hy₀)
  let α := angle x y hx₀ hy₀
  let β := angle y z hy₀ hz₀
  let a := Real.sin α
  let b := Real.sin β
  have ha : ‖ortho y x‖ = a := norm_ortho_eq_sin_angle hx hy
  have hb : ‖ortho y z‖ = b := by rw [norm_ortho_eq_sin_angle hz hy, hzy]
  have hpol := congrArg Real.cos h
  rw [Real.cos_add, ← inner_eq_cos_angle_of_norm_eq_one hx hz,
    inner_eq_cos_and_ortho hx hy hz] at hpol
  have hi : ⟪ortho y x, ortho y z⟫ = -(a * b) := by
    dsimp [a, b, α, β]
    linarith
  have hsum : ‖b • ortho y x + a • ortho y z‖ ^ 2 = 0 := by
    rw [norm_add_pow_two_real, norm_smul_of_nonneg (hb ▸ norm_nonneg _),
      norm_smul_of_nonneg (ha ▸ norm_nonneg _), real_inner_smul_left, real_inner_smul_right,
      ha, hb, hi]
    ring
  have hzero : b • ortho y x + a • ortho y z = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero] at hsum
    exact hsum
  have hzdec := ortho_decomposition hz hy
  rw [hzy] at hzdec
  calc
    _ = (b * Real.cos α + a * Real.cos β) • y := by
      rw [h, Real.sin_add]
      congr 1
      dsimp [a, b]
      ring
    _ = b • (Real.cos α • y + ortho y x) + a • (Real.cos β • y + ortho y z) := by
      rw [add_smul, mul_smul, mul_smul, smul_add, smul_add]
      rw [← add_zero (_ + _), ← hzero]
      abel
    _ = _ := by rw [← ortho_decomposition hx hy, ← hzdec]

end UnitVectorAngles


/-- **Triangle inequality** for angles between vectors. -/
public theorem angle_le_angle_add_angle (x y z : V) {hx : x ≠ 0} {hy : y ≠ 0} {hz : z ≠ 0} :
    angle x z ≤ angle x y + angle y z := by
  simpa using angle_le_angle_add_angle_of_norm_eq_one (norm_normalize x (hx := hx))
    (norm_normalize y (hx := hy)) (norm_normalize z (hx := hz))

/-- The triangle inequality is an equality if the middle vector is a nonnegative linear combination
of the other two vectors. See `angle_add_angle_eq_pi_of_angle_eq_pi` for the other equality case. -/
public theorem angle_eq_angle_add_add_angle_add_of_mem_span {x y z : V}
    {hx : x ≠ 0} {hz : z ≠ 0} (hy : y ≠ 0)
    (h_mem : y ∈ Submodule.span ℝ≥0 {x, z}) : angle x z = angle x y + angle y z := by
  rw [Submodule.mem_span_pair] at h_mem
  obtain ⟨kx, kz, rfl⟩ := h_mem
  rcases eq_zero_or_pos kx with rfl | hkx <;> rcases eq_zero_or_pos kz with rfl | hkz
  · simp at hy
  · have hkz' : 0 < (kz : ℝ) := by exact_mod_cast hkz
    simp only [zero_smul, zero_add, NNReal.smul_def]
    rw [angle_smul_right_of_pos x z hkz' (hx := hx) (hy := hz),
      angle_smul_left_of_pos z z hkz' (hx := hz) (hy := hz), angle_self (hx := hz), add_zero]
  · have hkx' : 0 < (kx : ℝ) := by exact_mod_cast hkx
    simp only [zero_smul, add_zero, NNReal.smul_def]
    rw [angle_smul_right_of_pos x x hkx' (hx := hx) (hy := hx),
      angle_smul_left_of_pos x z hkx' (hx := hx) (hy := hz), angle_self (hx := hx), zero_add]
  · have hkx' : 0 < (kx : ℝ) := by exact_mod_cast hkx
    have hkz' : 0 < (kz : ℝ) := by exact_mod_cast hkz
    have hx' := smul_ne_zero hkx'.ne' hx
    have hz' := smul_ne_zero hkz'.ne' hz
    have hsum : (kx : ℝ) • x + (kz : ℝ) • z ≠ 0 := hy
    have hangle := angle_eq_angle_add_add_angle_add ((kx : ℝ) • x)
      (hx := hx') (hy := hz') (hsum := hsum)
    rw [angle_smul_left_of_pos x _ hkx' (hx := hx) (hy := hz'),
      angle_smul_right_of_pos x z hkz' (hx := hx) (hy := hz),
      angle_smul_left_of_pos x _ hkx' (hx := hx) (hy := hsum),
      angle_smul_left_of_pos z _ hkz' (hx := hz) (hy := hsum),
      angle_comm z _ (hx := hz) (hy := hsum)] at hangle
    exact hangle

lemma mem_span_of_linear_combination {x y z : V} {kx ky kz : ℝ≥0} (hy : ky ≠ 0)
    (hlincomb : ky • y = kx • x + kz • z) : y ∈ Submodule.span ℝ≥0 {x, z} := by
  have h₁ : ky • y ∈ Submodule.span ℝ≥0 {x, z} := by
    rw [Submodule.mem_span_pair]; grind
  rwa [Submodule.smul_mem_iff _ hy] at h₁

/-- The triangle inequality on vectors `x`, `y`, `z` is an equality if and only if
`angle x z = π`, or `y` is a nonnegative linear combination of `x` and `z`. -/
public theorem angle_eq_angle_add_angle_iff {x y z : V}
    {hx : x ≠ 0} {hz : z ≠ 0} (hy : y ≠ 0) :
    angle x z = angle x y + angle y z ↔ angle x z = π ∨ y ∈ Submodule.span ℝ≥0 {x, z} := by
  constructor <;> rintro h
  · by_cases hxz₁ : angle x z = π
    · tauto
    right
    by_cases hxz₂ : angle x z = 0
    · have hxy : angle x y = 0 := by grind [angle_nonneg]
      rw [angle_eq_zero_iff] at hxy hxz₂
      obtain ⟨_, ⟨r2, ⟨hr2, rfl⟩⟩⟩ := hxy
      lift r2 to ℝ≥0 using hr2.le
      have hx_mem : x ∈ ({x, z} : Set V) := Set.mem_insert _ _
      exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem hx_mem)
    have h_sin_xz : Real.sin (angle x z) ≠ 0 := by
      grind [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]
    have hnneg₁ : 0 ≤ Real.sin (angle y z) / ‖x‖ :=
      div_nonneg (sin_angle_nonneg y z (hx := hy) (hy := hz)) (norm_nonneg x)
    have hnneg₂ : 0 ≤ Real.sin (angle x y) / ‖z‖ :=
      div_nonneg (sin_angle_nonneg x y (hx := hx) (hy := hy)) (norm_nonneg z)
    have hnneg₃ : 0 ≤ Real.sin (angle x z) / ‖y‖ :=
      div_nonneg (sin_angle_nonneg x z (hx := hx) (hy := hz)) (norm_nonneg y)
    have hnonzero : (⟨Real.sin (angle x z) / ‖y‖, hnneg₃⟩ : ℝ≥0) ≠ 0 := by
      intro heq
      have hcoe := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) heq
      exact h_sin_xz (div_eq_zero_iff.mp hcoe)
    have h₁ := angle_expression_of_angle_eq_angle_sum (norm_normalize x (hx := hx))
        (norm_normalize y (hx := hy)) (norm_normalize z (hx := hz))
    simp only [angle_normalize_right, angle_normalize_left] at h₁
    have h₂ := h₁ hxz₁ h
    have h₃ : (⟨_, hnneg₃⟩ : ℝ≥0) • y = (⟨_, hnneg₁⟩ : ℝ≥0) • x + (⟨_, hnneg₂⟩ : ℝ≥0) • z := by
      simp only [NormedSpace.normalize, ← smul_assoc, smul_eq_mul, Nonneg.mk_smul,
        div_eq_mul_inv₀] at h₂ ⊢
      exact h₂
    exact mem_span_of_linear_combination hnonzero h₃
  · obtain h | h := h
    · have hsum := angle_add_angle_eq_pi_of_angle_eq_pi y h (hz := hy)
      rw [angle_comm z y (hx := hz) (hy := hy)] at hsum
      exact h.trans hsum.symm
    · exact angle_eq_angle_add_add_angle_add_of_mem_span hy h

end InnerProductGeometry

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for angles in Euclidean geometry. -/
public theorem angle_le_angle_add_angle (p p₁ p₂ p₃ : P)
    {hp₁ : p₁ ≠ p} {hp₂ : p₂ ≠ p} {hp₃ : p₃ ≠ p} :
    ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_le_angle_add_angle _ _ _
    (hx := vsub_ne_zero.mpr hp₁) (hy := vsub_ne_zero.mpr hp₂) (hz := vsub_ne_zero.mpr hp₃)

end EuclideanGeometry

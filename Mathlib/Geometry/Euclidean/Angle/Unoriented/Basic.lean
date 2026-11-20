/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angles between vectors

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.
-/

@[expose] public section


assert_not_exists HasFDerivAt ConformalAt

noncomputable section

open Real Set

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

/-- The undirected angle between two nonzero vectors.
See `Orientation.oangle` for the corresponding oriented angle definition. -/
@[wikidata Q11352]
def angle (x y : V)
    (hx : x ≠ 0 := by
      first | checked_nonzero | (intro h; simp_all) | fail "a nonzero first vector is required")
    (hy : y ≠ 0 := by
      first | checked_nonzero | (intro h; simp_all) | fail "a nonzero second vector is required") :
    ℝ :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

theorem continuousAt_angle {x : {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0}} :
    ContinuousAt (fun y : {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0} ↦
      angle y.1.1 y.1.2 y.2.1 y.2.2) x := by
  unfold angle
  apply Real.continuous_arccos.continuousAt.comp
  exact ContinuousAt.div₀ (by fun_prop) (by fun_prop)

theorem angle_smul_smul {c : ℝ} (hc : c ≠ 0) (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    angle (c • x) (c • y) = angle x y := by
  have : c * c ≠ 0 := mul_ne_zero hc hc
  simp only [angle, real_inner_smul_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_mul_mul_comm |c| ‖x‖ |c| ‖y‖, abs_mul_abs_self, ← mul_assoc c c, mul_div_mul_left]

@[simp]
theorem _root_.LinearIsometry.angle_map {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (u v : E)
    {hu : u ≠ 0} {hv : v ≠ 0} :
    angle (f u) (f v) (fun h ↦ hu (f.injective (h.trans f.map_zero.symm)))
      (fun h ↦ hv (f.injective (h.trans f.map_zero.symm))) = angle u v := by
  simp only [angle, f.inner_map_map, f.norm_map]

@[simp, norm_cast]
theorem _root_.Submodule.angle_coe {s : Submodule ℝ V} (x y : s) {hx : x ≠ 0} {hy : y ≠ 0} :
    angle (x : V) (y : V) = angle x y :=
  s.subtypeₗᵢ.angle_map x y

/-- The cosine of the angle between two vectors. -/
theorem cos_angle (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
theorem angle_comm (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : angle x y = angle y x := by
  simp only [angle, real_inner_comm x y, mul_comm ‖x‖ ‖y‖]

/-- The angle between the negation of two vectors. -/
@[simp]
theorem angle_neg_neg (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : angle (-x) (-y) = angle x y := by
  simp only [angle, inner_neg_neg, norm_neg]

/-- The angle between two vectors is nonnegative. -/
theorem angle_nonneg (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : 0 ≤ angle x y :=
  Real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
theorem angle_le_pi (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : angle x y ≤ π :=
  Real.arccos_le_pi _

/-- The sine of the angle between two vectors is nonnegative. -/
theorem sin_angle_nonneg (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : 0 ≤ sin (angle x y) :=
  sin_nonneg_of_nonneg_of_le_pi (angle_nonneg x y) (angle_le_pi x y)

/-- The angle between a vector and the negation of another vector. -/
theorem angle_neg_right (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : angle x (-y) = π - angle x y := by
  simp only [angle, norm_neg, inner_neg_right, neg_div₀, Real.arccos_neg]

/-- The angle between the negation of a vector and another vector. -/
theorem angle_neg_left (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} : angle (-x) y = π - angle x y := by
  calc
    angle (-x) y = angle x (-y) := by simpa only [neg_neg] using angle_neg_neg x (-y)
    _ = π - angle x y := angle_neg_right x y

/-- The angle between a nonzero vector and itself. -/
@[simp]
theorem angle_self {x : V} {hx : x ≠ 0} : angle x x = 0 := by
  simp only [angle, real_inner_self_eq_norm_mul_norm, div_self, Real.arccos_one]

/-- The angle between a nonzero vector and its negation. -/
@[simp]
theorem angle_self_neg_of_nonzero {x : V} {hx : x ≠ 0} : angle x (-x) = π := by
  rw [angle_neg_right x x (hx := hx) (hy := hx), angle_self (hx := hx), sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp]
theorem angle_neg_self_of_nonzero {x : V} {hx : x ≠ 0} : angle (-x) x = π := by
  rw [angle_comm, angle_self_neg_of_nonzero]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_pos (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} {r : ℝ} (hr : 0 < r) :
    angle x (r • y) = angle x y := by
  simp only [angle, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mul_left_comm ‖x‖ r ‖y‖, mul_div_mul_left]

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_pos (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} {r : ℝ} (hr : 0 < r) :
    angle (r • x) y = angle x y := by
  rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_neg (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} {r : ℝ} (hr : r < 0) :
    angle x (r • y) = angle x (-y) := by
  simpa only [neg_smul, neg_neg, smul_neg] using
    angle_smul_right_of_pos x (-y) (neg_pos.mpr hr)

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_neg (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} {r : ℝ} (hr : r < 0) :
    angle (r • x) y = angle (-x) y := by
  exact (angle_comm (r • x) y).trans
    ((angle_smul_right_of_neg y x hr (hx := hy) (hy := hx)).trans (angle_comm y (-x)))

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem cos_angle_mul_norm_mul_norm (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ := by
  rw [cos_angle, div_mul_cancel₀]

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem sin_angle_mul_norm_mul_norm (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    Real.sin (angle x y) * (‖x‖ * ‖y‖) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
  unfold angle
  rw [Real.sin_arccos]
  nth_rw 2 [← Real.sqrt_sq (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [← Real.sqrt_mul' _ (by positivity), sq]
  simp only [real_inner_self_eq_norm_mul_norm]
  congr 1
  field_simp

/-- The sine of the angle between two vectors. -/
theorem sin_angle {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) :=
  (eq_div_iff (hb := (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)).isUnit)).2
    (sin_angle_mul_norm_mul_norm x y)

/-- The sine of the angle between `x` and `x + y`. -/
theorem sin_angle_add {x y : V} {hx : x ≠ 0} {hy : x + y ≠ 0} :
    Real.sin (angle x (x + y)) =
      √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖x + y‖) := by
  rw [sin_angle]
  field_simp
  simp only [inner_add_left, inner_add_right, real_inner_comm]
  ring_nf

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
theorem angle_eq_zero_iff {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    angle x y = 0 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, Real.arccos_eq_zero, LE.le.ge_iff_eq',
    eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
theorem angle_eq_pi_iff {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    angle x y = π ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, Real.arccos_eq_pi, LE.le.ge_iff_eq']
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} (z : V)
    {hz : z ≠ 0} (h : angle x y = π) : angle x z + angle y z = π := by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr (hx := hx) (hy := hz),
    angle_neg_left x z (hx := hx) (hy := hz)]
  abel

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    ⟪x, y⟫ = 0 ↔ angle x y = π / 2 := by
  rw [angle, Real.arccos_eq_pi_div_two, div_eq_zero_iff]

/-- The inner product of two vectors is nonpositive if and only if the angle between them is
at least `π / 2`. -/
theorem inner_nonpos_iff_pi_div_two_le_angle {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ⟪x, y⟫ ≤ 0 ↔ π / 2 ≤ angle x y := by
  rw [angle, Real.pi_div_two_le_arccos]
  refine ⟨fun h => div_nonpos_of_nonpos_of_nonneg h (by positivity), fun h => ?_⟩
  by_contra hpos
  push Not at hpos
  exact absurd h (not_le.2 (div_pos hpos (hpos.trans_le (real_inner_le_norm x y))))

/-- The inner product of two vectors is negative if and only if the angle between them exceeds
`π / 2`. -/
theorem inner_neg_iff_pi_div_two_lt_angle {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ⟪x, y⟫ < 0 ↔ π / 2 < angle x y := by
  rw [angle, Real.pi_div_two_lt_arccos]
  refine ⟨fun h => div_neg_of_neg_of_pos h (mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)), ?_⟩
  · intro h
    by_contra hnonneg
    push Not at hnonneg
    exact absurd h (not_lt.2 (div_nonneg hnonneg (by positivity)))

/-- If the angle between two vectors is π, the inner product equals the negative product
of the norms. -/
theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = π) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  rw [← cos_angle_mul_norm_mul_norm x y (hx := hx) (hy := hy), h, cos_pi, neg_one_mul]

/-- If the angle between two vectors is 0, the inner product equals the product of the norms. -/
theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  rw [← cos_angle_mul_norm_mul_norm x y (hx := hx) (hy := hy), h, cos_zero, one_mul]

/-- The inner product of two non-zero vectors equals the negative product of their norms
if and only if the angle between the two vectors is π. -/
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) ↔ angle x y = π := by
  refine ⟨fun h => ?_, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, neg_div₀, div_self, Real.arccos_neg_one]

/-- The inner product of two non-zero vectors equals the product of their norms
if and only if the angle between the two vectors is 0. -/
theorem inner_eq_mul_norm_iff_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ angle x y = 0 := by
  refine ⟨fun h => ?_, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, div_self, Real.arccos_one]

/-- If the angle between two vectors is π, the norm of their difference equals
the sum of their norms. -/
theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = π) :
    ‖x - y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

/-- If the angle between two vectors is 0, the norm of their sum equals
the sum of their norms. -/
theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h]
  ring

/-- If the angle between two vectors is 0, the norm of their difference equals
the absolute value of the difference of their norms. -/
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (h : angle x y = 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖)), norm_sub_pow_two_real,
    inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (‖x‖ - ‖y‖)]
  ring

/-- The norm of the difference of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is π. -/
theorem norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x - y‖ = ‖x‖ + ‖y‖ ↔ angle x y = π := by
  refine ⟨fun h => ?_, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq₀ hxy₁ hxy₂, norm_sub_pow_two_real] at h
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - (‖x‖ + ‖y‖) ^ 2) / 2 := by linarith
    _ = -(‖x‖ * ‖y‖) := by ring

/-- The norm of the sum of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is 0. -/
theorem norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔ angle x y = 0 := by
  refine ⟨?_, norm_add_eq_add_norm_of_angle_eq_zero⟩
  grind [inner_eq_mul_norm_iff_angle_eq_zero, norm_add_pow_two_real]

/-- The norm of the difference of two non-zero vectors equals the absolute value
of the difference of their norms if and only the angle between the two vectors is 0. -/
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x - y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0 := by
  refine ⟨fun h => ?_, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero]
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring

/-- The norm of the sum of two vectors equals the norm of their difference if and only if
the angle between them is π/2. -/
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (norm_nonneg (x - y)),
    ← inner_eq_zero_iff_angle_eq_pi_div_two x y, norm_add_pow_two_real, norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

/-- The cosine of the angle between two vectors is 1 if and only if the angle is 0. -/
theorem cos_eq_one_iff_angle_eq_zero {hx : x ≠ 0} {hy : y ≠ 0} :
    cos (angle x y) = 1 ↔ angle x y = 0 := by
  rw [← cos_zero]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)

/-- The cosine of the angle between two vectors is 0 if and only if the angle is π / 2. -/
theorem cos_eq_zero_iff_angle_eq_pi_div_two {hx : x ≠ 0} {hy : y ≠ 0} :
    cos (angle x y) = 0 ↔ angle x y = π / 2 := by
  rw [← cos_pi_div_two]
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]

/-- The cosine of the angle between two vectors is -1 if and only if the angle is π. -/
theorem cos_eq_neg_one_iff_angle_eq_pi {hx : x ≠ 0} {hy : y ≠ 0} :
    cos (angle x y) = -1 ↔ angle x y = π := by
  rw [← cos_pi]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)

/-- The sine of the angle between two vectors is 0 if and only if the angle is 0 or π. -/
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {hx : x ≠ 0} {hy : y ≠ 0} :
    sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π := by
  rw [sin_eq_zero_iff_cos_eq, cos_eq_one_iff_angle_eq_zero, cos_eq_neg_one_iff_angle_eq_pi]

/-- The sine of the angle between two vectors is 1 if and only if the angle is π / 2. -/
theorem sin_eq_one_iff_angle_eq_pi_div_two {hx : x ≠ 0} {hy : y ≠ 0} :
    sin (angle x y) = 1 ↔ angle x y = π / 2 := by
  refine ⟨fun h => ?_, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two, ← abs_eq_zero, abs_cos_eq_sqrt_one_sub_sin_sq, h]
  simp

/-- If the angle between two vectors of equal norm is equal to 0, then the vectors are equal. -/
lemma eq_of_angle_eq_zero_of_norm_eq {x y : V} {hx : x ≠ 0} {hy : y ≠ 0}
    (hxy : angle x y = 0) (h : ‖x‖ = ‖y‖) : x = y := by
  obtain ⟨_, r, hr, rfl⟩ := angle_eq_zero_iff.mp hxy
  have hnorm : r * ‖x‖ = 1 * ‖x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, one_mul] using h.symm
  rw [mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) hnorm, one_smul]

/-- The angle between a normalized vector and another vector is equal to the angle
between the original vectors. -/
@[simp]
lemma angle_normalize_left (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    angle (NormedSpace.normalize x) y = angle x y := by
  simpa only [NormedSpace.normalize] using
    angle_smul_left_of_pos x y (hx := hx) (hy := hy) (inv_pos.mpr (norm_pos_iff.mpr hx))

/-- The angle between a vector and another normalized vector is equal to the angle
between the original vectors. -/
@[simp]
lemma angle_normalize_right (x y : V) {hx : x ≠ 0} {hy : y ≠ 0} :
    angle x (NormedSpace.normalize y) = angle x y := by
  rw [angle_comm, angle_normalize_left, angle_comm]

/-- The inner product of two unit vectors is equal to the cosine of the angle between them. -/
lemma inner_eq_cos_angle_of_norm_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = Real.cos (angle x y
      (by intro h; simp [h] at hx) (by intro h; simp [h] at hy)) := by
  simp [cos_angle, hx, hy]

end InnerProductGeometry

/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Projection

/-!
# Angle bisectors.

This file proves lemmas relating to bisecting angles.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

private lemma cos_angle_orthogonalProjection_mul_dist {p p' : P} {s : AffineSubspace ℝ P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] (hp' : p' ∈ s) (hp : p ≠ p')
    (hq : (orthogonalProjection s p : P) ≠ p') :
    Real.cos (angle p p' (orthogonalProjection s p) hp hq) * dist p p' =
      dist p' (orthogonalProjection s p) := by
  let q : P := orthogonalProjection s p
  change Real.cos (angle p p' q hp hq) * dist p p' = dist p' q
  rw [dist_comm p' q, dist_eq_norm_vsub V p p', dist_eq_norm_vsub V q p']
  apply mul_right_cancel₀ (norm_ne_zero_iff.2 (vsub_ne_zero.2 hq))
  rw [mul_assoc, angle, InnerProductGeometry.cos_angle_mul_norm_mul_norm,
    ← real_inner_self_eq_norm_mul_norm]
  have ho : inner ℝ (p' -ᵥ q) (q -ᵥ p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p hp')
      (orthogonalProjection_vsub_mem_direction_orthogonal s p)
  have ho' : inner ℝ (p -ᵥ q) (q -ᵥ p') = 0 := calc
    _ = inner ℝ (q -ᵥ p') (p -ᵥ q) := real_inner_comm _ _
    _ = inner ℝ (p' -ᵥ q) (q -ᵥ p) := by
      rw [← neg_vsub_eq_vsub_rev p' q, ← neg_vsub_eq_vsub_rev q p, inner_neg_neg]
    _ = 0 := ho
  rw [← vsub_add_vsub_cancel p q p', inner_add_left, ho', zero_add]

/-- A point `p` is equidistant to two affine subspaces if and only if the angles at a point `p'`
in their intersection between `p` and its orthogonal projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    ∀ (hp : p ≠ p') (hq₁ : (orthogonalProjection s₁ p : P) ≠ p')
      (hq₂ : (orthogonalProjection s₂ p : P) ≠ p'),
      dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
        angle p p' (orthogonalProjection s₁ p) hp hq₁ =
          angle p p' (orthogonalProjection s₂ p) hp hq₂ := by
  intro hp hq₁ hq₂
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  let q₁ : P := orthogonalProjection s₁ p
  let q₂ : P := orthogonalProjection s₂ p
  have hpy₁ := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p hp'₁
  have hpy₂ := dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p hp'₂
  have hlegs : dist p q₁ = dist p q₂ ↔ dist p' q₁ = dist p' q₂ := by
    change dist p' p * dist p' p =
      dist p' q₁ * dist p' q₁ + dist p q₁ * dist p q₁ at hpy₁
    change dist p' p * dist p' p =
      dist p' q₂ * dist p' q₂ + dist p q₂ * dist p q₂ at hpy₂
    constructor <;> intro heq <;> rw [heq] at hpy₁ <;>
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).1 <;> nlinarith only [hpy₁, hpy₂]
  have hcos₁ := cos_angle_orthogonalProjection_mul_dist hp'₁ hp hq₁
  have hcos₂ := cos_angle_orthogonalProjection_mul_dist hp'₂ hp hq₂
  change dist p q₁ = dist p q₂ ↔ angle p p' q₁ hp hq₁ = angle p p' q₂ hp hq₂
  rw [hlegs]
  constructor
  · intro h
    apply Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    apply mul_right_cancel₀ (dist_ne_zero.2 hp)
    rw [hcos₁, hcos₂, h]
  · intro h
    rw [← hcos₁, ← hcos₂, h]

section Oriented

open Module

variable [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if the oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have hp : p ≠ p' := by
    rintro rfl
    exact hp₁ (orthogonalProjection_eq_self_iff.2 hp'₁)
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂ hp hp₁ hp₂, angle_comm,
    angle_eq_iff_oangle_eq_or_wbtw hp₁ (hp₃ := hp) hp₂]
  exact .inl h

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- The oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto two affine subspaces (typically lines, for this version of the lemma) are equal
if `p` is equidistant to the two subspaces. -/
lemma oangle_eq_of_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) →
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  intro hne h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  have : Nonempty (s₁ ⊓ s₂ : AffineSubspace ℝ P) := ⟨p', hp'₁, hp'₂⟩
  have hp₁ : orthogonalProjection s₁ p ≠ p' := by
    intro hp
    rw [hp, eq_comm, dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₂] at h
    grind
  have hp₂ : orthogonalProjection s₂ p ≠ p' := by
    intro hp
    rw [hp, dist_orthogonalProjection_eq_dist_iff_eq_of_mem hp'₁] at h
    grind
  have hp : p ≠ p' := by
    rintro rfl
    exact hp₁ (orthogonalProjection_eq_self_iff.2 hp'₁)
  have hc : ¬ Collinear ℝ {p', (orthogonalProjection s₁ p : P),
      (orthogonalProjection s₂ p : P)} := by
    intro hc
    have h₁ :
        (orthogonalProjection s₁ p : P) ∈ affineSpan ℝ {p', (orthogonalProjection s₂ p : P)} :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₁' : (orthogonalProjection s₁ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨orthogonalProjection_mem _,
        SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₂ (orthogonalProjection_mem _)) h₁⟩
    have h₁'' : (orthogonalProjection s₁ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_left, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    have h₂ :
        (orthogonalProjection s₂ p : P) ∈ affineSpan ℝ {p', (orthogonalProjection s₁ p : P)} :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₂' : (orthogonalProjection s₂ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'₁ (orthogonalProjection_mem _)) h₂,
        orthogonalProjection_mem _⟩
    have h₂'' : (orthogonalProjection s₂ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_right, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    apply hne
    rw [h₁'', h₂'']
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂ hp hp₁ hp₂, angle_comm,
    angle_eq_iff_oangle_eq_or_wbtw hp₁ (hp₃ := hp) hp₂] at h
  rcases h with h | h | h
  · exact h
  · exfalso
    exact hc h.collinear
  · exfalso
    have h' := h.collinear
    rw [Set.pair_comm] at h'
    exact hc h'

-- See https://github.com/leanprover/lean4/issues/11182 for why hypotheses are after the colon.
/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if and only if the oriented angles at a point `p'` in their intersection between `p` and
its orthogonal projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_iff_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p →
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    (dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p)) :=
  fun hne hp₁ hp₂ ↦ ⟨oangle_eq_of_dist_orthogonalProjection_eq hp'₁ hp'₂ hne,
    dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂⟩

private lemma mem_of_two_zsmul_oangle_orthogonalProjection_eq_zero
    {p p' : P} {s : AffineSubspace ℝ P} [Nonempty s] [s.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s) (hq : (orthogonalProjection s p : P) ≠ p')
    (h : (2 : ℤ) • ∡ p p' (orthogonalProjection s p : P) = 0) : p ∈ s := by
  have hcol := oangle_eq_zero_or_eq_pi_iff_collinear.mp (Real.Angle.two_zsmul_eq_zero_iff.mp h)
  exact SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp' (orthogonalProjection_mem p))
    (hcol.mem_affineSpan_of_mem_of_ne (p₁ := p') (p₂ := (orthogonalProjection s p : P))
      (p₃ := p) (by simp) (by simp) (by simp) hq.symm)

/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if twice the oriented angles at a point `p'` in their intersection between `p` and its
orthogonal projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P} (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'₁⟩
    haveI : Nonempty s₂ := ⟨p', hp'₂⟩
    -- after the colon as these need the `haveI`s above
    orthogonalProjection s₁ p ≠ p' →
    orthogonalProjection s₂ p ≠ p' →
    (2 : ℤ) • ∡ (orthogonalProjection s₁ p : P) p' p =
      (2 : ℤ) • ∡ p p' (orthogonalProjection s₂ p) →
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  intro hp₁ hp₂ h
  have : Nonempty s₁ := ⟨p', hp'₁⟩
  have : Nonempty s₂ := ⟨p', hp'₂⟩
  by_cases hs₁ : p ∈ s₁
  · have hzero : (2 : ℤ) • ∡ p p' (orthogonalProjection s₂ p : P) = 0 := by
      simpa only [orthogonalProjection_eq_self_iff.2 hs₁, oangle_self_left_right, smul_zero]
        using h.symm
    have hs₂ := mem_of_two_zsmul_oangle_orthogonalProjection_eq_zero hp'₂ hp₂ hzero
    simp [orthogonalProjection_eq_self_iff.2 hs₁, orthogonalProjection_eq_self_iff.2 hs₂]
  by_cases hs₂ : p ∈ s₂
  · have hzero : (2 : ℤ) • ∡ (orthogonalProjection s₁ p : P) p' p = 0 := by
      simpa only [orthogonalProjection_eq_self_iff.2 hs₂, oangle_self_left_right, smul_zero]
        using h
    rw [oangle_rev p p' (orthogonalProjection s₁ p : P), smul_neg, neg_eq_zero] at hzero
    have hs₁' := mem_of_two_zsmul_oangle_orthogonalProjection_eq_zero hp'₁ hp₁ hzero
    simp [orthogonalProjection_eq_self_iff.2 hs₁', orthogonalProjection_eq_self_iff.2 hs₂]
  have h' : ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) :=
    oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two h
      (angle_self_orthogonalProjection _ hp'₁ hs₁ hp₁.symm)
      (angle_self_orthogonalProjection _ hp'₂ hs₂ hp₂.symm)
  exact dist_orthogonalProjection_eq_of_oangle_eq hp'₁ hp'₂ hp₁ hp₂ h'

/-- Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal projection of `p`
to the line `p₁ p₂` is `p₁`. -/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ ≠ p₂) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃)
    (h' : orthogonalProjection (affineSpan ℝ {p₁, p₂}) p = p₁) :
    dist p (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p) =
      dist p (orthogonalProjection (affineSpan ℝ {p₁, p₃}) p) := by
  obtain rfl | hp := eq_or_ne p p₁
  · rw [h', dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    exact left_mem_affineSpan_pair _ _ _
  · rw [← h'] at h hp
    have hpm : p ∉ affineSpan ℝ {p₁, p₂} := orthogonalProjection_eq_self_iff.not.1 (Ne.symm hp)
    rw [two_zsmul_oangle_orthogonalProjection_self _ hpm (right_mem_affineSpan_pair _ _ _)
          (h'.symm ▸ h₂.symm), eq_comm, oangle, Real.Angle.two_zsmul_eq_pi_iff, h'] at h
    replace h := (Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero _).1 (.inr (.inr h))
    congr 1
    rw [h', eq_comm, coe_orthogonalProjection_eq_iff_mem]
    refine ⟨left_mem_affineSpan_pair _ _ _, ?_⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [direction_affineSpan, mem_vectorSpan_pair] at hu
    rcases hu with ⟨r, rfl⟩
    rw [inner_smul_right, ← inner_neg_neg, inner_neg_left]
    simp [h]

/-- Auxiliary lemma for the special case of
`dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq` where the orthogonal projection of `p`
to the line `p₁ p₂` or `p₁ p₃` is `p₁`. -/
private lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ {p p₁ p₂ p₃ : P}
    (h₂ : p₁ ≠ p₂) (h₃ : p₁ ≠ p₃) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃)
    (h' : orthogonalProjection (affineSpan ℝ {p₁, p₂}) p = p₁ ∨
      orthogonalProjection (affineSpan ℝ {p₁, p₃}) p = p₁) :
    dist p (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p) =
      dist p (orthogonalProjection (affineSpan ℝ {p₁, p₃}) p) := by
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₂ h h'
  · refine (dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₁ h₃ ?_ h').symm
    rw [oangle_rev, smul_neg, ← h, oangle_rev, smul_neg, neg_neg]

/-- A point `p` is equidistant to two lines `p₁ p₂` and `p₁ p₃` if the oriented angles at `p₁`
are equal modulo `π`. -/
lemma dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} (h₂ : p₁ ≠ p₂)
    (h₃ : p₁ ≠ p₃) (h : (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃) :
    dist p (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p) =
      dist p (orthogonalProjection (affineSpan ℝ {p₁, p₃}) p) := by
  by_cases h' : orthogonalProjection (affineSpan ℝ {p₁, p₂}) p = p₁ ∨
      orthogonalProjection (affineSpan ℝ {p₁, p₃}) p = p₁
  · exact dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq_aux₂ h₂ h₃ h h'
  · rw [not_or] at h'
    refine dist_orthogonalProjection_eq_of_two_zsmul_oangle_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) h'.1 h'.2 ?_
    rw [(collinear_insert_of_mem_affineSpan_pair
          (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left h'.1 h₂.symm,
      (collinear_insert_of_mem_affineSpan_pair
        (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right h'.2 h₃.symm, h]

/-- If a point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃`, the oriented angles
at `p₁` are equal modulo `π`. -/
lemma two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent ℝ ![p₁, p₂, p₃])
    (h : dist p (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p) =
      dist p (orthogonalProjection (affineSpan ℝ {p₁, p₃}) p)) :
    (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃ := by
  by_cases ho : (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p : P) =
      orthogonalProjection (affineSpan ℝ {p₁, p₃}) p
  · suffices p = p₁ by simp [this]
    have hs := orthogonalProjection_sup_of_orthogonalProjection_eq ho
    have hinf : affineSpan ℝ {p₁, p₂} ⊓ affineSpan ℝ {p₁, p₃} = affineSpan ℝ {p₁} := by
      convert! (ha.inf_affineSpan_eq_affineSpan_inter {0, 1} {0, 2})
      · simp
      · simp
      · suffices {p₁} = ![p₁, p₂, p₃] '' {0} by grind
        simp
    have hsup : affineSpan ℝ {p₁, p₂} ⊔ affineSpan ℝ {p₁, p₃} = ⊤ := by
      rw [← AffineSubspace.span_union]
      convert! ha.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 ?_
      · simp
        grind
      · simpa using Fact.out
    have hp : orthogonalProjection (affineSpan ℝ {p₁, p₂}) p = p₁ := by
      suffices (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p : P) ∈ affineSpan ℝ {p₁} by
        simpa using this
      have hi : (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p : P) ∈
          affineSpan ℝ {p₁, p₂} ⊓ affineSpan ℝ {p₁, p₃} :=
        ⟨orthogonalProjection_mem _, ho ▸ orthogonalProjection_mem _⟩
      rwa [hinf] at hi
    rw [← orthogonalProjection_sup_of_orthogonalProjection_eq ho] at hp
    rw [← hp, eq_comm, orthogonalProjection_eq_self_iff, hsup]
    exact AffineSubspace.mem_top ℝ V p
  · have hp := oangle_eq_of_dist_orthogonalProjection_eq
      (left_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _) ho h
    have h₂₁ : p₂ ≠ p₁ := ha.injective.ne (by decide : (1 : Fin 3) ≠ 0)
    have h₃₁ : p₃ ≠ p₁ := ha.injective.ne (by decide : (2 : Fin 3) ≠ 0)
    have hp₁ : orthogonalProjection (affineSpan ℝ {p₁, p₂}) p ≠ p₁ := by
      intro hp
      rw [hp, eq_comm, dist_orthogonalProjection_eq_dist_iff_eq_of_mem
        (left_mem_affineSpan_pair ℝ _ p₃)] at h
      grind
    have hp₂ : orthogonalProjection (affineSpan ℝ {p₁, p₃}) p ≠ p₁ := by
      intro hp
      rw [hp, dist_orthogonalProjection_eq_dist_iff_eq_of_mem
          (left_mem_affineSpan_pair ℝ _ p₂)] at h
      grind
    rw [← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_left hp₁ h₂₁,
        ← (collinear_insert_of_mem_affineSpan_pair
             (orthogonalProjection_mem p)).two_zsmul_oangle_eq_right hp₂ h₃₁, hp]

/-- A point `p` is equidistant to two different lines `p₁ p₂` and `p₁ p₃` if and only if the
oriented angles at `p₁` are equal modulo `π`. -/
lemma dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P}
    (ha : AffineIndependent ℝ ![p₁, p₂, p₃]) :
    dist p (orthogonalProjection (affineSpan ℝ {p₁, p₂}) p) =
      dist p (orthogonalProjection (affineSpan ℝ {p₁, p₃}) p) ↔
        (2 : ℤ) • ∡ p₂ p₁ p = (2 : ℤ) • ∡ p p₁ p₃ :=
  ⟨two_zsmul_oangle_eq_of_dist_orthogonalProjection_line_eq ha,
    dist_orthogonalProjection_line_eq_of_two_zsmul_oangle_eq
      (ha.injective.ne (by decide : (0 : Fin 3) ≠ 1))
      (ha.injective.ne (by decide : (0 : Fin 3) ≠ 2))⟩

end Oriented

end EuclideanGeometry

/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! # Continuous linear maps with a continuous left/right inverse

This file defines continuous linear maps which admit a continuous left/right inverse.

We prove that both of these classes of maps are closed under products and composition and contain
linear equivalences. A continuous left inverse also splits the range: if `f` admits a continuous
left inverse, then its range is closed and admits a closed complement. This is used to extract a
complement from immersions, for use in the regular value theorem. (For submersions, there is a
natural choice of complement, and an analogous statement is not necessary.)

A continuous left inverse of `f` is determined by `f` only on the range of `f`, and a continuous
right inverse only up to the kernel of `f`, so none is chosen here. A topological complement of the
range determines the continuous left inverse vanishing on it, and a topological complement of the
kernel determines the continuous right inverse with values in it; every continuous left inverse
vanishes on its kernel, a topological complement of the range, and every continuous right inverse
takes values in its range, a topological complement of the kernel.

This concept is used to give an equivalent definition of immersions and submersions of manifolds.
Sufficient criteria in finite dimension and between Banach spaces are in
`Mathlib/Analysis/Normed/Module/ContinuousInverse.lean`.

## Main definitions and results

* `ContinuousLinearMap.HasLeftInverse`: a continuous linear map admits a left inverse
  which is a continuous linear map itself
* `ContinuousLinearMap.HasRightInverse`: a continuous linear map admits a right inverse
  which is a continuous linear map itself

* `ContinuousLinearMap.HasLeftInverse.isClosed_range`: if `f` has a continuous left inverse,
  its range is closed
* `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`: if `f` has a continuous left
  inverse, its range admits a closed complement
* `ContinuousLinearMap.HasLeftInverse.leftInverseOfIsTopCompl`: the continuous left inverse of `f`
  vanishing on a topological complement of its range; `eq_leftInverseOfIsTopCompl` shows that it is
  the only left inverse vanishing there
* `ContinuousLinearMap.HasRightInverse.rightInverseOfIsTopCompl`: the continuous right inverse of
  `f` with values in a topological complement of its kernel; `eq_rightInverseOfIsTopCompl` shows
  that it is the only right inverse with values there

* `ContinuousLinearEquiv.hasLeftInverse` and `ContinuousLinearEquiv.hasRightInverse`:
  a continuous linear equivalence admits a continuous left (resp. right) inverse
* `ContinuousLinearMap.HasLeftInverse.comp`, `ContinuousLinearMap.HasRightInverse.comp`:
  if `f : E → F` and `g : F → G` both admit a continuous left (resp. right) inverse,
  so does `g.comp f`.
* `ContinuousLinearMap.HasLeftInverse.of_comp`, `ContinuousLinearMap.HasRightInverse.of_comp`:
  suppose `f : E → F` and `g : F → G` are continuous linear maps.
  If `g.comp f : E → G` admits a continuous left inverse, then so does `f`.
  If `g.comp f : E → G` admits a continuous right inverse, then so does `g`.
* `ContinuousLinearMap.HasLeftInverse.prodMap`, `ContinuousLinearMap.HasRightInverse.prodMap`:
  having a continuous left/right inverse is closed under taking products
* `ContinuousLinearMap.HasLeftInverse.inl`, `ContinuousLinearMap.HasLeftInverse.inr`:
  `ContinuousLinearMap.inl` and `.inr` have a continuous left inverse
* `ContinuousLinearMap.HasRightInverse.fst`, `ContinuousLinearMap.HasRightInverse.snd`:
  `ContinuousLinearMap.fst` and `.snd` have a continuous right inverse
-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/-- A continuous linear map admits a left inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasLeftInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, LeftInverse g f

/-- A continuous linear map admits a right inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasRightInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, RightInverse g f

namespace ContinuousLinearMap

namespace HasLeftInverse

variable {f : E →L[R] F}

lemma injective (h : f.HasLeftInverse) : Injective f := by
  obtain ⟨g, hg⟩ := h
  exact hg.injective

lemma congr {g : E →L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) :
    g.HasLeftInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous left inverse. -/
lemma _root_.ContinuousLinearEquiv.hasLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/-- An invertible continuous linear map has a continuous left inverse. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasLeftInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasLeftInverse

/-- If `f` and `g` admit continuous left inverses, so does `f × g`. -/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse) :
    (f.prodMap g).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

lemma comp {g : F →L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) :
    (g.comp f).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [comp_apply]
  rw [hginv, hfinv]

lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasLeftInverse) :
    f.HasLeftInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y ↦ ?_⟩
  simp only [comp_apply]
  exact hfginv y

lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse) :
    (f.comp f₀.toContinuousLinearMap).HasLeftInverse :=
  hf.comp f₀.hasLeftInverse

lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasLeftInverse) :
    (g.toContinuousLinearMap.comp f).HasLeftInverse :=
  g.hasLeftInverse.comp hf

/-- `ContinuousLinearMap.inl` has a continuous left inverse. -/
protected lemma inl : (ContinuousLinearMap.inl R F G).HasLeftInverse := by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp

/-- `ContinuousLinearMap.inr` has a continuous left inverse. -/
protected lemma inr : (ContinuousLinearMap.inr R F G).HasLeftInverse := by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp

/-! An equivalent characterisation of maps with a continuous left inverse -/
section Ring

-- The next lemmas assume we are working over a ring.
variable {R E F : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] {f : E →L[R] F}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` has a continuous left inverse, its range admits a closed complement. -/
lemma closedComplemented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range := by
  -- Idea of proof: let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f.
  -- Mathlib's definition of closed complement takes a continuous projection to f.range instead
  -- of a complementary subspace: consider `f.comp g` instead, which is continuous as both maps are,
  -- and idempotent as a continuous left inverse.
  obtain ⟨g, hg⟩ := hf
  use (f.comp g).codRestrict f.range (by intro y; simp)
  rintro ⟨y, x, rfl⟩
  ext
  simp only [coe_coe, coe_codRestrict_apply, comp_apply]
  rw [hg]

section

variable [T1Space F]

lemma isClosed_range (hf : f.HasLeftInverse) [IsTopologicalAddGroup F] :
    IsClosed (range f) := by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  obtain ⟨g, hg⟩ := hf
  rw [← f.range_toLinearMap, ← f.coe_range, f.range_eq_ker_of_leftInverse hg]
  exact ((f.comp g) - (ContinuousLinearMap.id R F)).isClosed_ker

end

/-- The continuous left inverse of `f` vanishing on a topological complement `C` of the range of
`f`: the projection onto the range along `C`, followed by the inverse of `f` on its range. It is the
left inverse `LinearMap.linearProjOfIsCompl` of the underlying linear map, which is continuous
because it is the composition of any continuous left inverse with the continuous projection. -/
def leftInverseOfIsTopCompl (hf : f.HasLeftInverse) {C : Submodule R F}
    (hC : f.range.IsTopCompl C) : F →L[R] E where
  toLinearMap := LinearMap.linearProjOfIsCompl C (f : E →ₗ[R] F) hf.injective hC.isCompl
  cont := by
    obtain ⟨g, hg⟩ := id hf
    have : LinearMap.linearProjOfIsCompl C (f : E →ₗ[R] F) hf.injective hC.isCompl =
        ((g ∘L f.range.subtypeL ∘L f.range.projectionOntoL C hC :
          F →L[R] E) : F →ₗ[R] E) :=
      (LinearMap.eq_linearProjOfIsCompl _ _ _ _
        (fun x ↦ by
          simp [Submodule.projection_apply_of_mem_left hC.isCompl (x := f x) ⟨x, rfl⟩, hg x])
        fun x hx ↦ by simp [Submodule.projection_apply_of_mem_right hC.isCompl hx]).symm
    rw [this]
    exact (g ∘L f.range.subtypeL ∘L f.range.projectionOntoL C hC).continuous

@[simp]
lemma leftInverseOfIsTopCompl_apply (hf : f.HasLeftInverse) {C : Submodule R F}
    (hC : f.range.IsTopCompl C) (x : E) :
    hf.leftInverseOfIsTopCompl hC (f x) = x :=
  LinearMap.linearProjOfIsCompl_apply_left C (f : E →ₗ[R] F) hf.injective hC.isCompl x

lemma leftInverse_leftInverseOfIsTopCompl (hf : f.HasLeftInverse) {C : Submodule R F}
    (hC : f.range.IsTopCompl C) : LeftInverse (hf.leftInverseOfIsTopCompl hC) f :=
  hf.leftInverseOfIsTopCompl_apply hC

lemma leftInverseOfIsTopCompl_apply_of_mem (hf : f.HasLeftInverse) {C : Submodule R F}
    (hC : f.range.IsTopCompl C) {y : F} (hy : y ∈ C) :
    hf.leftInverseOfIsTopCompl hC y = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' C (f : E →ₗ[R] F) hf.injective hC.isCompl y hy

/-- The continuous left inverse of `f` vanishing on a topological complement of its range is the
only left inverse of `f` vanishing there. -/
lemma eq_leftInverseOfIsTopCompl (hf : f.HasLeftInverse) {C : Submodule R F}
    (hC : f.range.IsTopCompl C) {g : F →L[R] E} (hg : LeftInverse g f)
    (hgC : ∀ y ∈ C, g y = 0) : g = hf.leftInverseOfIsTopCompl hC :=
  ContinuousLinearMap.coe_injective <|
    LinearMap.eq_linearProjOfIsCompl C (f : E →ₗ[R] F) hf.injective hC.isCompl hg hgC

/-- Every continuous left inverse `g` of `f` is the left inverse vanishing on its kernel, which is a
topological complement of the range of `f`. -/
lemma eq_leftInverseOfIsTopCompl_ker {g : F →L[R] E} (hg : LeftInverse g f) :
    g = HasLeftInverse.leftInverseOfIsTopCompl ⟨g, hg⟩
      (f.isTopCompl_range_ker_of_leftInverse g hg) :=
  eq_leftInverseOfIsTopCompl _ _ hg fun _ hy ↦ by simpa using hy

end Ring

end HasLeftInverse

namespace HasRightInverse

variable {f : E →L[R] F}

lemma surjective (h : f.HasRightInverse) : Surjective f := by
  obtain ⟨g, hg⟩ := h
  exact hg.surjective

lemma congr {g : E →L[R] F} (hf : f.HasRightInverse) (hfg : g = f) :
    g.HasRightInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous right inverse. -/
lemma _root_.ContinuousLinearEquiv.hasRightInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasRightInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/-- An invertible continuous linear map has a continuous right inverse. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasRightInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasRightInverse

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInverse) :
    (f.prodMap g).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

lemma comp {g : F →L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) :
    (g.comp f).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [comp_apply]
  rw [hfinv, hginv]

lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasRightInverse) :
    g.HasRightInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y ↦ by simpa using hfginv y⟩

lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse) :
    (f.comp f₀.toContinuousLinearMap).HasRightInverse :=
  hf.comp f₀.hasRightInverse

lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasRightInverse) :
    (g.toContinuousLinearMap.comp f).HasRightInverse :=
  g.hasRightInverse.comp hf

/-- `ContinuousLinearMap.fst` has a continuous right inverse. -/
protected lemma fst : (ContinuousLinearMap.fst R F G).HasRightInverse := by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp

/-- `ContinuousLinearMap.snd` has a continuous right inverse. -/
protected lemma snd : (ContinuousLinearMap.snd R F G).HasRightInverse := by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp

section Ring

variable {R E F : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] {f : E →L[R] F}

/-- The restriction of a surjective `f` to a complement `C` of its kernel is bijective. -/
lemma bijective_domRestrict (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : IsCompl C f.ker) : Bijective ((f : E →ₗ[R] F).domRestrict C) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have hmem : (x : E) - y ∈ f.ker := by
      simpa [LinearMap.mem_ker, sub_eq_zero] using hxy
    have hC' : (x : E) - y ∈ C := C.sub_mem x.2 y.2
    have := hC.disjoint.le_bot ⟨hC', hmem⟩
    exact Subtype.ext (sub_eq_zero.mp this)
  · obtain ⟨x, rfl⟩ := hf.surjective y
    have hx : x ∈ C ⊔ f.ker := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨⟨c, hc⟩, by simp [show f k = 0 by simpa using hk]⟩

/-- The continuous right inverse of `f` with values in a topological complement `C` of the kernel
of `f`: the inverse of the restriction of `f` to `C`. It is continuous because it is the projection
onto `C` along the kernel of `f` of any continuous right inverse of `f`. -/
def rightInverseOfIsTopCompl (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : C.IsTopCompl f.ker) : F →L[R] E where
  toLinearMap := C.subtype ∘ₗ
    (LinearEquiv.ofBijective _ (hf.bijective_domRestrict hC.isCompl)).symm.toLinearMap
  cont := by
    obtain ⟨g, hg⟩ := id hf
    have key (y : F) : (LinearEquiv.ofBijective _ (hf.bijective_domRestrict hC.isCompl)).symm y =
        C.projectionOntoL f.ker hC (g y) := by
      rw [LinearEquiv.symm_apply_eq]
      have h := Submodule.projection_add_projection_eq_self hC.isCompl (g y)
      have hk : f (f.ker.projection C hC.isCompl.symm (g y)) = 0 :=
        LinearMap.mem_ker.mp (Submodule.projection_apply_mem hC.isCompl.symm (g y))
      simp only [LinearEquiv.ofBijective_apply, LinearMap.domRestrict_apply, coe_coe,
        Submodule.coe_projectionOntoL, Submodule.coe_projectionOnto_apply]
      conv_lhs => rw [← hg y, ← h, map_add, hk, add_zero]
    have hcont : Continuous fun y ↦ (C.projectionOntoL f.ker hC (g y) : E) := by fun_prop
    refine hcont.congr fun y ↦ ?_
    simp [key]

@[simp]
lemma apply_rightInverseOfIsTopCompl (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : C.IsTopCompl f.ker) (y : F) : f (hf.rightInverseOfIsTopCompl hC y) = y :=
  LinearEquiv.apply_ofBijective_symm_apply (f := (f : E →ₗ[R] F).domRestrict C)
    (h := hf.bijective_domRestrict hC.isCompl) y

lemma rightInverse_rightInverseOfIsTopCompl (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : C.IsTopCompl f.ker) : RightInverse (hf.rightInverseOfIsTopCompl hC) f :=
  hf.apply_rightInverseOfIsTopCompl hC

lemma rightInverseOfIsTopCompl_apply_mem (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : C.IsTopCompl f.ker) (y : F) : hf.rightInverseOfIsTopCompl hC y ∈ C :=
  ((LinearEquiv.ofBijective _ (hf.bijective_domRestrict hC.isCompl)).symm y).2

/-- The continuous right inverse of `f` with values in a topological complement of its kernel is
the only right inverse of `f` with values there. -/
lemma eq_rightInverseOfIsTopCompl (hf : f.HasRightInverse) {C : Submodule R E}
    (hC : C.IsTopCompl f.ker) {g : F →L[R] E} (hg : RightInverse g f) (hgC : ∀ y, g y ∈ C) :
    g = hf.rightInverseOfIsTopCompl hC := by
  ext y
  have := (hf.bijective_domRestrict hC.isCompl).1 (a₁ := ⟨g y, hgC y⟩)
    (a₂ := (LinearEquiv.ofBijective _ (hf.bijective_domRestrict hC.isCompl)).symm y)
    (by simp [hg y])
  exact congrArg Subtype.val this

/-- Every continuous right inverse `g` of `f` is the right inverse with values in its range, which
is a topological complement of the kernel of `f`. -/
lemma eq_rightInverseOfIsTopCompl_range {g : F →L[R] E} (hg : RightInverse g f) :
    g = HasRightInverse.rightInverseOfIsTopCompl ⟨g, hg⟩
      (g.isTopCompl_range_ker_of_leftInverse f hg) :=
  eq_rightInverseOfIsTopCompl _ _ hg fun y ↦ ⟨y, rfl⟩

end Ring

end HasRightInverse

end ContinuousLinearMap

end

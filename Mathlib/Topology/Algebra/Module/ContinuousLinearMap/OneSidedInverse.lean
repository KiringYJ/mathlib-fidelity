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
* `ContinuousLinearMap.HasLeftInverse.complement`: a choice of closed complement for `range f`

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

/-- Choice of continuous left inverse for `f : F →L[R] E`, given that such an inverse exists. -/
def leftInverse (h : f.HasLeftInverse) : F →L[R] E := Classical.choose h

lemma leftInverse_leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h

lemma injective (h : f.HasLeftInverse) : Injective f :=
  h.leftInverse_leftInverse.injective

example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

lemma congr {g : E →L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) :
    g.HasLeftInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous left inverse. -/
lemma _root_.ContinuousLinearEquiv.hasLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

@[simp] lemma _root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse (f : E ≃L[R] F) :
    f.hasLeftInverse.leftInverse = f.symm := by
  ext y
  calc f.hasLeftInverse.leftInverse y
    _ = f.hasLeftInverse.leftInverse (f (f.symm y)) := by simp
    _ = f.symm y := f.hasLeftInverse.leftInverse_leftInverse (f.symm y)

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
  use (f.comp hf.leftInverse).codRestrict f.range (by intro y; simp)
  rintro ⟨y, x, rfl⟩
  ext
  simp only [coe_coe, coe_codRestrict_apply, comp_apply]
  rw [hf.leftInverse_leftInverse]

section

variable [T1Space F]

lemma isClosed_range (hf : f.HasLeftInverse) [IsTopologicalAddGroup F] :
    IsClosed (range f) := by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  rw [← f.range_toLinearMap, ← f.coe_range,
    f.range_eq_ker_of_leftInverse (hf.leftInverse_leftInverse)]
  exact ((f.comp hf.leftInverse) - (ContinuousLinearMap.id R F)).isClosed_ker

/-- Choice of a closed complement of `range f` -/
def complement (h : f.HasLeftInverse) : Submodule R F :=
  h.closedComplemented_range.complement

lemma isClosed_complement (h : f.HasLeftInverse) : IsClosed (X := F) h.complement :=
  h.closedComplemented_range.isClosed_complement

omit [T1Space F] in
lemma isCompl_complement (h : f.HasLeftInverse) : IsCompl f.range h.complement :=
  h.closedComplemented_range.isCompl_complement

end

end Ring

end HasLeftInverse

namespace HasRightInverse

variable {f : E →L[R] F}

/-- Choice of continuous right inverse for `f : F →L[R] E`, given that such an inverse exists. -/
def rightInverse (h : f.HasRightInverse) : F →L[R] E := Classical.choose h

lemma rightInverse_rightInverse (h : f.HasRightInverse) : RightInverse h.rightInverse f :=
  Classical.choose_spec h

lemma surjective (h : f.HasRightInverse) : Surjective f :=
  h.rightInverse_rightInverse.surjective

lemma congr {g : E →L[R] F} (hf : f.HasRightInverse) (hfg : g = f) :
    g.HasRightInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous right inverse. -/
lemma _root_.ContinuousLinearEquiv.hasRightInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasRightInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

@[simp] lemma _root_.ContinuousLinearEquiv.rightInverse_hasRightInverse (f : E ≃L[R] F) :
    f.hasRightInverse.rightInverse = f.symm := by
  ext y
  exact f.injective <| by simpa using f.hasRightInverse.rightInverse_rightInverse y

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

end HasRightInverse

end ContinuousLinearMap

end

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.OneSidedInverse

/-!
# Split morphisms and isomorphisms of topological modules

A morphism of `TopModuleCat R` is a split monomorphism exactly when the underlying continuous
linear map has a continuous linear left inverse, a split epimorphism exactly when it has a
continuous linear right inverse, and an isomorphism exactly when it is a continuous linear
equivalence. This identifies `CategoryTheory.IsSplitMono`, `CategoryTheory.IsSplitEpi` and
`CategoryTheory.IsIso` in `TopModuleCat R` with `ContinuousLinearMap.HasLeftInverse`,
`ContinuousLinearMap.HasRightInverse` and `ContinuousLinearMap.IsInvertible`, which are stated for
unbundled topological modules in arbitrary universes.

## Main results

* `TopModuleCat.isSplitMono_iff_hasLeftInverse`
* `TopModuleCat.isSplitEpi_iff_hasRightInverse`
* `TopModuleCat.isIso_iff_isInvertible`
-/

public section

open CategoryTheory

universe v u

namespace TopModuleCat

variable {R : Type u} [Ring R] [TopologicalSpace R] {X Y : TopModuleCat.{v} R}

/-- A morphism of topological modules is a split monomorphism exactly when it has a continuous
linear left inverse. -/
theorem isSplitMono_iff_hasLeftInverse (f : X ⟶ Y) : IsSplitMono f ↔ f.hom.HasLeftInverse := by
  constructor
  · rintro ⟨⟨r, hr⟩⟩
    exact ⟨r.hom, fun x ↦ by simpa using congr_arg (fun g : X ⟶ X ↦ g.hom x) hr⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨ofHom g, by ext x; exact hg x⟩⟩

/-- A morphism of topological modules is a split epimorphism exactly when it has a continuous
linear right inverse. -/
theorem isSplitEpi_iff_hasRightInverse (f : X ⟶ Y) : IsSplitEpi f ↔ f.hom.HasRightInverse := by
  constructor
  · rintro ⟨⟨s, hs⟩⟩
    exact ⟨s.hom, fun y ↦ by simpa using congr_arg (fun g : Y ⟶ Y ↦ g.hom y) hs⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨ofHom g, by ext y; exact hg y⟩⟩

/-- A morphism of topological modules is an isomorphism exactly when it is a continuous linear
equivalence. -/
theorem isIso_iff_isInvertible (f : X ⟶ Y) : IsIso f ↔ f.hom.IsInvertible := by
  constructor
  · intro _
    refine .of_inverse (g := (inv f).hom) ?_ ?_
    · ext y
      simp
    · ext x
      simp
  · rintro ⟨e, he⟩
    have hf : f = (ofIso e).hom := by
      ext x
      exact (congr_arg (fun g : X →L[R] Y ↦ g x) he).symm
    rw [hf]
    infer_instance

end TopModuleCat

/-
Copyright (c) 2023 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Pullbacks of `C^n` vector bundles

This file defines pullbacks of `C^n` vector bundles over a manifold.

## Main definitions

* `ContMDiffVectorBundle.pullback`: For a `C^n` vector bundle `E` over a manifold `B` and a `C^n`
  map `f : B' → B`, the pullback vector bundle `f *ᵖ E` is a `C^n` vector bundle.

-/

public section

open Bundle Set
open scoped Manifold

variable {𝕜 B B' : Type*} (F : Type*) (E : B → Type*) {n : WithTop ℕ∞}
variable [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB'] (IB' : ModelWithCorners 𝕜 EB' HB')
  [TopologicalSpace B'] [ChartedSpace HB' B'] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB] (f : ContMDiffMap IB' IB B' B n)

/-- For a `C^n` vector bundle `E` over a manifold `B` and a `C^n` map `f : B' → B`, the pullback
vector bundle `f *ᵖ E` is a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.pullback : ContMDiffVectorBundle n F (f *ᵖ E) IB' where
  exists_contMDiffOn_coordChangeL := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨φ, hφ, hφe⟩ :=
      ContMDiffVectorBundle.exists_contMDiffOn_coordChangeL (n := n) (IB := IB) e e'
    refine ⟨φ ∘ f, hφ.comp f.contMDiff.contMDiffOn fun b hb => hb, ?_⟩
    intro b hb
    have hb' : f b ∈ e.baseSet ∩ e'.baseSet := hb
    ext v
    change φ (f b) v = ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) hb) v
    rw [hφe (f b) hb', ContinuousLinearEquiv.coe_coe, e.coordChangeL_apply e' hb',
      (e.pullback f).coordChangeL_apply' _]
    rfl

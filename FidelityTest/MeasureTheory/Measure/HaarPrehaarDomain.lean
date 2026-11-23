/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! The pre-Haar quotient has exactly the nonzero covering-index domain. -/

open MeasureTheory.Measure.haar TopologicalSpace

noncomputable section

example {G : Type*} [Group G] [TopologicalSpace G]
    (K₀ U : Set G) (h : index K₀ U ≠ 0) (K : Compacts G) : ℝ :=
  prehaar K₀ U h K

example {G : Type*} [Group G] [TopologicalSpace G]
    (K₀ U : Set G) (h₁ h₂ : index K₀ U ≠ 0) (K : Compacts G) :
    prehaar K₀ U h₁ K = prehaar K₀ U h₂ K := rfl

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : PositiveCompacts G) (U : OpenNhdsOf (1 : G)) (K : Compacts G) : ℝ :=
  prehaar K₀ U (index_pos K₀ (by rw [U.isOpen.interior_eq]; exact ⟨1, U.mem⟩)).ne' K

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ U : Set G) (h₀ : index K₀ U ≠ 0) (hU : (interior U).Nonempty)
    (K₁ K₂ : Compacts G) (h : (K₁ : Set G) ⊆ K₂) :
    prehaar K₀ U h₀ K₁ ≤ prehaar K₀ U h₀ K₂ :=
  prehaar_mono hU h

example {G : Type*} [AddGroup G] [TopologicalSpace G]
    (K₀ U : Set G) (h : addIndex K₀ U ≠ 0) (K : Compacts G) : ℝ :=
  addPrehaar K₀ U h K

/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : ℝ :=
  addPrehaar (∅ : Set ℤ) Set.univ (by simp [addIndex_empty]) ⊥

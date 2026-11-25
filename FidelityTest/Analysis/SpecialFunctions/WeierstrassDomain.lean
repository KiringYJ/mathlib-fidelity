/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! The pole and evaluation domains of the Weierstrass functions. -/

open TopologicalSpace
open scoped PeriodPair

variable (L : PeriodPair)

example : (L.ω₁ / 2 : ℂ) ∉ L.lattice := L.ω₁_div_two_notMem_lattice

example : (⟨L.ω₁ / 2, by simp⟩ : (⊤ : Opens ℂ)) ∈
    L.meromorphicWeierstrassP.regularLocus :=
  (L.mem_regularLocus_meromorphic_weierstrassP_iff _).mpr L.ω₁_div_two_notMem_lattice

example : (⟨0, by simp⟩ : (⊤ : Opens ℂ)) ∉ L.meromorphicWeierstrassP.regularLocus := by
  rw [L.mem_regularLocus_meromorphic_weierstrassP_iff]
  exact not_not_intro L.lattice.zero_mem

example : (⟨0, by simp⟩ : (⊤ : Opens ℂ)) ∉
    L.meromorphicDerivWeierstrassP.regularLocus := by
  rw [L.mem_regularLocus_meromorphic_derivWeierstrassP_iff]
  exact not_not_intro L.lattice.zero_mem

example : (MeromorphicSection.germ ⟨0, by simp⟩ L.meromorphicWeierstrassP).order = ↑(-2 : ℤ) :=
  L.order_weierstrassP (0 : L.lattice)

example : (MeromorphicSection.germ ⟨0, by simp⟩ L.meromorphicDerivWeierstrassP).order = ↑(-3 : ℤ) :=
  L.order_derivWeierstrassP (0 : L.lattice)

example : let z : {z : ℂ // z ∉ L.lattice} := ⟨L.ω₁ / 2, L.ω₁_div_two_notMem_lattice⟩
    ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ :=
  L.derivWeierstrassP_sq _

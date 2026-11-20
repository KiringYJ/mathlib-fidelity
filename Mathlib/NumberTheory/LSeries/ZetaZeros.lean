/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Analytic.Order

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main declarations

* `riemannZetaZeros`: The zeros of Riemann zeta function.

## Main results

* `isClosed_riemannZetaZeros`: `riemannZetaZeros` is closed.

* `isDiscrete_riemannZetaZeros`: `riemannZetaZeros` is discrete.

* `IsCompact.inter_riemannZetaZeros_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZetaZeros` is finite.
-/

@[expose] public section

/-- The zeros of Riemann's ζ-function. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
noncomputable def riemannZetaZeros : Set ℂ := {z | ∃ hz : z ≠ 1, riemannZeta z hz = 0}

lemma mem_riemannZetaZeros {z : ℂ} :
    z ∈ riemannZetaZeros ↔ ∃ hz : z ≠ 1, riemannZeta z hz = 0 := .rfl

open DirichletCharacter in
private lemma riemannZetaZeros_eq_preimage :
    riemannZetaZeros = LFunctionTrivChar₁ 1 ⁻¹' {0} := by
  ext z
  change (∃ hz : z ≠ 1, riemannZeta z hz = 0) ↔ LFunctionTrivChar₁ 1 z = 0
  rcases eq_or_ne z 1 with rfl | hz
  · simp [LFunctionTrivChar₁_apply_one]
  · rw [LFunctionTrivChar₁, LFunction₁_eq_mul _ hz, LFunction_modOne_eq hz,
      mul_eq_zero, or_iff_right (sub_ne_zero.mpr hz)]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hz, h⟩⟩

open DirichletCharacter in
/-- The complement of the zero set of `riemannZeta` is codiscrete. -/
private lemma compl_riemannZetaZeros_mem_codiscrete :
    riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ := by
  rw [riemannZetaZeros_eq_preimage, ← Set.preimage_compl]
  have hf := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  exact hf.preimage_zero_mem_codiscrete (x := 1) (by simp [LFunctionTrivChar₁_apply_one])

lemma isClosed_riemannZetaZeros : IsClosed riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

lemma isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
lemma IsCompact.inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite := by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

open Filter in
lemma tendsto_riemannZeta_cofinite_cocompact :
    Tendsto ((↑) : riemannZetaZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

end

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Multilinear normalization uses the product of coordinate norms, including the empty product. -/

example {ι : Type*} [Fintype ι] {E : ι → Type*} {F : Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ContinuousMultilinearMap ℝ E F) (m : ∀ i, E i)
    (hm : (∏ i, ‖m i‖) ≠ 0) : ‖f m‖ / (∏ i, ‖m i‖) ≤ ‖f‖ :=
  f.ratio_le_opNorm m

-- An empty domain family has denominator one, without any nontriviality of the codomain.
example {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℝ) F) :
    ‖f (fun i => Fin.elim0 i)‖ ≤ ‖f‖ := by
  simpa using f.ratio_le_opNorm (fun i => Fin.elim0 i) (hm := by simp)

-- A zero coordinate is still covered by the unnormalized operator bound.
example (f : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ℝ) ℝ) :
    ‖f (fun _ => 0)‖ ≤ ‖f‖ * ∏ _ : Fin 1, ‖(0 : ℝ)‖ := f.le_opNorm _

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
f : ℝ [×1]→L[ℝ] ℝ
⊢ IsUnit (∏ x, ‖0‖)
-/
#guard_msgs in
noncomputable example (f : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ℝ) ℝ) : ℝ :=
  ‖f (fun _ => 0)‖ / (∏ _ : Fin 1, ‖(0 : ℝ)‖)

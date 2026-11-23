/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Normalizing a vector in a seminormed space requires its norm to be nonzero. -/

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : ‖x‖ ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : E) 1 :=
  inv_norm_smul_mem_unitClosedBall x

example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : IsUnit ‖x‖) : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : E) 1 :=
  inv_norm_smul_mem_unitClosedBall x

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
E : Type u_1
inst✝¹ : SeminormedAddCommGroup E
inst✝ : NormedSpace ℝ E
x : E
hx : x ≠ 0
⊢ IsUnit ‖x‖
-/
#guard_msgs in
noncomputable example {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) : E := ‖x‖⁻¹ • x

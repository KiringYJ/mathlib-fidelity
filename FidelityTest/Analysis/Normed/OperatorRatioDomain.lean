/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-! Operator norm ratios need a nonzero norm even when the vector itself is nonzero. -/

example {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (f : E →L[ℝ] F) (x : E) (hx : ‖x‖ ≠ 0) :
    ‖f x‖ / ‖x‖ ≤ ‖f‖ := f.ratio_le_opNorm x

example {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (x : E) (hx : IsUnit ‖x‖) :
    ‖(0 : E →L[ℝ] F) x‖ / ‖x‖ = 0 := by simp

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
E : Type u_1
F : Type u_2
inst✝³ : SeminormedAddCommGroup E
inst✝² : SeminormedAddCommGroup F
inst✝¹ : NormedSpace ℝ E
inst✝ : NormedSpace ℝ F
f : E →L[ℝ] F
x : E
hx : x ≠ 0
⊢ IsUnit ‖x‖
-/
#guard_msgs in
noncomputable example {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (f : E →L[ℝ] F) (x : E) (hx : x ≠ 0) : ℝ :=
  ‖f x‖ / ‖x‖

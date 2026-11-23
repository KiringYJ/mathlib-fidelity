/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Singleton projection has a genuine zero-vector branch and a checked nonzero formula. -/

open scoped InnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example (w : E) : (ℝ ∙ (0 : E)).starProjection w = 0 := by
  simp

example (v w : E) (hv : v ≠ 0) :
    (ℝ ∙ v).starProjection w = (⟪v, w⟫_ℝ / ‖v‖ ^ 2) • v := by
  simpa [hv] using
    (Submodule.starProjection_singleton ℝ (v := v) w)

example (w : E) : (ℝ ∙ (0 : E)).reflection w = -w := by
  simp

example (v w : E) (hv : v ≠ 0) :
    (ℝ ∙ v).reflection w = 2 • ((⟪v, w⟫_ℝ / ‖v‖ ^ 2) • v) - w := by
  simpa [hv] using
    (Submodule.reflection_singleton_apply (𝕜 := ℝ) v w)

end

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
⊢ IsUnit ‖0‖
-/
#guard_msgs in
noncomputable example : ℝ := ‖(0 : ℝ)‖⁻¹

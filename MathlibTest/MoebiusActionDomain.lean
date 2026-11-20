/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! Regression tests for the exact denominator domain of the Möbius transformation. -/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

private def S : GL (Fin 2) ℝ := ModularGroup.S

example : denom S 0 = 0 := by
  have h := congrArg Complex.re (ModularGroup.denom_S UpperHalfPlane.I)
  have h₁ : S 1 1 = 0 := by
    simpa only [S, denom, coe_I, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, zero_add] using h
  simp [denom, h₁]

/--
error: could not synthesize default value for parameter 'hg' using tactics
---
error: an invertibility proof is required
⊢ IsUnit (denom S 0)
-/
#guard_msgs in
example : ℂ := smulAux' S 0

example : smulAux' (1 : GL (Fin 2) ℝ) 0 (by simp [denom]) = 0 := by
  simp [smulAux', σ, num, denom]

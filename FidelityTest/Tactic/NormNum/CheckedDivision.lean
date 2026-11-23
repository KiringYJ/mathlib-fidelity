/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-! Regression tests for exact-domain rational coefficient normalization. -/

example {K : Type*} [DivisionSemiring K] (h5 : (5 : K) ≠ 0) :
    Checked.div (5 : K) 5 h5.isUnit = 1 := by
  norm_num

example {K : Type*} [DivisionSemiring K] (h2 : (2 : K) ≠ 0) :
    Checked.div (1 : K) 2 h2.isUnit + Checked.div (1 : K) 2 h2.isUnit = 1 := by
  norm_num

example {K : Type*} [DivisionSemiring K] (h3 : (3 : K) ≠ 0) :
    Checked.div (2 : K) 3 h3.isUnit * 3 = 2 := by
  norm_num

example {K : Type*} [DivisionRing K] (h2 : (2 : K) ≠ 0) :
    (-3 : K) / 2 + 1 / 2 = -1 := by
  norm_num

example : NNRat.divNat (2 + 4) (2 ^ 3) (by decide) = (3 : ℚ≥0) / 4 := by
  norm_num

example : (NNRat.divNat (2 + 4) (2 ^ 3) (by decide) : ℝ) < 1 := by
  norm_num

example : (2.7182818286 : ℝ) = 13591409143 / 5000000000 := by
  norm_num

example : (2.7182818286 : ℝ) < 3 := by
  norm_num

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Tactic.NormNum

/-! Regression tests for exact-domain rational coefficient normalization. -/

example {K : Type*} [DivisionSemiring K] (h5 : (5 : K) ≠ 0) : (5 : K) / 5 = 1 := by
  norm_num

example {K : Type*} [DivisionSemiring K] (h2 : (2 : K) ≠ 0) :
    (1 : K) / 2 + 1 / 2 = 1 := by
  norm_num

example {K : Type*} [DivisionSemiring K] (h3 : (3 : K) ≠ 0) :
    ((2 : K) / 3) * 3 = 2 := by
  norm_num

example {K : Type*} [DivisionRing K] (h2 : (2 : K) ≠ 0) :
    (-3 : K) / 2 + 1 / 2 = -1 := by
  norm_num

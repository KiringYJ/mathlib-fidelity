/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Tactic.Bound

/-! Regression tests for `bound` over evidence-bearing inverse and division. -/

example {K : Type*} [GroupWithZero K] [PartialOrder K] [PosMulReflectLT K]
    {a : K} (ha : IsUnit a) (h : 0 ≤ a) : 0 ≤ Checked.inv a ha := by
  bound

example {K : Type*} [GroupWithZero K] [PartialOrder K] [PosMulReflectLT K]
    {a : K} (ha : IsUnit a) (h : 0 < a) : 0 < Checked.inv a ha := by
  bound

example {K : Type*} [GroupWithZero K] [PartialOrder K] [PosMulReflectLT K]
    {a b : K} (hb : IsUnit b) (ha : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ Checked.div a b hb := by
  bound

example {K : Type*} [GroupWithZero K] [PartialOrder K] [PosMulReflectLT K]
    {a b : K} (hb : IsUnit b) (ha : 0 < a) (hb0 : 0 < b) :
    0 < Checked.div a b hb := by
  bound

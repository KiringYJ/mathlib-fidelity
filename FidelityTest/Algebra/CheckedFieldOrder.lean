/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (a b c : K) (hb : b ≠ 0)

-- Multiplication by the squared denominator preserves order without fixing its sign.
example : a / b < c / b ↔ a * b < c * b := by
  field_simp

example : a / b ≤ c / b ↔ a * b ≤ c * b := by
  field_simp

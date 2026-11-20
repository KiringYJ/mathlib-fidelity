/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Field.Basic

open Mathlib.Tactic.FieldSimp

variable {K : Type*} [Field K] (a b c : K) (hb : b ≠ 0) (hc : c ≠ 0)

example : (a / b) * b = a := by
  field_simp

example : a / b + c / b = (a + c) / b := by
  field_simp

example : (a / b) / c = a / (b * c) := by
  field_simp

example (ha : a ≠ 0) : a ^ (-1 : Int) * a = 1 := by
  field_simp

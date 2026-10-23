/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Data.Rat.Init

/-- error: failed to synthesize
  Inv ℚ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Inv ℚ

/-- error: failed to synthesize
  Div ℚ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Div ℚ

/-- error: failed to synthesize
  Pow ℚ Int

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Pow ℚ Int

/-- error: Type mismatch
  Rat.reciprocal 0
has type
  0 ≠ 0 → ℚ
but is expected to have type
  ℚ -/
#guard_msgs in
example : ℚ := Rat.reciprocal 0

/-- error: Type mismatch
  Rat.fraction 0 0
has type
  0 ≠ 0 → ℚ
but is expected to have type
  ℚ -/
#guard_msgs in
example : ℚ := Rat.fraction 0 0

/-- error: Type mismatch
  Rat.fractionInt 0 0
has type
  0 ≠ 0 → ℚ
but is expected to have type
  ℚ -/
#guard_msgs in
example : ℚ := Rat.fractionInt 0 0

example : Rat.fraction 2 4 (by decide) = Rat.fraction 1 2 (by decide) := by decide +kernel
example (q : ℚ) (hq : q ≠ 0) : q * Rat.reciprocal q hq = 1 := Rat.mul_reciprocal q hq

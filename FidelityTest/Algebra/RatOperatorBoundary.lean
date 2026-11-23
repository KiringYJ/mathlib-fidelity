/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Pi

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
  Pow ℚ ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Pow ℚ ℤ

/-- error: failed to synthesize
  Inv (Fin 1 → ℚ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Inv (Fin 1 → ℚ)

/-- error: failed to synthesize
  Div (Fin 1 → ℚ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Div (Fin 1 → ℚ)

/-- error: failed to synthesize
  Pow (Fin 1 → ℚ) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Pow (Fin 1 → ℚ) ℤ

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
f : Fin 1 → ℚ
⊢ IsUnit f
-/
#guard_msgs in
noncomputable example (f : Fin 1 → ℚ) : Fin 1 → ℚ := f⁻¹

example (f g : Fin 1 → ℚ) (hg : IsUnit g) : (f / g) * g = f := div_mul_cancel₀ f

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

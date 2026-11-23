/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import FidelityTest.OperatorPolicy.Import
import Lean.Elab.GuardMsgs
/-- error: failed to synthesize
  Inv Rat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Inv Rat
/-- error: failed to synthesize
  Div Rat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Div Rat
/-- error: failed to synthesize
  Pow Rat Int

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Pow Rat Int
/-- error: failed to synthesize
  Lean.Grind.Field Rat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Lean.Grind.Field Rat
#check_failure (inferInstance : Inv Rat)
#check_failure (inferInstance : Div Rat)
example (a b : Rat) : Rat := a + b * a
example (a : Rat) : Rat := a ^ (3 : Nat)
/-- info: 9 -/
#guard_msgs in
#eval (4 : Nat) + 5

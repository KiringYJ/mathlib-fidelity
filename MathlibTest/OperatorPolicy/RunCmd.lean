/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import MathlibTest.OperatorPolicy.Import
import Lean.Elab.GuardMsgs
/-- error: failed to synthesize instance of type class
  Inv Rat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
run_cmd
  let _ : Inv Rat := inferInstance
  pure ()

section
example : Nat := 0
end
/-- error: failed to synthesize instance of type class
  Inv Rat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
run_cmd
  let _ : Inv Rat := inferInstance
  pure ()

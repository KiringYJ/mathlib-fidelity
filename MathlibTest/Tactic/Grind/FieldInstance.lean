import Mathlib.FieldTheory.IntermediateField.Basic
import Lean.Elab.GuardMsgs

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)

example (x : E) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀

/-- error: failed to synthesize
  Lean.Grind.Field ↥E

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Lean.Grind.Field E

/-- error: failed to synthesize
  Inv ↥E

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Inv E

end

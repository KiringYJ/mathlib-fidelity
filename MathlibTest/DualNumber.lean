import Mathlib.Algebra.DualNumber

open DualNumber

/-! Inversion is available exactly for dual numbers with unit constant term. -/

example [Nontrivial R] [Ring R] : ¬IsUnit (ε : R[ε]) :=
  not_isUnit_eps

/--
error: failed to synthesize instance of type class
  Inv ℤ[ε]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (x : ℤ[ε]) : ℤ[ε] := x⁻¹

example : TrivSqZeroExt.inverse (1 + ε : ℤ[ε]) (by simp) = 1 - ε := by
  ext <;> simp [TrivSqZeroExt.inverse]

-- TODO(kmill): make a ToExpr instance for DualNumber
set_option eval.pp false

/-- info: 0 + 0*ε -/
#guard_msgs in
#eval (0 : ℕ[ε])

/-- info: 2 + 0*ε -/
#guard_msgs in
#eval (2 : ℕ[ε])

/-- info: 6 + 0*ε -/
#guard_msgs in
#eval (2 + 4 : ℕ[ε])

/-- info: 2 + 0*ε + (0 + 0*ε)*ε -/
#guard_msgs in
#eval (2 : (ℕ[ε])[ε])

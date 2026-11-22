module
import Mathlib.Tactic.NormNum.Ordinal

universe u

/-- error: failed to synthesize
  Div Ordinal.{0}

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Div Ordinal.{0}

example (a : Ordinal) : a % 0 = a := Ordinal.mod_zero a

example : Ordinal.quotient (Ordinal.omega0 * 2 + 1) Ordinal.omega0 Ordinal.omega0_ne_zero = 2 :=
  Ordinal.quotient_eq_of_remainder Ordinal.omega0_ne_zero rfl Ordinal.one_lt_omega0

example : (2 : Ordinal.{0}) * 3 + 4 = 10 := by norm_num

example : ¬Ordinal.quotient (15 : Ordinal.{4}) 4 (by norm_num) % 34 < 3 := by norm_num

example : (12 : Ordinal.{u}) ^ (2 : Ordinal.{u}) ^ (2 : ℕ) ≤
    (12 : Ordinal.{u}) ^ (2 : Ordinal.{u}) ^ (2 : ℕ) := by norm_num

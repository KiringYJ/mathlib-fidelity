import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nonvanishing of the Riemann zeta function on its domain

These tests ensure that nonvanishing on the closed right half-plane requires excluding the pole at
`s = 1` explicitly.
-/

example {s : ℂ} (hs₀ : s ≠ 1) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs₀ hs

set_option linter.unusedVariables false in
example {s : ℂ} (hs : 1 ≤ s.re) : True := by
  fail_if_success
    have _h : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
  trivial

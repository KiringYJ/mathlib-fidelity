import Mathlib.Algebra.Polynomial.Mirror

/-!
# The natural trailing degree takes its domain

`Polynomial.natTrailingDegree p hp` is the trailing degree of a nonzero polynomial as a natural
number. The zero polynomial has trailing degree `⊤` and no natural trailing degree; the proof `hp`
is found by `assumption`. The trailing coefficient and the mirror stay total, with value `0` at `0`.
-/

open Polynomial

/-! The lemma that stated the value `0` at `0` is removed. -/

/-- info: Unknown identifier `natTrailingDegree_zero` -/
#guard_msgs in
#check_failure natTrailingDegree_zero

/-! The proof is found among the hypotheses, or passed explicitly. -/

example (p : ℤ[X]) (hp : p ≠ 0) : p.coeff p.natTrailingDegree ≠ 0 :=
  coeff_natTrailingDegree_ne_zero hp

example (p : ℤ[X]) (hp : p ≠ 0) : p.trailingDegree = p.natTrailingDegree :=
  trailingDegree_eq_natTrailingDegree hp

example (p : ℤ[X]) (h : p.coeff 2 ≠ 0) : p.natTrailingDegree (ne_zero_of_coeff_ne_zero h) ≤ 2 :=
  natTrailingDegree_le_of_ne_zero h

example : (X ^ 3 : ℤ[X]).natTrailingDegree (pow_ne_zero 3 X_ne_zero) = 3 :=
  natTrailingDegree_X_pow 3

/-! The total invariants keep their values at `0`. -/

example : (0 : ℤ[X]).trailingDegree = ⊤ := trailingDegree_zero

example : (0 : ℤ[X]).trailingCoeff = 0 := trailingCoeff_zero

example : (0 : ℤ[X]).mirror = 0 := mirror_zero

/-! Without a proof that the polynomial is nonzero, there is no natural trailing degree. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: Tactic `assumption` failed

p : ℤ[X]
⊢ p ≠ 0
-/
#guard_msgs in
example (p : ℤ[X]) : ℕ := p.natTrailingDegree

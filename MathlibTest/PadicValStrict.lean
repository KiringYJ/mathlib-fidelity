import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Multiplicity and the `p`-adic valuations take their domains

`multiplicity a b h` takes a proof `h` that the multiplicity is finite, and the `p`-adic valuations
`padicValNat p n`, `padicValInt p z`, and `padicValRat p q` take `p ≠ 1` and a nonzero argument,
which `padic_val_tac` finds by default. None of them has a value outside its domain.
-/

/-! The lemmas that stated the values at infinite multiplicity are removed. -/

/-- info: Unknown identifier `multiplicity_eq_zero_of_not_finiteMultiplicity` -/
#guard_msgs in
#check_failure multiplicity_eq_zero_of_not_finiteMultiplicity

/-- info: Unknown identifier `padicValNat_zero_right` -/
#guard_msgs in
#check_failure padicValNat_zero_right

/-- info: Unknown identifier `padicValNat_one_left` -/
#guard_msgs in
#check_failure padicValNat_one_left

/-- info: Unknown constant `padicValRat.zero` -/
#guard_msgs in
#check_failure padicValRat.zero

/-! The default discharger uses hypotheses, primality, and positivity. -/

example (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p (n * n) = padicValNat p n + padicValNat p n :=
  padicValNat.mul hn hn

example (p : ℕ) [Fact p.Prime] (n : ℕ) : padicValNat p n.factorial ≤ n :=
  padicValNat_factorial_le p n

example (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : z ≠ 0) : ℕ := padicValInt p (-z)

example (a b : ℕ) (h : FiniteMultiplicity a b) : emultiplicity a b = multiplicity a b h :=
  h.emultiplicity_eq_multiplicity

/-! Other evidence is passed by name. -/

example (p n : ℕ) (h : p ≠ 1) (hn : n ≠ 0) : padicValNat p n (hp := h) = padicValNat p n :=
  rfl

example (p : ℕ) (hp : p.Prime) (q : ℚ) (hq : q ^ 2 ≠ 0) : ℤ :=
  padicValRat p q (hq := (pow_ne_zero_iff two_ne_zero).1 hq)

/-! At `0`, or for `p = 1`, the valuation is not defined. -/

/--
error: could not synthesize default value for parameter 'hn' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
⊢ 0 ≠ 0
-/
#guard_msgs in
example : ℕ := padicValNat 2 0

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
⊢ 1 ≠ 1
-/
#guard_msgs in
example : ℕ := padicValNat 1 5

/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
q : ℚ
⊢ q ≠ 0
-/
#guard_msgs in
example (q : ℚ) : ℤ := padicValRat 3 q

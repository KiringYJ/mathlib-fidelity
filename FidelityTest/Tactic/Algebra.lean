module

import Mathlib.Tactic.Algebra.Basic

-- A symbolic denominator is an atom, and its invertibility comes from the hypothesis.
example (x y : ℚ) (hy : y ≠ 0) : x / y + x / y = 2 * (x / y) := by
  algebra

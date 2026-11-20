/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# IMO 1960 Q2

For what values of the variable $x$ does the following inequality hold:

\[\dfrac{4x^2}{(1 - \sqrt {2x + 1})^2} < 2x + 9 \ ?\]

We follow solution at
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1960_IMO_Problems/Problem_2)
with minor modifications.
-/

public section

open Real Set

namespace Imo1960Q2

/-- The predicate says that `x` satisfies the inequality

\[\dfrac{4x^2}{(1 - \sqrt {2x + 1})^2} < 2x + 9\]

and belongs to the domain of the function on the left-hand side.
-/
structure IsGood (x : ℝ) : Prop where
  /-- The number belongs to the domain of \(\sqrt {2x + 1}\). -/
  sqrt_dom : 0 ≤ 2 * x + 1
  /-- The number belongs to the domain of the denominator. -/
  denom_dom : (1 - sqrt (2 * x + 1)) ^ 2 ≠ 0
  /-- The number satisfies the inequality. -/
  ineq : Checked.div (4 * x ^ 2) ((1 - sqrt (2 * x + 1)) ^ 2) denom_dom.isUnit < 2 * x + 9

theorem isGood_iff' (x : ℝ) :
    IsGood x ↔ 0 ≤ 2 * x + 1 ∧ ∃ hd : (1 - sqrt (2 * x + 1)) ^ 2 ≠ 0,
      Checked.div (4 * x ^ 2) ((1 - sqrt (2 * x + 1)) ^ 2) hd.isUnit < 2 * x + 9 :=
  ⟨fun h ↦ ⟨h.sqrt_dom, h.denom_dom, h.ineq⟩, fun ⟨hs, hd, hi⟩ ↦ ⟨hs, hd, hi⟩⟩

/-- Solution of IMO 1960 Q2: solutions of the inequality
are the numbers of the half-closed interval \([-1/2, 45/8)\) except for the number zero. -/
theorem isGood_iff {x : ℝ} : IsGood x ↔ x ∈ Ico (-1 / 2) (45 / 8) \ {0} := by
  -- First, note that the denominator is equal to zero at `x = 0`, hence it's not a solution.
  rcases eq_or_ne x 0 with rfl | hx
  · constructor
    · intro h
      exact (h.denom_dom (by norm_num)).elim
    · intro h
      exact (h.2 (by simp)).elim
  cases lt_or_ge x (-1 / 2) with
  | inl hx2 =>
    -- Next, if `x < -1/2`, then the square root is undefined.
    have : 2 * x + 1 < 0 := by linarith
    simp [hx2.not_ge, isGood_iff', this.not_ge]
  | inr hx2 =>
    -- Now, if `x ≥ -1/2`, `x ≠ 0`, then the expression is well-defined.
    have hx2' : 0 ≤ 2 * x + 1 := by linarith
    have H : 1 - sqrt (2 * x + 1) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, sqrt_eq_iff_eq_sq hx2' zero_le_one]
      simpa
    calc
      -- Note that the fraction in the LHS is equal to `(1 + sqrt (2 * x + 1)) ^ 2`
      IsGood x ↔ (1 + sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 := by
        have : 4 * x ^ 2 = (1 + sqrt (2 * x + 1)) ^ 2 * (1 - sqrt (2 * x + 1)) ^ 2 := by
          rw [← mul_pow, ← sq_sub_sq, sq_sqrt hx2']
          ring
        have hd : (1 - sqrt (2 * x + 1)) ^ 2 ≠ 0 := pow_ne_zero _ H
        have he : Checked.div (4 * x ^ 2) ((1 - sqrt (2 * x + 1)) ^ 2) hd.isUnit =
            (1 + sqrt (2 * x + 1)) ^ 2 := div_eq_iff.mpr this
        constructor
        · intro h
          simpa only [he] using h.ineq
        · intro h
          exact ⟨hx2', hd, by simpa only [he] using h⟩
      -- Simplify the inequality
      _ ↔ sqrt (2 * x + 1) < 7 / 2 := by
        rw [add_sq, sq_sqrt hx2']; constructor <;> intro <;> linarith
      _ ↔ 2 * x + 1 < (7 / 2) ^ 2 := sqrt_lt' <| by positivity
      _ ↔ x < 45 / 8 := by constructor <;> intro <;> linarith
      _ ↔ x ∈ Ico (-1 / 2) (45 / 8) \ {0} := by simp [*]

end Imo1960Q2

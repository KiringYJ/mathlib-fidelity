/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Basic.NNReal.Basic

/-!
# IMO 1986 Q5

Find all functions `f`, defined on the non-negative real numbers and taking nonnegative real values,
such that:

- $f(xf(y))f(y) = f(x + y)$ for all $x, y \ge 0$,
- $f(2) = 0$,
- $f(x) \ne 0$ for $0 \le x < 2$.

We formalize the assumptions in `Imo1986Q5.IsGood`. The unique solution is
`2 / (2 - x)` for `x < 2` and zero for `2 ≤ x`. The functional equation and `f 2 = 0`
force the zero branch.

Formalization is based on
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1986_IMO_Problems/Problem_5)
with minor modifications.
-/

@[expose] public section

open NNReal

namespace Imo1986Q5

structure IsGood (f : ℝ≥0 → ℝ≥0) : Prop where
  map_add_rev x y : f (x * f y) * f y = f (x + y)
  map_two : f 2 = 0
  map_ne_zero : ∀ x < 2, f x ≠ 0

/-- The solution, with the quotient restricted to `x < 2`. -/
noncomputable def solution (x : ℝ≥0) : ℝ≥0 :=
  if hx : x < 2 then Checked.div 2 (2 - x) (tsub_pos_of_lt hx).ne'.isUnit else 0

private theorem solution_of_not_lt {x : ℝ≥0} (hx : ¬ x < 2) : solution x = 0 := by
  rw [solution, dite_eq_right hx]

private theorem solution_pos {x : ℝ≥0} (hx : x < 2) : 0 < solution x := by
  rw [solution, dite_eq_left hx]
  exact div_pos zero_lt_two (tsub_pos_of_lt hx)

private theorem solution_mul {x : ℝ≥0} (hx : x < 2) : solution x * (2 - x) = 2 := by
  rw [solution, dite_eq_left hx, div_mul_cancel₀]

namespace IsGood

variable {f : ℝ≥0 → ℝ≥0} (hf : IsGood f) {x y : ℝ≥0}
include hf

theorem map_add (x y : ℝ≥0) : f (x + y) = f (x * f y) * f y :=
  (hf.map_add_rev x y).symm

theorem map_eq_zero : f x = 0 ↔ 2 ≤ x := by
  refine ⟨fun hx₀ ↦ not_lt.1 fun hlt ↦ hf.map_ne_zero x hlt hx₀, fun hle ↦ ?_⟩
  rcases exists_add_of_le hle with ⟨x, rfl⟩
  rw [add_comm, hf.map_add, hf.map_two, mul_zero]

theorem map_ne_zero_iff : f x ≠ 0 ↔ x < 2 := by simp [hf.map_eq_zero]

theorem map_of_lt_two (hx : x < 2) : f x = 2 / (2 - x) := by
  have hx' : 0 < 2 - x := tsub_pos_of_lt hx
  have hfx : f x ≠ 0 := hf.map_ne_zero_iff.2 hx
  apply le_antisymm
  · rw [le_div_iff₀ hx', ← le_div_iff₀' hfx.bot_lt, tsub_le_iff_right, ← hf.map_eq_zero,
      hf.map_add, div_mul_cancel₀, hf.map_two, zero_mul]
  · rw [div_le_iff₀' hx', ← hf.map_eq_zero]
    refine (mul_eq_zero.1 ?_).resolve_right hfx
    rw [hf.map_add_rev, hf.map_eq_zero, tsub_add_cancel_of_le hx.le]

theorem map_eq (x : ℝ≥0) : f x = solution x := by
  by_cases hx : x < 2
  · simpa only [solution, dite_eq_left hx] using hf.map_of_lt_two hx
  · rw [solution_of_not_lt hx]
    exact hf.map_eq_zero.2 (le_of_not_gt hx)

end IsGood

theorem isGood_iff {f : ℝ≥0 → ℝ≥0} : IsGood f ↔ f = solution := by
  refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩
  rintro rfl
  constructor
  case map_two => exact solution_of_not_lt (lt_irrefl _)
  case map_ne_zero => exact fun x hx ↦ (solution_pos hx).ne'
  case map_add_rev =>
    intro x y
    by_cases hy : y < 2
    · have hy2 : (2 - y) * solution y = 2 := by rw [mul_comm, solution_mul hy]
      have hlt : x * solution y < 2 ↔ x + y < 2 := calc
        x * solution y < 2 ↔ x * solution y < (2 - y) * solution y := by rw [hy2]
        _ ↔ x < 2 - y := mul_lt_mul_iff_of_pos_right (solution_pos hy)
        _ ↔ x + y < (2 - y) + y := by simp only [add_lt_add_iff_right]
        _ ↔ x + y < 2 := by rw [tsub_add_cancel_of_le hy.le]
      by_cases hxy : x + y < 2
      · have hd : solution y * (2 - (x + y)) = 2 - x * solution y := by
          rw [mul_comm (solution y), tsub_add_eq_tsub_tsub_swap, tsub_mul, hy2]
        apply (mul_left_inj' (tsub_pos_of_lt hxy).ne').mp
        rw [mul_assoc, hd, solution_mul (hlt.mpr hxy), solution_mul hxy]
      · have hz := mt hlt.mp hxy
        rw [solution_of_not_lt hz, zero_mul, solution_of_not_lt hxy]
    · have hz : ¬ x + y < 2 := not_lt_of_ge (le_add_left (le_of_not_gt hy))
      simp only [solution_of_not_lt hy, solution_of_not_lt hz, mul_zero]

end Imo1986Q5

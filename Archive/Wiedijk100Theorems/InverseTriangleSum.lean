/-
Copyright (c) 2020 Jalex Stark, Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring

/-!
# Sum of the Reciprocals of the Triangular Numbers

This file proves Theorem 42 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The positive triangular numbers have the form $\frac{(k+1)(k+2)}{2}$ for natural `k`.
The sum of the reciprocals of the first `n` positive triangular numbers is $2 - \frac{2}{n+1}$.

## Tags

discrete_sum
-/

open Finset

/-- **Sum of the Reciprocals of the Triangular Numbers** -/
public theorem Theorems100.inverse_triangle_sum (n : ℕ) :
    ∑ k ∈ range n, (2 : ℚ) / (((k : ℚ) + 1) * ((k : ℚ) + 2)) =
      2 - (2 : ℚ) / ((n : ℚ) + 1) := by
  have h (k : ℕ) : (2 : ℚ) / (((k : ℚ) + 1) * ((k : ℚ) + 2)) =
      (2 : ℚ) / ((k : ℚ) + 1) - 2 / ((k : ℚ) + 2) := by
    rw [div_sub_div, show (2 : ℚ) * (k + 2) - (k + 1) * 2 = 2 by ring]
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, h]
    simp only [Nat.cast_succ]
    ring_nf

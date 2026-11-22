/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Positivity

/-!
# Rational approximations to square roots of naturals

This file defines `Nat.ratSqrt x prec`, a rational approximation of the square root of a
natural number `x` to within `1 / prec`, and proves the basic bounds it satisfies.

See also `Mathlib.Analysis.Rat.NatSqrt.Real` for comparisons with the real square root.
-/

@[expose] public section

namespace Nat

/--
Approximate the square root of a natural number using positive precision `prec`,
to within `1 / prec`.
-/
def ratSqrt (x prec : ℕ) (hprec : 0 < prec) : ℚ :=
  Rat.fraction ((x * prec ^ 2).sqrt : ℤ) prec hprec.ne'

theorem ratSqrt_nonneg (x prec : ℕ) (hprec : 0 < prec) : 0 ≤ ratSqrt x prec hprec :=
  Rat.fraction_nonneg (Int.natCast_nonneg _) _ _

theorem ratSqrt_mul_prec (x prec : ℕ) (hprec : 0 < prec) :
    ratSqrt x prec hprec * (prec : ℚ) = ((x * prec ^ 2).sqrt : ℚ) := by
  exact Rat.fraction_mul_den _ _ _

theorem ratSqrt_sq_le (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec h) ^ 2 ≤ (x : ℚ) := by
  apply (mul_le_mul_iff_of_pos_right (pow_pos (Nat.cast_pos.mpr h : (0 : ℚ) < prec) 2)).mp
  rw [← mul_pow, ratSqrt_mul_prec]
  exact_mod_cast sqrt_le' (x * prec ^ 2)

theorem lt_ratSqrt_add_inv_prec_sq (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (x : ℚ) < (ratSqrt x prec h + (1 : ℚ) / (prec : ℚ)) ^ 2 := by
  apply (mul_lt_mul_iff_of_pos_right (pow_pos (Nat.cast_pos.mpr h : (0 : ℚ) < prec) 2)).mp
  rw [← mul_pow, add_mul, ratSqrt_mul_prec, div_mul_cancel₀]
  exact_mod_cast lt_succ_sqrt' (x * prec ^ 2)

end Nat

/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.NatSqrt.Defs
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Rational approximations to square roots of naturals

Comparisons between rational approximations to the square root of a natural number
and the real square root.
-/

public section

namespace Nat

theorem ratSqrt_le_realSqrt (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec h : ℝ) ≤ √x := by
  have hq := ratSqrt_sq_le (x := x) h
  have hr : ((x.ratSqrt prec h : ℚ) : ℝ) ^ 2 ≤ ↑x := by exact_mod_cast hq
  have hs := Real.sqrt_monotone hr
  rwa [Real.sqrt_sq] at hs
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _ h

theorem realSqrt_lt_ratSqrt_add_inv_prec (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x < ratSqrt x prec h + 1 / prec := by
  have hp : (0 : ℝ) < prec := Nat.cast_pos.mpr h
  have hr : ((ratSqrt x prec h : ℚ) : ℝ) * prec = ((x * prec ^ 2).sqrt : ℝ) := by
    exact_mod_cast ratSqrt_mul_prec x prec h
  have hpos : (0 : ℝ) < ratSqrt x prec h + 1 / prec :=
    add_pos_of_nonneg_of_pos (by exact_mod_cast ratSqrt_nonneg x prec h) (by positivity)
  rw [Real.sqrt_lt' hpos]
  apply (mul_lt_mul_iff_of_pos_right (pow_pos hp 2)).mp
  rw [← mul_pow, add_mul, hr, one_div_mul_cancel]
  exact_mod_cast lt_succ_sqrt' (x * prec ^ 2)

theorem realSqrt_mem_Ico (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x ∈ Set.Ico (ratSqrt x prec h : ℝ) (ratSqrt x prec h + 1 / prec : ℝ) :=
  ⟨ratSqrt_le_realSqrt x h, realSqrt_lt_ratSqrt_add_inv_prec x h⟩

theorem ratSqrt_mem_Ioc (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec h : ℝ) ∈ Set.Ioc (√x - 1 / prec) √x := by
  constructor
  · exact sub_lt_iff_lt_add.mpr (realSqrt_lt_ratSqrt_add_inv_prec x h)
  · exact ratSqrt_le_realSqrt x h

end Nat

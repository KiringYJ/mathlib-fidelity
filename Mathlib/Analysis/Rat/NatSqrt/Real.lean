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
    √x < (ratSqrt x prec h : ℝ) +
      (1 : ℝ) /ₚ Units.mk0 (prec : ℝ) (Nat.cast_ne_zero.mpr h.ne') := by
  let uq := Units.mk0 (prec : ℚ) (Nat.cast_ne_zero.mpr h.ne')
  let ur := Units.mk0 (prec : ℝ) (Nat.cast_ne_zero.mpr h.ne')
  have hmap : Units.map (Rat.castHom ℝ).toMonoidHom uq = ur := by
    apply Units.ext
    change ((prec : ℚ) : ℝ) = (prec : ℝ)
    exact Rat.cast_natCast _
  have hc : (((1 : ℚ) /ₚ uq : ℚ) : ℝ) = (1 : ℝ) /ₚ ur := by
    rw [Rat.cast_divp, Rat.cast_one, hmap]
  have hq := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have hr : (x : ℝ) < ↑((x.ratSqrt prec h + (1 : ℚ) /ₚ uq) ^ 2 : ℚ) := by
    exact_mod_cast hq
  have hs := Real.sqrt_lt_sqrt (by simp) hr
  rw [Rat.cast_pow, Real.sqrt_sq] at hs
  · simpa only [Rat.cast_add, hc] using hs
  · rw [Rat.cast_add, hc]
    exact add_nonneg (by simpa only [Rat.cast_nonneg] using ratSqrt_nonneg x prec h)
      (divp_nonneg zero_le_one (by change (0 : ℝ) ≤ prec; exact Nat.cast_nonneg _))

theorem realSqrt_mem_Ico (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x ∈ Set.Ico (ratSqrt x prec h : ℝ)
      ((ratSqrt x prec h : ℝ) +
        (1 : ℝ) /ₚ Units.mk0 (prec : ℝ) (Nat.cast_ne_zero.mpr h.ne')) :=
  ⟨ratSqrt_le_realSqrt x h, realSqrt_lt_ratSqrt_add_inv_prec x h⟩

theorem ratSqrt_mem_Ioc (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec h : ℝ) ∈ Set.Ioc
      (√x - (1 : ℝ) /ₚ Units.mk0 (prec : ℝ) (Nat.cast_ne_zero.mpr h.ne')) √x := by
  constructor
  · exact sub_lt_iff_lt_add.mpr (realSqrt_lt_ratSqrt_add_inv_prec x h)
  · exact ratSqrt_le_realSqrt x h

end Nat

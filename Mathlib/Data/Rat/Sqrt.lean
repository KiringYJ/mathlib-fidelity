/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `Rat.sqrt`
and proves several theorems about it.

-/

@[expose] public section


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
def sqrt (q : ℚ) : ℚ :=
  fraction (Int.sqrt q.num) (Nat.sqrt q.den) (Nat.sqrt_pos.mpr q.den_pos).ne'

theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = |q| := by
  simp only [sqrt, mul_self_num, mul_self_den, Int.sqrt_eq, Nat.sqrt_eq]
  by_cases h : 0 ≤ q
  · rw [abs_of_nonneg h]
    simpa only [fraction, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr h)] using
      Rat.normalize_self q
  · rw [abs_of_nonpos (le_of_not_ge h)]
    have hn : q.num ≤ 0 := by
      have hn := Rat.num_nonneg.mpr (neg_nonneg.mpr (le_of_not_ge h))
      simpa only [Rat.neg_num, Int.neg_nonneg] using hn
    simpa only [fraction, Int.ofNat_natAbs_of_nonpos hn, Rat.neg_num, Rat.neg_den] using
      Rat.normalize_self (-q)

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

lemma sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q := by
  exact Rat.fraction_nonneg (Int.sqrt_nonneg _) _ _

/-- `IsSquare` can be decided on `ℚ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℚ → Prop) :=
  fun m => decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]
theorem sqrt_intCast (z : ℤ) : Rat.sqrt (z : ℚ) = Int.sqrt z := by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, fraction]
  rw [Rat.normalize_eq_mk' _ _ _ (by simp), Rat.mk_den_one]

@[simp, norm_cast]
theorem sqrt_natCast (n : ℕ) : Rat.sqrt (n : ℚ) = Nat.sqrt n := by
  rw [← Int.cast_natCast, sqrt_intCast, Int.sqrt_natCast, Int.cast_natCast]

@[simp]
theorem sqrt_ofNat (n : ℕ) : Rat.sqrt (ofNat(n) : ℚ) = Nat.sqrt (OfNat.ofNat n) :=
  sqrt_natCast _

end Rat

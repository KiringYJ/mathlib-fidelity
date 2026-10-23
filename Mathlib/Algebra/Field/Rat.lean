/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.NNRat.Defs

/-!
# The rational numbers form a field

This file contains the field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

@[expose] public section

namespace Rat

instance instField : Field ℚ where
  __ := commRing
  __ := commGroupWithZero

instance instDivisionRing : DivisionRing ℚ := inferInstance

/-- Reciprocals preserve nonnegativity on their nonzero domain. -/
protected theorem reciprocal_nonneg {a : ℚ} (ha : 0 ≤ a) (hn : a ≠ 0) :
    0 ≤ Rat.reciprocal a hn := by
  apply Rat.num_nonneg.mp
  rw [Rat.reciprocal, Rat.fractionInt, Rat.num_normalize]
  apply Int.ediv_nonneg
  · exact Int.mul_nonneg (Int.sign_nonneg_iff.mpr (Rat.num_nonneg.mpr ha))
      (Int.natCast_nonneg _)
  · exact Int.natCast_nonneg _

end Rat

namespace NNRat

/-- A concrete nonzero rational unit, with its inverse constructed from normalized data. -/
def unit (q : ℚ≥0) (hq : q ≠ 0) : (ℚ≥0)ˣ := by
  have hn : (q : ℚ) ≠ 0 := fun h => hq (Subtype.ext h)
  exact {
    val := q
    inv := ⟨Rat.reciprocal (q : ℚ) hn, Rat.reciprocal_nonneg q.2 hn⟩
    val_inv := Subtype.ext (Rat.mul_reciprocal (q : ℚ) hn)
    inv_val := Subtype.ext (Rat.reciprocal_mul (q : ℚ) hn) }

@[simp] theorem coe_unit (q : ℚ≥0) (hq : q ≠ 0) : (unit q hq : ℚ≥0) = q := rfl

instance instSemifield : Semifield ℚ≥0 where
  __ := (inferInstance : CommSemiring ℚ≥0)
  __ := NNRat.instNontrivial
  isUnit_of_ne_zero {q} hq := ⟨unit q hq, rfl⟩

theorem divNat_mul_den (n d : ℕ) (hd : d ≠ 0) :
    divNat n d hd * (d : ℚ≥0) = (n : ℚ≥0) := by
  apply NNRat.ext
  simpa only [NNRat.coe_mul, NNRat.coe_natCast, NNRat.coe_divNat, Int.cast_natCast] using
    Rat.fraction_mul_den (n : ℤ) d hd

theorem divNat_eq_divp (n d : ℕ) (hd : d ≠ 0) :
    divNat n d hd = (n : ℚ≥0) /ₚ Units.mk0 (d : ℚ≥0) (Nat.cast_ne_zero.mpr hd) :=
  eq_divp_iff_mul_eq.mpr (divNat_mul_den n d hd)

/-- Reconstruct a nonnegative rational by division by its denominator unit. -/
theorem num_div_den (q : ℚ≥0) :
    (q.num : ℚ≥0) /ₚ Units.mk0 (q.den : ℚ≥0) (Nat.cast_ne_zero.mpr q.den_ne_zero) = q := by
  apply divp_eq_iff_mul_eq.mpr
  exact mul_den_eq_num q

end NNRat

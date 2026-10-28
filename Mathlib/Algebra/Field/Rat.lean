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

This file contains the field instance on the rational numbers and the semifield instance on the
nonnegative rational numbers. Inverses, quotients and integer powers on `ℚ` and `ℚ≥0` are the
checked operations of a group with zero: `q⁻¹` requires evidence that `q` is a unit.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

@[expose] public section

namespace Rat

instance instField : Field ℚ where
  __ := commRing
  __ := commGroupWithZero
  nnratCastOfCharZero _ q := q
  nnratCastOfCharZero_mul_den _ q := by
    simpa only [NNRat.num_coe, NNRat.den_coe, Int.cast_natCast] using Rat.mul_den_eq_num (q : ℚ)
  ratCastOfCharZero _ q := q
  ratCastOfCharZero_mul_den _ q := Rat.mul_den_eq_num q

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

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

protected lemma inv_nonneg {a : ℚ} {haUnit : IsUnit a} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right₀ (Rat.mul_reciprocal a haUnit.ne_zero)]
  exact Rat.reciprocal_nonneg ha haUnit.ne_zero

protected lemma div_nonneg {a b : ℚ} {hbUnit : IsUnit b} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a / b := by
  rw [div_eq_mul_inv₀]
  exact Rat.mul_nonneg ha (Rat.inv_nonneg hb)

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
  nnratCastOfCharZero _ q := q
  nnratCastOfCharZero_mul_den _ q := NNRat.mul_den_eq_num q

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) {hq : IsUnit q} : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right₀
  rw [← coe_mul, mul_inv_cancel₀, coe_one]

@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) {hq : IsUnit q} : ((p / q : ℚ≥0) : ℚ) = p / q := by
  rw [div_eq_mul_inv₀, coe_mul, coe_inv, div_eq_mul_inv₀]

@[simp, norm_cast] lemma coe_zpow (p : ℚ≥0) (n : ℤ) {h : n < 0 → IsUnit p} :
    ((p ^ n : ℚ≥0) : ℚ) = (p : ℚ) ^ n := by
  match n with
  | .ofNat k => exact coe_pow p k
  | .negSucc k =>
    rw [zpow_negSucc₀, zpow_negSucc₀, coe_inv]
    simp only [coe_pow]

theorem divNat_mul_den (n d : ℕ) (hd : d ≠ 0) :
    divNat n d hd * (d : ℚ≥0) = (n : ℚ≥0) := by
  apply NNRat.ext
  simpa only [NNRat.coe_mul, NNRat.coe_natCast, NNRat.coe_divNat, Int.cast_natCast] using
    Rat.fraction_mul_den (n : ℤ) d hd

theorem divNat_eq_div (a b : ℕ) (hb : b ≠ 0) : divNat a b hb = a / b :=
  eq_div_of_mul_eq (divNat_mul_den a b hb)

lemma inv_def (q : ℚ≥0) {hq : IsUnit q} :
    q⁻¹ = divNat q.den q.num (num_ne_zero.mpr hq.ne_zero) := by
  apply inv_eq_of_mul_eq_one_right₀
  rw [divNat_eq_div, ← mul_div_assoc₀, mul_den_eq_num, div_self]

lemma div_def (p q : ℚ≥0) {hq : IsUnit q} :
    p / q = divNat (p.num * q.den) (p.den * q.num)
      (Nat.mul_ne_zero p.den_ne_zero (num_ne_zero.mpr hq.ne_zero)) := by
  rw [div_eq_mul_inv₀, inv_def,
    ← divNat_mul_divNat _ _ p.den_ne_zero (num_ne_zero.mpr hq.ne_zero), num_divNat_den]

lemma num_inv_of_ne_zero {q : ℚ≥0} {hq : IsUnit q} : q⁻¹.num = q.den := by
  rw [inv_def]
  change (Rat.normalize (q.den : ℤ) q.num (num_ne_zero.mpr hq.ne_zero)).num.natAbs = q.den
  rw [Rat.normalize_eq_mk' _ _ _ (by simpa using q.coprime_num_den.symm)]
  simp

lemma den_inv_of_ne_zero {q : ℚ≥0} {hq : IsUnit q} : q⁻¹.den = q.num := by
  rw [inv_def]
  change (Rat.normalize (q.den : ℤ) q.num (num_ne_zero.mpr hq.ne_zero)).den = q.num
  rw [Rat.normalize_eq_mk' _ _ _ (by simpa using q.coprime_num_den.symm)]

@[simp]
lemma num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  rw [← divNat_eq_div _ _ q.den_ne_zero, num_divNat_den]

end NNRat

theorem NNRatCast.ofScientific_eq_ite {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      if b = true then NNRat.divNat m (10 ^ d) (pow_ne_zero d (by decide))
      else ↑(m * 10 ^ d) := by
  rw [NNRatCast.toOfScientific_def]
  split_ifs with hb
  · congr 1
    apply NNRat.ext
    change Rat.ofScientific m b d = Rat.fraction m (10 ^ d) (pow_ne_zero d (by decide))
    rw [Rat.ofScientific, ite_eq_left hb]
    rfl
  · congr 1
    apply NNRat.ext
    change Rat.ofScientific m b d = ((m * 10 ^ d : ℕ) : ℚ)
    rw [Rat.ofScientific, ite_eq_right hb]

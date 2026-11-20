/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The rational numbers are a commutative ring

This file contains the commutative ring instance on the rational numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists IsOrderedMonoid Field PNat Nat.gcd_greatest

namespace Rat

/-! ### Instances -/

instance commRing : CommRing ℚ where
  __ := addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := Rat.natCast_add n 1

instance commGroupWithZero : CommGroupWithZero ℚ where
  __ := commRing
  __ := Rat.nontrivial
  isUnit_of_ne_zero {q} hq :=
    ⟨⟨q, Rat.reciprocal q hq, Rat.mul_reciprocal q hq, Rat.reciprocal_mul q hq⟩, rfl⟩

instance isDomain : IsDomain ℚ := NoZeroDivisors.to_isDomain _
/-- The characteristic of `ℚ` is 0. -/
@[stacks 09FS "Second part."]
instance instCharZero : CharZero ℚ where cast_injective a b hab := by simpa using congr_arg num hab

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance commSemiring : CommSemiring ℚ := by infer_instance
instance semiring : Semiring ℚ := by infer_instance

/-! ### Miscellaneous lemmas -/

@[simp] lemma mul_den_eq_num (q : ℚ) : q * q.den = q.num := by
  simp only [Rat.mul_def, Rat.num_natCast, Rat.den_natCast, Nat.mul_one]
  have h := Rat.normalize_mul_right (n := q.num) (d := 1) (a := q.den)
    (by decide) q.den_nz
  simpa only [Nat.one_mul, Rat.normalize_eq, Nat.gcd_one_right, Int.natCast_one, Int.ediv_one,
    Nat.div_one, Rat.mk_den_one] using h

@[simp] lemma den_mul_eq_num (q : ℚ) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

/-- A checked fraction satisfies its original numerator-denominator equation. -/
theorem fraction_mul_den (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    fraction n d hd * (d : ℚ) = (n : ℚ) := by
  obtain ⟨g, _, hn, he⟩ := Rat.normalize_num_den' n d hd
  have hn' := congrArg (fun x : ℤ => (x : ℚ)) hn
  have he' := congrArg (fun x : ℕ => (x : ℚ)) he
  simp only [Int.cast_mul, Int.cast_natCast] at hn'
  simp only [Rat.natCast_mul] at he'
  calc
    _ = fraction n d hd * ((fraction n d hd).den : ℚ) * (g : ℚ) := by
      conv => lhs; rhs; rw [he']
      simp only [fraction, mul_assoc]
    _ = (n : ℚ) := by rw [mul_den_eq_num]; exact hn'.symm

theorem fraction_eq_div (n : ℤ) (d : ℕ) (hd : d ≠ 0) : fraction n d hd = n / d :=
  eq_div_iff.mpr (fraction_mul_den n d hd)

/-- A checked fraction with an integer denominator satisfies its signed numerator equation. -/
theorem fractionInt_mul_den (n d : ℤ) (hd : d ≠ 0) :
    fractionInt n d hd * (d : ℚ) = (n : ℚ) := by
  have hs : (d.sign : ℚ) ≠ 0 := fun h ↦
    hd (Int.sign_eq_zero_iff_zero.mp (intCast_injective (h.trans Int.cast_zero.symm)))
  apply mul_right_cancel₀ hs
  rw [mul_assoc, ← Int.cast_mul d d.sign, Int.mul_sign_self, Int.cast_natCast]
  change fraction (d.sign * n) d.natAbs (Int.natAbs_ne_zero.mpr hd) *
      (d.natAbs : ℚ) = (n : ℚ) * (d.sign : ℚ)
  rw [fraction_mul_den, Int.cast_mul, mul_comm]

theorem fractionInt_eq_div (n d : ℤ) (hd : d ≠ 0) :
    fractionInt n d hd = (n : ℚ) / (d : ℚ) :=
  eq_div_iff.mpr (fractionInt_mul_den n d hd)

lemma num_div_den (r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r :=
  div_eq_iff.mpr (mul_den_eq_num r).symm

end Rat

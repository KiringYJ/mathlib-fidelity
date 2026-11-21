/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Euclidean division on fields

* `Field.toEuclideanDomain`: explicitly equips a field with Euclidean quotient and remainder.

The explicit construction uses checked field division on the nonzero domain of the quotient.
-/

public section

namespace Field

variable {K : Type*} [Field K]

/-- Equip a field with Euclidean division, explicitly selecting the Euclidean quotient contract. -/
@[expose, instance_reducible]
noncomputable def toEuclideanDomain : EuclideanDomain K := by
  classical
  exact
    { toCommRing := toCommRing
      quotient := fun a b hb => Checked.div a b hb.isUnit
      remainder := fun a b => if b = 0 then a else 0
      remainder_zero := fun a => by simp
      quotient_mul_add_remainder_eq := fun a b hb => by
        simp only [ite_eq_right hb, add_zero]
        exact mul_div_cancel₀ a
      r := fun a b => a = 0 ∧ b ≠ 0
      r_wellFounded :=
        WellFounded.intro fun _ =>
          (Acc.intro _) fun _ ⟨hb, _⟩ => (Acc.intro _) fun _ ⟨_, hnb⟩ => False.elim <| hnb hb
      remainder_lt := fun a b hnb => by simp [hnb]
      mul_left_not_lt := fun _ _ hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }

attribute [local instance] toEuclideanDomain

open Classical in
@[simp]
protected theorem mod_eq (a b : K) : a % b = if b = 0 then a else 0 := by
  classical
  rfl

/-- Euclidean quotient agrees with field division for a nonzero divisor. -/
protected theorem quotient_eq_div (a : K) {b : K} (hb : b ≠ 0) :
    EuclideanDomain.quotient a b hb = a / b :=
  rfl

@[simp]
protected theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]

protected theorem gcd_zero_eq [DecidableEq K] (b : K) :
    EuclideanDomain.gcd 0 b = b := by
  rw [Field.gcd_eq, ite_eq_left rfl]

protected theorem gcd_eq_of_ne [DecidableEq K] {a : K} (ha : a ≠ 0) (b : K) :
    EuclideanDomain.gcd a b = a := by
  rw [Field.gcd_eq, ite_eq_right ha]

end Field

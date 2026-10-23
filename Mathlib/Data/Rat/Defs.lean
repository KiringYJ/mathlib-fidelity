/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Attr.Core

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib/Algebra/Field/Rat.lean`
once the `Field` class has been defined.

## Main Definitions

- `Rat.fraction n d hd` constructs a rational from an integer numerator and a nonzero
  natural denominator.
- `Rat.fractionInt n d hd` permits a nonzero integer denominator.

-/

@[expose] public section

-- TODO: If `Inv` was defined earlier than `Algebra.Group.Defs`, we could have
-- assert_not_exists Monoid
assert_not_exists MonoidWithZero Lattice PNat Nat.gcd_greatest

open Function

namespace Rat
variable {q : ℚ}

theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz

lemma mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl

lemma intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num
lemma natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1

@[simp high, norm_cast] lemma intCast_eq_one_iff {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj

@[simp high, norm_cast] lemma natCast_eq_one_iff {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj

@[simp] lemma mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

lemma num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not

@[simp] lemma den_ne_zero (q : ℚ) : q.den ≠ 0 := q.den_pos.ne'

lemma mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul_left h₂₁).mul_right (h₁₂.mul_left hnd₂)) := by
  rw [mul_def]; simp [mk_eq_normalize]

lemma mul_eq_fraction (q r : ℚ) :
    q * r = fraction (q.num * r.num) (q.den * r.den) (Nat.mul_ne_zero q.den_nz r.den_nz) :=
  mul_def q r

lemma pow_eq_fraction (q : ℚ) (n : ℕ) :
    q ^ n = fraction (q.num ^ n) (q.den ^ n) (by simp [Nat.pow_eq_zero, q.den_nz]) := by
  rw [pow_def, fraction, ← mk_eq_normalize]

@[simp] lemma mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  intro h
  have := congrArg Rat.num h
  contradiction

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Basic.Real.Basic
instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

instance addCommGroup : AddCommGroup ℚ where
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q = _
    rw [Rat.intCast_add, Rat.add_mul, Rat.intCast_one, Rat.one_mul]
    rfl
  zsmul_zero' := Rat.zero_mul
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; simp [Rat.add_mul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [Int.negSucc_eq, Rat.intCast_neg, Rat.neg_mul]; rfl

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ where
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

@[simp]
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

-- Not `@[simp]` as `num_ofNat` is stronger.
theorem num_zero : Rat.num 0 = 0 :=
  rfl

-- Not `@[simp]` as `den_ofNat` is stronger.
theorem den_zero : Rat.den 0 = 1 :=
  rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := Rat.num_eq_zero.mp hq

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

-- `Not `@[simp]` as `num_ofNat` is stronger.
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
theorem den_one : (1 : ℚ).den = 1 :=
  rfl

section Casts

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  have h := Rat.normalize_self q
  simpa only [hq, Rat.normalize_eq, Nat.gcd_one_right, Int.natCast_one, Int.ediv_one, Nat.div_one,
    Rat.mk_den_one] using h

lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

@[deprecated (since := "2026-06-06")] alias coe_int_inj := intCast_inj

end Casts

/-- Eliminate a rational into its numerator and its nonzero natural denominator. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def divCasesOn {C : ℚ → Sort*} (a : ℚ)
    (div : ∀ (n : ℤ) (d : ℕ) (hd : d ≠ 0), n.natAbs.Coprime d → C (fraction n d hd)) : C a :=
  a.casesOn fun n d nz red => by
    rw [Rat.mk_eq_normalize]
    exact div n d nz red

end Rat

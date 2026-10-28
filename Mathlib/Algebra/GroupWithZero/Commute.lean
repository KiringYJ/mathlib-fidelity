/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Commute

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

/-- For invertible `a`, the inverse `a⁻¹` commutes with `b` if and only if `a` does. -/
@[simp]
theorem inv_left_iff₀ {ha : IsUnit a} : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀

theorem inv_left₀ {ha : IsUnit a} (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

variable (a) in
theorem inv_left_self₀ {ha : IsUnit a} : Commute a⁻¹ a :=
  (Commute.refl a).inv_left₀

/-- For invertible `b`, the element `a` commutes with `b⁻¹` if and only if it commutes with `b`. -/
@[simp]
theorem inv_right_iff₀ {hb : IsUnit b} : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀

theorem inv_right₀ {hb : IsUnit b} (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

variable (a) in
theorem inv_right_self₀ {ha : IsUnit a} : Commute a a⁻¹ :=
  (Commute.refl a).inv_right₀

@[simp]
theorem div_right {hc : IsUnit c} (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  SemiconjBy.div_right hab hac

@[simp]
theorem div_left {hb : IsUnit b} (hac : Commute a c) (hbc : Commute b c) :
    Commute (a / b) c := by
  rw [div_eq_mul_inv₀]
  exact hac.mul_left hbc.inv_left₀

end Monoid

end Commute

theorem pow_inv_comm₀ {M : Type*} [Monoid M] (a : M) {ha : IsUnit a} (m n : ℕ) :
    a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

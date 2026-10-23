/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Theorems about invertible elements in a `GroupWithZero`

We intentionally keep imports minimal here as this file is used by `Mathlib/Tactic/NormNum.lean`.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

universe u

variable {α : Type u}

theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

instance (priority := 100) Invertible.toNeZero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨Invertible.ne_zero a⟩

section GroupWithZero
variable [GroupWithZero α]

/-- A nonzero element has an inverse, obtained from its unit witness. -/
@[instance_reducible]
noncomputable def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨↑(Units.mk0 a h)⁻¹, (Units.mk0 a h).inv_mul, (Units.mk0 a h).mul_inv⟩

/-- The inverse supplied by `Invertible` agrees with inversion of the checked unit. -/
theorem invOf_eq_mk0_inv (a : α) [Invertible a] :
    ⅟a = (↑(Units.mk0 a (Invertible.ne_zero a))⁻¹ : α) :=
  invOf_eq_right_inv (Units.mk0 a (Invertible.ne_zero a)).mul_inv

end GroupWithZero

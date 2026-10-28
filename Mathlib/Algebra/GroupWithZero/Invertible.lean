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

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
@[instance_reducible]
noncomputable def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel₀, mul_inv_cancel₀⟩

@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv mul_inv_cancel₀

/-- `a` is the inverse of `a⁻¹` -/
instance invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, mul_inv_cancel₀, inv_mul_cancel₀⟩

/-- `b / a` is the inverse of `a / b` -/
@[instance_reducible]
noncomputable def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by rw [← mul_div_assoc₀, div_mul_cancel₀, div_self],
    by rw [← mul_div_assoc₀, div_mul_cancel₀, div_self]⟩

theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟(a / b) = b / a :=
  invOf_eq_right_inv (by rw [← mul_div_assoc₀, div_mul_cancel₀, div_self])

end GroupWithZero

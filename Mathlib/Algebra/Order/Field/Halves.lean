/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Checked
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Halving and density in ordered semifields

The denominator is the unit represented by `2`; no ambient division instance is needed.
-/

public section

variable {α : Type*}

section Semifield
variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b : α}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

theorem half_pos (h : 0 < a) : 0 < Checked.div a 2 :=
  Checked.div_pos h zero_lt_two

theorem one_half_pos : (0 : α) < Checked.div (1 : α) 2 := half_pos zero_lt_one

@[simp] theorem half_le_self_iff : Checked.div a 2 ≤ a ↔ 0 ≤ a := by
  rw [Checked.div_le_iff (zero_lt_two' α), mul_two, le_add_iff_nonneg_left]

@[simp] theorem half_lt_self_iff : Checked.div a 2 < a ↔ 0 < a := by
  rw [Checked.div_lt_iff (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff
alias ⟨_, half_lt_self⟩ := half_lt_self_iff
alias div_two_lt_of_pos := half_lt_self

theorem one_half_lt_one : Checked.div (1 : α) 2 < 1 := half_lt_self zero_lt_one

theorem two_inv_lt_one : Checked.inv (2 : α) < 1 := by
  simpa only [Checked.div, Checked.inv, divp, one_mul] using (one_half_lt_one (α := α))

theorem left_lt_add_div_two : a < Checked.div (a + b) 2 ↔ a < b := by
  rw [Checked.lt_div_iff (zero_lt_two' α), mul_two, add_lt_add_iff_left]

theorem add_div_two_lt_right : Checked.div (a + b) 2 < b ↔ a < b := by
  rw [Checked.div_lt_iff (zero_lt_two' α), mul_two, add_lt_add_iff_right]

omit [PosMulReflectLT α] in
theorem add_thirds (a : α) : Checked.div a 3 + Checked.div a 3 + Checked.div a 3 = a := by
  change a /ₚ Units.mk0 3 three_ne_zero + a /ₚ Units.mk0 3 three_ne_zero +
    a /ₚ Units.mk0 3 three_ne_zero = a
  rw [Units.divp_add_divp_same, Units.divp_add_divp_same]
  apply divp_eq_iff_mul_eq.mpr
  change a * 3 = a + a + a
  rw [← two_add_one_eq_three, mul_add, mul_two, mul_one]

instance (priority := 100) LinearOrderedSemiField.toDenselyOrdered :
    DenselyOrdered α where
  dense a b hab :=
    ⟨Checked.div (a + b) 2, left_lt_add_div_two.mpr hab, add_div_two_lt_right.mpr hab⟩

end Semifield

section Field
variable [Field α] [PartialOrder α] [IsStrictOrderedRing α]

theorem sub_self_div_two (a : α) : a - Checked.div a 2 = Checked.div a 2 := sub_half a

theorem div_two_sub_self (a : α) : Checked.div a 2 - a = -(Checked.div a 2) := half_sub a

end Field

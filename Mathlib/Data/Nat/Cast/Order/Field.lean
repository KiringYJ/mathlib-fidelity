/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Cast of naturals into ordered fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a `LinearOrderedSemifield`.

## Main results

* `Nat.cast_div_le`: for nonzero `n`, `↑(m / n) ≤ ↑m / ↑ n`
-/

public section


namespace Nat

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

lemma cast_inv_le_one (n : ℕ) {hn : IsUnit (n : α)} : (n⁻¹ : α) ≤ 1 :=
  inv_le_one_of_one_le₀ <| n.one_le_cast_iff_ne_zero.mpr <| Nat.cast_ne_zero.mp hn.ne_zero

/-- Natural division is at most division in the field. -/
theorem cast_div_le {m n : ℕ} {hn : IsUnit (n : α)} : ((m / n : ℕ) : α) ≤ m / n := by
  rw [le_div_iff₀ ((Nat.cast_nonneg n).lt_of_ne' hn.ne_zero), ← Nat.cast_mul, @Nat.cast_le]
  exact Nat.div_mul_le_self m _

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div₀]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_cast_pos {n : ℕ} {hn : IsUnit (n : α)} : 0 < 1 / (n : α) :=
  one_div_pos.mpr ((cast_nonneg n).lt_of_ne' hn.ne_zero)

theorem one_div_cast_nonneg (n : ℕ) {hn : IsUnit (n : α)} : 0 ≤ 1 / (n : α) :=
  one_div_nonneg.mpr (cast_nonneg' n)

theorem one_div_cast_ne_zero {n : ℕ} {hn : IsUnit (n : α)} : 1 / (n : α) ≠ 0 :=
  _root_.ne_of_gt one_div_cast_pos

end LinearOrderedSemifield

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem one_sub_one_div_cast_nonneg [AddRightMono α] (n : ℕ) {hn : IsUnit (n : α)} :
    0 ≤ 1 - 1 / (n : α) := by
  rw [sub_nonneg, one_div₀]
  exact cast_inv_le_one n

theorem one_sub_one_div_cast_le_one [AddLeftMono α] (n : ℕ) {hn : IsUnit (n : α)} :
    1 - 1 / (n : α) ≤ 1 := by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n

end LinearOrderedField

end Nat

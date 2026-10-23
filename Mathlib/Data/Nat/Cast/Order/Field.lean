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

attribute [local simp] cast_add_one_ne_zero

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

lemma cast_inv_le_one (n : ℕ) (hn : n ≠ 0) : (n⁻¹ : α) ≤ 1 := by
  have hp : (0 : α) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simpa only [Checked.inv_one] using
    (Checked.inv_le_inv (ha := (Nat.cast_ne_zero.mpr hn : (n : α) ≠ 0).isUnit)
      (hb := isUnit_one) (a := (n : α)) (b := 1) hp zero_lt_one).mpr
      (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn))

/-- Natural division by a nonzero denominator is bounded by division in the field. -/
theorem cast_div_le {m n : ℕ} (hn : n ≠ 0) : ((m / n : ℕ) : α) ≤ m / n := by
  rw [Checked.le_div_iff (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
    ← Nat.cast_mul, Nat.cast_le]
  exact Nat.div_mul_le_self m n

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  Checked.inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [Checked.one_div]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine Checked.div_le_div_of_nonneg_left zero_le_one ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine Checked.div_lt_div_of_pos_left zero_lt_one ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_cast_pos {n : ℕ} (hn : n ≠ 0) : 0 < 1 / (n : α) :=
  Checked.div_pos zero_lt_one (cast_pos.mpr (Nat.pos_of_ne_zero hn))

theorem one_div_cast_nonneg (n : ℕ) (hn : n ≠ 0) : 0 ≤ 1 / (n : α) :=
  Checked.div_nonneg zero_le_one (cast_nonneg' n)

theorem one_div_cast_ne_zero {n : ℕ} (hn : n ≠ 0) : 1 / (n : α) ≠ 0 :=
  _root_.ne_of_gt (one_div_cast_pos hn)

end LinearOrderedSemifield

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem one_sub_one_div_cast_nonneg [AddRightMono α] (n : ℕ) (hn : n ≠ 0) :
    0 ≤ 1 - 1 / (n : α) := by
  rw [sub_nonneg, Checked.one_div]
  exact cast_inv_le_one n hn

theorem one_sub_one_div_cast_le_one [AddLeftMono α] (n : ℕ) (hn : n ≠ 0) : 1 - 1 / (n : α) ≤ 1 := by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n hn

end LinearOrderedField

end Nat

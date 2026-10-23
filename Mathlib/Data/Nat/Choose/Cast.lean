/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/

public section


open Nat

variable (K : Type*)

namespace Nat

attribute [local simp] factorial_ne_zero
section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

theorem cast_choose {a b : ℕ} (h : a ≤ b) : (b.choose a : K) = b ! / (a ! * (b - a)!) := by
  rw [Checked.eq_div_iff_mul_eq]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]

theorem cast_add_choose {a b : ℕ} : ((a + b).choose a : K) = (a + b)! / (a ! * b !) := by
  simpa only [Nat.add_sub_cancel_left] using cast_choose K (le_add_right a b)

end DivisionSemiring

section DivisionRing
variable [DivisionRing K] [NeZero (2 : K)]

theorem cast_choose_two (a : ℕ) : (a.choose 2 : K) = a * (a - 1) / 2 := by
  rw [← cast_descFactorial_two, descFactorial_eq_factorial_mul_choose, factorial_two, mul_comm,
    cast_mul, cast_two, Checked.eq_div_iff_mul_eq]

end DivisionRing
end Nat

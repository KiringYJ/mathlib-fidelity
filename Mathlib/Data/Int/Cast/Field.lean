/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Lean.Elab.NativeDivision

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

* `Int.cast_div`: casting an exact integer quotient agrees with division by the cast denominator
  when that denominator is nonzero.
-/

public section


namespace Int

open Nat

variable {α : Type*}

/-- Auxiliary lemma for `norm_cast` to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `DivisionRing` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
theorem cast_neg_natCast {R} [DivisionRing R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp

@[simp]
theorem cast_div [DivisionRing α] {m n : ℤ} (n_dvd : n ∣ m) (hn : (n : α) ≠ 0) :
    (Int.exactQuotient m n n_dvd (fun h => hn (h ▸ Int.cast_zero)) : α) =
      (m : α) / (n : α) := by
  rw [eq_div_iff, ← Int.cast_mul, Int.mul_comm, Int.mul_exactQuotient]

end Int

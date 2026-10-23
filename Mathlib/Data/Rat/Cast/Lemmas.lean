/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Characteristic-zero rational cast lemmas
-/

public section

namespace Rat
variable {α : Type*} [DivisionRing α] [CharZero α]

@[simp, norm_cast] theorem cast_pow (p : ℚ) (n : ℕ) : ((p^n : ℚ) : α) = (p : α)^n :=
  (castHom α).map_pow p n

/-- A rational embedding preserves division by a unit. -/
theorem cast_divp (p : ℚ) (u : ℚˣ) :
    ((p /ₚ u : ℚ) : α) = (p : α) /ₚ Units.map (Rat.castHom α).toMonoidHom u :=
  map_divp (Rat.castHom α).toMonoidHom p u

/-- Casting the concrete reciprocal agrees with inversion of the corresponding unit. -/
theorem cast_reciprocal (q : ℚ) (hq : q ≠ 0) :
    ((reciprocal q hq : ℚ) : α) =
      ↑((Units.mk0 (q : α) (cast_ne_zero.mpr hq))⁻¹) := by
  apply mul_right_cancel₀ (cast_ne_zero.mpr hq)
  rw [← cast_mul, reciprocal_mul, cast_one]
  exact (Units.inv_mul _).symm

@[simp, norm_cast] theorem cast_nnratCast (q : ℚ≥0) : ((q : ℚ) : α) = (q : α) := by
  simp only [Rat.cast_def, NNRat.cast_def, Rat.eval, NNRat.eval,
    NNRat.num_coe, NNRat.den_coe, Int.cast_natCast]

end Rat

namespace NNRat

@[simp, norm_cast] theorem cast_pow {α : Type*} [DivisionSemiring α] [CharZero α]
    (q : ℚ≥0) (n : ℕ) : ((q^n : ℚ≥0) : α) = (q : α)^n :=
  (castHom α).map_pow q n

@[simp] theorem cast_mk {α : Type*} [DivisionRing α] [CharZero α] (q : ℚ) (h : 0 ≤ q) :
    (NNRat.cast ⟨q, h⟩ : α) = (q : α) := (Rat.cast_nnratCast ⟨q, h⟩).symm

end NNRat

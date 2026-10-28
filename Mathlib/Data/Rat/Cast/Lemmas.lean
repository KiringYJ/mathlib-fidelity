/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Nonneg.Field
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Basic

/-!
# Characteristic-zero rational cast lemmas
-/

public section

namespace Rat
variable {α : Type*} [DivisionRing α] [CharZero α]

@[simp, norm_cast] theorem cast_pow (p : ℚ) (n : ℕ) : ((p^n : ℚ) : α) = (p : α)^n :=
  (castHom α).map_pow p n

theorem cast_inv_nat (n : ℕ) {hn : IsUnit (n : ℚ)} : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right₀
  rw [← cast_natCast (α := α) n, ← cast_mul, mul_inv_cancel₀, cast_one]

theorem cast_inv_int (n : ℤ) {hn : IsUnit (n : ℚ)} : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right₀
  rw [← cast_intCast (α := α) n, ← cast_mul, mul_inv_cancel₀, cast_one]

@[simp, norm_cast] theorem cast_nnratCast (q : ℚ≥0) : ((q : ℚ) : α) = (q : α) := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : α) ≠ 0)
  have h := Rat.cast_mul_den (α := α) (q : ℚ)
  rw [NNRat.den_coe, NNRat.num_coe, Int.cast_natCast] at h
  rw [h, NNRat.cast_mul_den]

/-- Casting a scientific literal via `ℚ` is the same as casting directly. -/
@[simp, norm_cast]
theorem cast_ofScientific {K : Type*} [DivisionRing K] [CharZero K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K), ← NNRat.cast_ofScientific, cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast] theorem cast_pow {α : Type*} [DivisionSemiring α] [CharZero α]
    (q : ℚ≥0) (n : ℕ) : ((q^n : ℚ≥0) : α) = (q : α)^n :=
  (castHom α).map_pow q n

@[simp] theorem cast_mk {α : Type*} [DivisionRing α] [CharZero α] (q : ℚ) (h : 0 ≤ q) :
    (NNRat.cast ⟨q, h⟩ : α) = (q : α) := (Rat.cast_nnratCast ⟨q, h⟩).symm

open OfScientific in
theorem Nonneg.coe_ofScientific {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (s : Bool) (e : ℕ) :
    (ofScientific m s e : {x : K // 0 ≤ x}).val = ofScientific m s e :=
  _root_.Nonneg.coe_nnratCast _

end NNRat

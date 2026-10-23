/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

* `Nat.cast_div`: if `n` divides `m` and its image is nonzero, then natural division
  agrees with division by the corresponding unit.
-/

public section


namespace Nat

variable {K : Type*} [DivisionSemiring K] {d m n : ℕ}

@[simp]
lemma cast_div (hnm : n ∣ m) (hn : (n : K) ≠ 0) :
    (↑(m / n) : K) = (m : K) /ₚ Units.mk0 (n : K) hn := by
  apply eq_divp_iff_mul_eq.mpr
  change (↑(m / n) : K) * (n : K) = (m : K)
  rw [← Nat.cast_mul, Nat.div_mul_cancel hnm]

variable [CharZero K]

@[simp]
lemma cast_div_charZero (hnm : n ∣ m) (hn : n ≠ 0) :
    (↑(m / n) : K) = (m : K) /ₚ Units.mk0 (n : K) (Nat.cast_ne_zero.mpr hn) :=
  cast_div hnm (Nat.cast_ne_zero.mpr hn)

/-- A nonzero multiple has a nonzero natural quotient by its divisor. -/
lemma cast_div_ne_zero (hnm : n ∣ m) (hm : m ≠ 0) : (↑(m / n) : K) ≠ 0 := by
  apply Nat.cast_ne_zero.mpr
  intro hq
  apply hm
  have h := Nat.div_mul_cancel hnm
  simpa only [hq, Nat.zero_mul] using h.symm

lemma cast_div_div_div_cancel_right (hn : d ∣ n) (hm : d ∣ m) (hn0 : n ≠ 0) :
    (↑(m / d) : K) /ₚ Units.mk0 (↑(n / d) : K) (cast_div_ne_zero hn hn0) =
      (m : K) /ₚ Units.mk0 (n : K) (Nat.cast_ne_zero.mpr hn0) := by
  apply eq_divp_iff_mul_eq.mpr
  change ((↑(m / d) : K) /ₚ Units.mk0 (↑(n / d) : K) (cast_div_ne_zero hn hn0)) *
    (n : K) = (m : K)
  have hn' : (n : K) = (↑(n / d) : K) * (d : K) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hn]
  rw [hn', ← mul_assoc]
  have hc := divp_mul_cancel (↑(m / d) : K)
    (Units.mk0 (↑(n / d) : K) (cast_div_ne_zero hn hn0))
  simp only [Units.val_mk0] at hc
  rw [hc, ← Nat.cast_mul, Nat.div_mul_cancel hm]

end Nat

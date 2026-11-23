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

* `Nat.cast_div`: if `n` divides `m` and its image is nonzero, then the cast of the natural
  quotient `Nat.euclideanDiv m n` agrees with division of the casts by the unit represented by `n`.
-/

public section


namespace Nat

variable {K : Type*} [DivisionSemiring K] {d m n : ℕ}

@[simp]
lemma cast_div (hnm : n ∣ m) (hn : (n : K) ≠ 0) :
    (Nat.euclideanDiv m n (fun he => hn (he ▸ Nat.cast_zero)) : K) =
      Checked.div (m : K) (n : K) hn.isUnit := by
  have hn' : n ≠ 0 := fun he => hn (he ▸ Nat.cast_zero)
  rw [eq_div_iff, ← Nat.cast_mul, Nat.mul_comm, Nat.mul_euclideanDiv_cancel hn' hnm]

variable [CharZero K]

@[norm_cast]
lemma cast_div_charZero (hnm : n ∣ m) (hn : n ≠ 0) :
    (Nat.euclideanDiv m n hn : K) = Checked.div (m : K) (n : K) (Nat.cast_ne_zero.mpr hn).isUnit :=
  cast_div hnm (Nat.cast_ne_zero.mpr hn)

/-- A nonzero multiple has a nonzero natural quotient by its divisor. -/
lemma cast_div_ne_zero (hnm : n ∣ m) (hm : m ≠ 0) :
    (Nat.euclideanDiv m n (fun he => hm (Nat.eq_zero_of_zero_dvd (he ▸ hnm))) : K) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
    (Nat.euclideanDiv_pos (fun he => hm (Nat.eq_zero_of_zero_dvd (he ▸ hnm)))
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hnm)))

/- Evidence for a quotient by a natural quotient: a nonzero multiple has a nonzero quotient by its
divisor. -/
macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply Nat.cast_div_ne_zero) <;> assumption))

lemma cast_div_div_div_cancel_right (hn : d ∣ n) (hm : d ∣ m) (hn0 : n ≠ 0) :
    Checked.div (Nat.euclideanDiv m d (fun he => hn0 (Nat.eq_zero_of_zero_dvd (he ▸ hn))) : K)
      (Nat.euclideanDiv n d (fun he => hn0 (Nat.eq_zero_of_zero_dvd (he ▸ hn))) : K)
      (cast_div_ne_zero hn hn0).isUnit =
      Checked.div (m : K) (n : K) (Nat.cast_ne_zero.mpr hn0).isUnit := by
  have hd : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr fun h ↦ hn0 (Nat.eq_zero_of_zero_dvd (h ▸ hn))
  simp only [cast_div hm hd, cast_div hn hd]
  exact div_div_div_cancel_right₀ _ _

end Nat

/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Int.Cast.Field
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Cast.Pi

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/

public section

open Nat Set

variable {α β : Type*}

namespace Int

/-- Exact integer division is preserved when the denominator is nonzero. -/
@[norm_cast]
theorem cast_div_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℤ}
    (n_dvd : n ∣ m) (hn : n ≠ 0) :
    ((m / n : ℤ) : k) = m / n :=
  cast_div n_dvd (cast_ne_zero.mpr hn)

-- Necessary for confluence with `ofNat_ediv` and `cast_div_charZero`.
@[simp, norm_cast]
theorem cast_div_ofNat_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℕ}
    (n_dvd : n ∣ m) (hn : n ≠ 0) :
    (((m : ℤ) / (n : ℤ) : ℤ) : k) = m / n := by
  simpa only [cast_natCast] using
    (cast_div_charZero (k := k) (Int.ofNat_dvd.mpr n_dvd) (Int.ofNat_ne_zero.mpr hn))

end Int

theorem RingHom.injective_int {α : Type*} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective

namespace Function
variable [AddGroupWithOne β] [CharZero β] {n : ℤ}

lemma support_intCast (hn : n ≠ 0) : support (n : α → β) = univ :=
  support_const <| Int.cast_ne_zero.2 hn

lemma mulSupport_intCast (hn : n ≠ 1) : mulSupport (n : α → β) = univ :=
  mulSupport_const <| Int.cast_ne_one.2 hn

end Function

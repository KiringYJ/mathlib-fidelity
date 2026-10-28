/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# `ZMod p` is a field
-/

public section

namespace ZMod
variable (p : ℕ) [hp : Fact p.Prime]

/-- `ZMod p` does not have characteristic zero when `p` is prime. -/
theorem not_charZero : ¬CharZero (ZMod p) := fun h =>
  hp.out.ne_zero (h.cast_injective ((ZMod.natCast_self p).trans Nat.cast_zero.symm))

/-- Field structure on `ZMod p` if `p` is prime. Its characteristic is not zero, so it has no
rational embedding. -/
instance : Field (ZMod p) where
  isUnit_of_ne_zero {a} ha := by
    obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
    apply (isUnit_iff_coprime k p).2
    apply Nat.Coprime.symm
    rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]
  nnratCastOfCharZero h := (not_charZero p h).elim
  nnratCastOfCharZero_mul_den h := (not_charZero p h).elim
  nnqsmulOfCharZero h := (not_charZero p h).elim
  nnqsmulOfCharZero_eq_mul h := (not_charZero p h).elim
  ratCastOfCharZero h := (not_charZero p h).elim
  ratCastOfCharZero_mul_den h := (not_charZero p h).elim
  qsmulOfCharZero h := (not_charZero p h).elim
  qsmulOfCharZero_eq_mul h := (not_charZero p h).elim

/-- `ZMod p` is an integral domain when `p` is prime. -/
instance : IsDomain (ZMod p) := by constructor

end ZMod

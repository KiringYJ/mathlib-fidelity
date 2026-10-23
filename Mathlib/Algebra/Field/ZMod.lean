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

/-- Field structure on `ZMod p` if `p` is prime. -/
instance : Field (ZMod p) where
  isUnit_of_ne_zero {a} ha := by
    obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
    apply (isUnit_iff_coprime k p).2
    apply Nat.Coprime.symm
    rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]

/-- `ZMod p` is an integral domain when `p` is prime. -/
instance : IsDomain (ZMod p) := by constructor

end ZMod

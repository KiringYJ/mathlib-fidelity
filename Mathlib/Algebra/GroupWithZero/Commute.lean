/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Commute

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [MonoidWithZero G₀] {a b : G₀} {u : G₀ˣ}

/-- Commutation with a numerator and a unit denominator implies commutation with the quotient. -/
theorem divp_right (hab : Commute a b) (hau : Commute a (u : G₀)) :
    Commute a (b /ₚ u) :=
  SemiconjBy.divp_right hab hau

/-- A quotient by a unit commutes with an element commuting with both its factors. -/
theorem divp_left (hab : Commute a b) (hub : Commute (u : G₀) b) :
    Commute (a /ₚ u) b :=
  (hab.symm.divp_right hub.symm).symm

end Commute

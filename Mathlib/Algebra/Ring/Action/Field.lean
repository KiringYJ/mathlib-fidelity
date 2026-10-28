/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Group action on fields
-/

public section

variable {M} [Monoid M] {F} [DivisionRing F]

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. The invertibility of `x • m` is that of `m`, transported by the ring homomorphism
`m ↦ x • m`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) {hm : IsUnit m} :
    x • m⁻¹ = Checked.inv (x • m) (hm.map (MulSemiringAction.toRingHom M F x)) :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _

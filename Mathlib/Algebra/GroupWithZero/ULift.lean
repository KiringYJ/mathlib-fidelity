/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# `ULift` instances for groups and monoids with zero

This file defines instances for group and monoid with zero and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

public section

assert_not_exists Ring

universe u

variable {α : Type u}

namespace ULift

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) where
  __ := monoidWithZero
  isUnit_of_ne_zero {a} ha := by
    obtain ⟨u, hu⟩ := GroupWithZero.isUnit_of_ne_zero (Equiv.ulift.injective.ne ha)
    change (u : α) = a.down at hu
    exact ⟨⟨a, up ↑u⁻¹,
      Equiv.ulift.injective (by change a.down * ↑u⁻¹ = 1; rw [← hu]; exact u.mul_inv),
      Equiv.ulift.injective (by change ↑u⁻¹ * a.down = 1; rw [← hu]; exact u.inv_mul)⟩, rfl⟩

instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) where

end ULift

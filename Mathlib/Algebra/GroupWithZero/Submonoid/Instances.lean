/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Instances for the range submonoid of a monoid with zero hom
-/

public section

assert_not_exists Ring

namespace MonoidWithZeroHom

variable {G H : Type*}

instance [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    MulZeroOneClass (MonoidHom.mrange f) where
  zero := ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
lemma val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    ((0 : MonoidHom.mrange f) : H) = 0 :=
  rfl

instance [MulZeroOneClass G] [MonoidWithZero H] (f : G →*₀ H) :
    MonoidWithZero (MonoidHom.mrange f) where

instance [MulZeroOneClass G] [CommMonoidWithZero H] (f : G →*₀ H) :
    CommMonoidWithZero (MonoidHom.mrange f) where

instance [GroupWithZero G] [GroupWithZero H] (f : G →*₀ H) :
    GroupWithZero (MonoidHom.mrange f) where
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [-map_one]⟩, by simp⟩
  isUnit_of_ne_zero {a} ha := by
    obtain ⟨y, hy⟩ := a.prop
    have hy0 : y ≠ 0 := by
      intro h
      apply ha
      apply Subtype.ext
      simpa [h] using hy.symm
    let u := Units.mk0 y hy0
    let v : MonoidHom.mrange f := ⟨f ↑u⁻¹, ↑u⁻¹, rfl⟩
    refine ⟨⟨a, v, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (a : H) * f ↑u⁻¹ = 1
      rw [← hy, ← map_mul]
      change f ((u : G) * ↑u⁻¹) = 1
      rw [u.mul_inv, map_one]
    · apply Subtype.ext
      change f ↑u⁻¹ * (a : H) = 1
      rw [← hy, ← map_mul]
      change f (↑u⁻¹ * (u : G)) = 1
      rw [u.inv_mul, map_one]

instance [GroupWithZero G] [CommGroupWithZero H] (f : G →*₀ H) :
    CommGroupWithZero (MonoidHom.mrange f) where

end MonoidWithZeroHom

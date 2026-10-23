/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

@[expose] public section

assert_not_exists DenselyOrdered MulAction Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

section Monoid

variable [Monoid M] [GroupWithZero G₀]

lemma isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
    (hf : ∃ x : G₀, f x ≠ 1) : IsLocalHom f where
  map_nonunit a h := by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0)), mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact GroupWithZero.isUnit_of_ne_zero h

instance [FunLike F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] [Nontrivial M₀]
    (f : F) : IsLocalHom f :=
  isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

end Monoid

section GroupWithZero

/-- Clear two commuting unit denominators without requiring the numerators to be units. -/
theorem Commute.divp_eq_divp_iff {a c : M₀} {u v : M₀ˣ} (h : Commute u v) :
    a /ₚ u = c /ₚ v ↔ a * v = c * u := by
  rw [divp_eq_iff_mul_eq, ← v.mul_left_inj]
  rw [mul_assoc, show (u : M₀) * v = v * u from congr_arg Units.val h.eq,
    ← mul_assoc, divp_mul_cancel, eq_comm]

section MulZeroOneClass

variable [GroupWithZero G₀] [MulZeroOneClass M₀'] [Nontrivial M₀'] [FunLike F G₀ M₀']
  [MonoidWithZeroHomClass F G₀ M₀']
  (f : F) {a : G₀}

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 := by
  refine ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f, ← Units.mul_inv a, map_mul, H, zero_mul]

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)

end MulZeroOneClass

section MonoidWithZero

variable [MonoidWithZero M₀']

/-- Homomorphisms agreeing on a unit agree on its inverse. -/
theorem eq_on_unit_inv (f g : M₀ →* M₀') (u : M₀ˣ) (h : f u = g u) :
    f ↑u⁻¹ = g ↑u⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f u.inv_mul)
    (h.symm ▸ map_mul_eq_one g u.mul_inv)

/-- A monoid homomorphism preserves mixed division by a unit. -/
@[simp] theorem map_divp (f : M₀ →* M₀') (a : M₀) (u : M₀ˣ) :
    f (a /ₚ u) = f a /ₚ Units.map f u := map_mul f _ _

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀']

/-- Mapping a checked nonzero element agrees with constructing the unit of its image. -/
@[simp] theorem Units.map_mk0 (f : G₀ →*₀ G₀') (a : G₀) (ha : a ≠ 0) :
    Units.map f.toMonoidHom (Units.mk0 a ha) = Units.mk0 (f a) ((map_ne_zero f).2 ha) :=
  Units.ext rfl

/-- A homomorphism preserves inversion on a checked nonzero element. -/
theorem map_mk0_inv (f : G₀ →*₀ G₀') (a : G₀) (ha : a ≠ 0) :
    f (↑(Units.mk0 a ha)⁻¹ : G₀) =
      (↑(Units.mk0 (f a) ((map_ne_zero f).2 ha))⁻¹ : G₀') := by
  rw [← Units.map_mk0 f a ha]
  rfl

end GroupWithZero
end GroupWithZero

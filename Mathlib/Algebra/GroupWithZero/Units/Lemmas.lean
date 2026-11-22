/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

@[expose] public section

assert_not_exists DenselyOrdered MulAction Ring

variable {M N M₀ G₀ M₀' G₀' F F' : Type*}
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

namespace Commute

variable [Monoid M] {a b c d : M}

/-- The version of `div_eq_div_iff_mul_eq_mul` for commuting invertible denominators in a
monoid. -/
protected lemma div_eq_div_iff (hbd : Commute b d) {hb : IsUnit b} {hd : IsUnit d} :
    (a / b) = (c / d) ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, div_mul_cancel₀, ← mul_assoc, hbd.right_comm,
    div_mul_cancel₀]

/-- The version of `mul_inv_eq_mul_inv_iff_mul_eq_mul` for commuting invertible elements of a
monoid. -/
protected lemma mul_inv_eq_mul_inv_iff (hbd : Commute b d) {hb : IsUnit b} {hd : IsUnit d} :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv₀, ← div_eq_mul_inv₀, hbd.div_eq_div_iff]

/-- The version of `inv_mul_eq_inv_mul_iff_mul_eq_mul` for commuting invertible elements of a
monoid. -/
protected lemma inv_mul_eq_inv_mul_iff (hbd : Commute b d) {hb : IsUnit b} {hd : IsUnit d} :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← (hd.mul hb).mul_right_inj, ← mul_assoc, mul_assoc d, mul_inv_cancel₀, mul_one,
    ← mul_assoc, mul_assoc d, hbd.symm.left_comm, mul_inv_cancel₀, mul_one]

end Commute

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

section MonoidHomClass

variable [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N]

/-- Monoid homomorphisms that agree at an invertible element agree at its inverse. -/
theorem eq_on_inv₀ (f g : F) {a : M} {ha : IsUnit a} (h : f a = g a) : f a⁻¹ = g a⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f inv_mul_cancel₀)
    (h.symm ▸ map_mul_eq_one g mul_inv_cancel₀)

end MonoidHomClass

section GroupWithZeroCodomain

variable [Monoid M] [GroupWithZero N] [FunLike F M N] [MonoidHomClass F M N]

/-- A monoid homomorphism into a group with zero sends the inverse of an invertible element `a`
to the inverse of `f a`. The codomain is a group with zero, as upstream, so that `simp` keeps an
inverse inside a homomorphism into a monoid with other units, such as `C a⁻¹` in a polynomial
ring or `algebraMap R A r⁻¹` in an algebra. -/
@[simp]
theorem map_inv₀ (f : F) (a : M) {ha : IsUnit a} : f a⁻¹ = Checked.inv (f a) (ha.map f) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right₀ <| map_mul_eq_one f mul_inv_cancel₀

/-- A monoid homomorphism preserves division by an invertible element. -/
@[simp]
theorem map_div₀ (f : F) (a b : M) {hb : IsUnit b} :
    f (a / b) = Checked.div (f a) (f b) (hb.map f) := by
  rw [div_eq_mul_inv₀, map_mul, map_inv₀, div_eq_mul_inv₀]

/-- A monoid homomorphism `f` maps `x ^ n` to `f x ^ n` for an integer `n`; only a negative
exponent requires `x` to be invertible. -/
@[simp]
theorem map_zpow₀ (f : F) (x : M) (n : ℤ) {h : n < 0 → IsUnit x} :
    f (x ^ n) = Checked.zpow (f x) n (fun hn => (h hn).map f) := by
  cases n with
  | ofNat k => exact map_pow f x k
  | negSucc k =>
    rw [zpow_negSucc₀, zpow_negSucc₀, map_inv₀]
    simp only [map_pow]

end GroupWithZeroCodomain

section MonoidWithZero

variable [MonoidWithZero M₀']

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

end GroupWithZero
end GroupWithZero

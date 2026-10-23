/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.GroupWithZero.Checked
public import Mathlib.Algebra.Group.Units.Hom

/-! # Homomorphisms preserve checked operations and their unit witnesses -/

public section

namespace Checked
variable {M : Type*} [Monoid M]

/-- Homomorphisms transport the supplied unit witness along with checked inversion. -/
theorem map_inv {N : Type*} [Monoid N] (f : M →* N) (a : M) (ha : IsUnit a) :
    f (inv a ha) = inv (f a) (ha.map f) := by
  have hu : (ha.map f).unit = Units.map f ha.unit := Units.ext rfl
  change f (↑ha.unit⁻¹ : M) = (↑(ha.map f).unit⁻¹ : N)
  rw [hu]
  rfl

/-- Homomorphisms preserve mixed division with the mapped denominator witness. -/
theorem map_div {N : Type*} [Monoid N] (f : M →* N) (a b : M) (hb : IsUnit b) :
    f (div a b hb) = div (f a) (f b) (hb.map f) := by
  rw [div_eq_mul_inv, _root_.map_mul, map_inv, div_eq_mul_inv]

/-- Only the negative-exponent branch transports an invertibility obligation. -/
theorem map_zpow {N : Type*} [Monoid N] (f : M →* N) (a : M) (n : ℤ)
    (h : n < 0 → IsUnit a) :
    f (zpow a n h) = zpow (f a) n (fun hn => (h hn).map f) := by
  cases n with
  | ofNat k => exact _root_.map_pow f a k
  | negSucc k => rw [zpow_negSucc, zpow_negSucc, _root_.map_pow, map_inv]

end Checked

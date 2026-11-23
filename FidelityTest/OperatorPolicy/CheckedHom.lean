/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharZero.Defs

/-! Regression tests for exact domain evidence and homomorphism transport. -/

section Hom
variable {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M)
example (ha : IsUnit a) :
    f (Checked.inv a ha) = Checked.inv (f a) (ha.map f) := by
  have hu : (ha.map f).unit = Units.map f ha.unit := Units.ext rfl
  change f (↑ha.unit⁻¹ : M) = (↑(ha.map f).unit⁻¹ : N)
  rw [hu]
  exact (Units.coe_map_inv f ha.unit).symm
example (hb : IsUnit b) :
    f (Checked.div a b hb) = Checked.div (f a) (f b) (hb.map f) := by
  have hu : (hb.map f).unit = Units.map f hb.unit := Units.ext rfl
  change f (a * (↑hb.unit⁻¹ : M)) = f a * (↑(hb.map f).unit⁻¹ : N)
  rw [map_mul, hu, Units.coe_map_inv]
example (n : Int) (h : n < 0 → IsUnit a) :
    f (Checked.zpow a n h) = Checked.zpow (f a) n (fun hn => (h hn).map f) := by
  cases n with
  | ofNat k => exact map_pow f a k
  | negSucc k =>
      have hu : ((h (Int.negSucc_lt_zero k)).map f).unit =
          Units.map f (h (Int.negSucc_lt_zero k)).unit := Units.ext rfl
      change f (↑((h (Int.negSucc_lt_zero k)).unit ^ Int.negSucc k) : M) =
        (↑(((h (Int.negSucc_lt_zero k)).map f).unit ^ Int.negSucc k) : N)
      rw [hu, ← Units.coe_map, map_zpow]
end Hom

section GroupWithZeroHom
variable {M N : Type*} [Monoid M] [GroupWithZero N] (f : M →* N) (a b : M)

example (ha : IsUnit a) :
    f (Checked.inv a ha) = Checked.inv (f a) (ha.map f) := map_inv₀ f a
example (hb : IsUnit b) :
    f (Checked.div a b hb) = Checked.div (f a) (f b) (hb.map f) := map_div₀ f a b
example (n : Int) (h : n < 0 → IsUnit a) :
    f (Checked.zpow a n h) = Checked.zpow (f a) n (fun hn => (h hn).map f) :=
  map_zpow₀ f a n

end GroupWithZeroHom

section Domains
variable {K : Type*} [DivisionRing K] [CharZero K]
example (n : Nat) : IsUnit ((n : K) + 1) := by checked_unit
example (a : K) (ha : a ≠ 0) : IsUnit (-a) := by checked_unit
end Domains

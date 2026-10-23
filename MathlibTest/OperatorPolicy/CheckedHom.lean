/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.GroupWithZero.CheckedHom
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharZero.Defs

/-! Regression tests for exact domain evidence and homomorphism transport. -/

section Hom
variable {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M)
example (ha : IsUnit a) :
    f (Checked.inv a ha) = Checked.inv (f a) (ha.map f) := Checked.map_inv f a ha
example (hb : IsUnit b) :
    f (Checked.div a b hb) = Checked.div (f a) (f b) (hb.map f) := Checked.map_div f a b hb
example (n : Int) (h : n < 0 → IsUnit a) :
    f (Checked.zpow a n h) = Checked.zpow (f a) n (fun hn => (h hn).map f) :=
  Checked.map_zpow f a n h
end Hom

section Domains
variable {K : Type*} [DivisionRing K] [CharZero K]
example (n : Nat) : IsUnit ((n : K) + 1) := by checked_unit
example (a : K) (ha : a ≠ 0) : IsUnit (-a) := by checked_unit
end Domains

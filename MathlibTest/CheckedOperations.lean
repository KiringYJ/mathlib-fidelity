/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Util.CheckedOperations
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Notation.Pi.Defs

section Monoid

variable {M : Type*} [Monoid M] (a b : M) (ha : IsUnit a) (hb : IsUnit b)

example : Checked.inv a * a = 1 := Checked.inv_mul_cancel a ha

example : Checked.div a b * b = a := Checked.div_mul_cancel a b hb

example : Checked.inv (a * b) * (a * b) = 1 :=
  Checked.inv_mul_cancel _ (ha.mul hb)

example : Checked.zpow a (0 : Int) = 1 := Checked.zpow_zero a _

example : Checked.zpow a (3 : Int) = a ^ (3 : Nat) := rfl

end Monoid

section GroupWithZero

variable {K : Type*} [GroupWithZero K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)

example : Checked.inv a * a = 1 :=
  Checked.inv_mul_cancel _ (GroupWithZero.isUnit_of_ne_zero ha)

example : Checked.div a (a * b) * (a * b) = a :=
  Checked.div_mul_cancel _ _ (GroupWithZero.isUnit_of_ne_zero (mul_ne_zero ha hb))

example (h₁ h₂ : IsUnit a) : Checked.inv a h₁ = Checked.inv a h₂ := rfl

example : a⁻¹ * a = 1 :=
  Checked.inv_mul_cancel _ (GroupWithZero.isUnit_of_ne_zero ha)

example : (a / b) * b = a :=
  Checked.div_mul_cancel _ _ (GroupWithZero.isUnit_of_ne_zero hb)

example : a ^ (-1 : Int) = Checked.zpow a (-1) := rfl

end GroupWithZero

section Group

variable {G : Type*} [Group G] (a b : G)

example : a / b = a * b⁻¹ := div_eq_mul_inv a b

example : a ^ (-1 : Int) = a⁻¹ := zpow_neg_one a

end Group

section UnitsCoercion

variable {K : Type*} [Monoid K] (u v : Kˣ)

example : (↑(u⁻¹) : K) = Units.val (Inv.inv u) := rfl

example : (↑(u / v) : K) = Units.val (Div.div u v) := rfl

example : (↑(u ^ (-1 : Int)) : K) = Units.val (HPow.hPow u (-1 : Int)) := rfl

end UnitsCoercion

section NumeralDenominators

variable {K : Type*} [DivisionSemiring K] [NeZero (2 : K)] (a : K)

example : (a / 2) * 2 = a :=
  Checked.div_mul_cancel _ _ (GroupWithZero.isUnit_of_ne_zero (NeZero.ne (2 : K)))

example : a ^ (2 : Nat) = a * a := pow_two a

example : (((3 : Nat) / 2 : K)) = Checked.div (3 : K) (2 : K) := rfl

end NumeralDenominators

namespace FunctionCoercion

structure Box (M : Type*) where
  val : Nat → M

instance {M : Type*} : CoeFun (Box M) (fun _ => Nat → M) := ⟨Box.val⟩

instance {M : Type*} [Monoid M] : Pow (Box M) Nat :=
  ⟨fun f n => ⟨fun i => (f i) ^ n⟩⟩

example {M : Type*} [Monoid M] (f : Box M) (n : Nat) :
    ⇑(f ^ n) = (f : Nat → M) ^ n := rfl

end FunctionCoercion

namespace DelayedInference

def inverse {G : Type*} [Group G] := fun x => (x⁻¹, (x : G))

def division {G : Type*} [Group G] := fun x y => (x / y, (x : G), (y : G))

def power {G : Type*} [Group G] := fun x => (x ^ (-1 : Int), (x : G))

example {G : Type*} [Group G] (x : G) : (inverse x).1 = Inv.inv x := rfl

example {G : Type*} [Group G] (x y : G) : (division x y).1 = HDiv.hDiv x y := rfl

example {G : Type*} [Group G] (x : G) : (power x).1 = HPow.hPow x (-1 : Int) := rfl

end DelayedInference

section AmbientOperations

variable {K : Type*} [GroupWithZero K]

local instance : Inv K := ⟨fun _ => 0⟩

local instance : Div K := ⟨fun _ _ => 0⟩

local instance : Pow K Int := ⟨fun _ _ => 0⟩

example (a : K) (ha : a ≠ 0) : a⁻¹ * a = 1 :=
  Checked.inv_mul_cancel _ (GroupWithZero.isUnit_of_ne_zero ha)

example (a b : K) (hb : b ≠ 0) : (a / b) * b = a :=
  Checked.div_mul_cancel _ _ (GroupWithZero.isUnit_of_ne_zero hb)

example (a : K) : a ^ (0 : Int) = 1 := Checked.zpow_zero a _

example (a : K) : a ^ (2 : Nat) = a * a := pow_two a

end AmbientOperations

namespace CarriedUnitData

variable {M : Type*} [Monoid M]

def inverseValue (u v : Mˣ) : M := (u * v)⁻¹

def quotientValue (a : M) (u v : Mˣ) : M := a / (u * v)

def powerValue (u v : Mˣ) (n : Int) : M := (u * v) ^ n

example (u v : Mˣ) : inverseValue u v = Units.val (Inv.inv (u * v)) := rfl

example (a : M) (u v : Mˣ) : quotientValue a u v = a /ₚ (u * v) := rfl

example (u v : Mˣ) (n : Int) : powerValue u v n = Units.val (HPow.hPow (u * v) n) := rfl

def inverseCoercedProduct (u v : Mˣ) : M := ((u : M) * (v : M))⁻¹

def quotientCoercedPower (a : M) (u : Mˣ) (n : Nat) : M := a / ((u : M) ^ n)

example (u v : Mˣ) : inverseCoercedProduct u v = Units.val (Inv.inv (u * v)) := rfl

example (a : M) (u : Mˣ) (n : Nat) : quotientCoercedPower a u n = a /ₚ (u ^ n) := rfl

example {K : Type*} [GroupWithZero K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (↑((Units.mk0 a ha * Units.mk0 b hb)⁻¹) : K) =
      Units.val (Inv.inv (Units.mk0 a ha * Units.mk0 b hb)) := rfl

end CarriedUnitData

namespace NamedFieldCarrier

-- A named carrier can have instances even when its opaque representation has none.
private axiom Base : Type

def Carrier : Type := Base

private axiom fieldCarrier : Field Carrier
attribute [instance] fieldCarrier

private axiom charZeroCarrier : CharZero Carrier
attribute [instance] charZeroCarrier

example (a b : Carrier) (hb : b ≠ 0) : a / b = Checked.div a b := rfl

example (a : Carrier) (ha : a ≠ 0) : a⁻¹ = Checked.inv a := rfl

example (a : Carrier) (ha : a ≠ 0) (n : Int) : a ^ n = Checked.zpow a n := rfl

example (a b d : Carrier) : a / 5 + d * (b / 4) =
    Checked.div a 5 + d * Checked.div b 4 := rfl

end NamedFieldCarrier

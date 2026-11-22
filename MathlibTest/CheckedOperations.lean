/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.GroupWithZero.Inverse
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Notation.Pi.Defs

section Monoid

variable {M : Type*} [Monoid M] (a b : M) (ha : IsUnit a) (hb : IsUnit b)

example : Checked.inv a * a = 1 := inv_mul_cancel₀

example : Checked.div a b * b = a := div_mul_cancel₀ a

example : Checked.inv (a * b) * (a * b) = 1 :=
  inv_mul_cancel₀ (ha := ha.mul hb)

example : Checked.zpow a (0 : Int) = 1 := zpow_zero₀ a

example : Checked.zpow a (3 : Int) = a ^ (3 : Nat) := rfl

end Monoid

section GroupWithZero

variable {K : Type*} [GroupWithZero K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)

example : Checked.inv a * a = 1 := inv_mul_cancel₀

example : Checked.div a (a * b) * (a * b) = a := div_mul_cancel₀ a

example (h₁ h₂ : IsUnit a) : Checked.inv a h₁ = Checked.inv a h₂ := rfl

example : a⁻¹ * a = 1 := inv_mul_cancel₀

example : Checked.div a b * b = a := div_mul_cancel₀ a

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

variable {K : Type*} [Field K] [NeZero (2 : K)] (a : K)

example : (a / 2) * 2 = a := div_mul_cancel₀ a

example : a ^ (2 : Nat) = a * a := pow_two a

example : ((3 : K) / (2 : K)) = Checked.div (3 : K) (2 : K) := rfl

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

variable {K : Type*} [Field K]

local instance : Inv K := ⟨fun _ => 0⟩

local instance : Div K := ⟨fun _ _ => 0⟩

local instance : Pow K Int := ⟨fun _ _ => 0⟩

example (a : K) (ha : a ≠ 0) : a⁻¹ * a = 1 := inv_mul_cancel₀

example (a b : K) (hb : b ≠ 0) : (a / b) * b = a := div_mul_cancel₀ a

example (a : K) : a ^ (0 : Int) = 1 := zpow_zero₀ a

example (a : K) : a ^ (2 : Nat) = a * a := pow_two a

end AmbientOperations

section GenericEuclideanDivision

variable {R : Type*} [EuclideanDomain R]

example (a : R) (u : Rˣ) : a / (u : R) = Checked.div a (u : R) := rfl

example (a b : R) (hb : b ≠ 0) : b * EuclideanDomain.quotient a b hb + a % b = a :=
  EuclideanDomain.div_add_mod a b hb

example [DecidableEq R] : EuclideanDomain.lcm (0 : R) 0 = 0 :=
  zero_dvd_iff.mp (EuclideanDomain.dvd_lcm_left 0 0)

/--
error: failed to synthesize
  Div R

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div R

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: a nonzero denominator proof is required
R : Type u_1
inst✝ : EuclideanDomain R
a : R
⊢ 0 ≠ 0
-/
#guard_msgs in
example (a : R) : R := EuclideanDomain.quotient a 0

local instance : Div R := ⟨fun _ _ => 0⟩

example (a b : R) (hb : IsUnit b) : a / b = Checked.div a b hb := rfl

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
R : Type u_1
inst✝ : EuclideanDomain R
a : R
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example (a : R) : R := a / 0

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
R : Type u_1
inst✝ : EuclideanDomain R
a : R
⊢ IsUnit (0 ^ 2)
-/
#guard_msgs in
noncomputable example (a : R) : R := a ^ 2 / (0 : R) ^ 2

end GenericEuclideanDivision

example : EuclideanDomain.quotient (7 : ℤ) 2 (by decide) = 3 := by
  change Int.euclideanDiv (7 : ℤ) 2 (by decide) = 3
  exact Int.euclideanDiv_eq_of_remainder (r := 1) (by decide) (by decide) (by decide) (by decide)

section NamedEuclideanCarrier

private def EuclideanInt := ℤ

private instance : EuclideanDomain EuclideanInt := Int.euclideanDomain

local instance : Div EuclideanInt := ⟨fun _ _ => 0⟩

example (a b : EuclideanInt) (hb : IsUnit b) : a / b = Checked.div a b hb := rfl

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
a : EuclideanInt
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example (a : EuclideanInt) : EuclideanInt := a / 0

end NamedEuclideanCarrier

section EuclideanDivision

variable {K : Type*} [Field K]

/--
error: failed to synthesize
  EuclideanDomain K

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth EuclideanDomain K

attribute [local instance] Field.toEuclideanDomain

example (a : K) : EuclideanDomain.remainder a 0 = a :=
  EuclideanDomain.mod_zero a

example (a b : K) (hb : b ≠ 0) : EuclideanDomain.quotient a b hb = Checked.div a b hb.isUnit :=
  Field.quotient_eq_div a hb

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
K : Type u_1
inst✝ : Field K
a : K
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example (a : K) : K := a / 0

end EuclideanDivision

namespace CarriedUnitData

variable {M : Type*} [Monoid M]

def inverseValue (u v : Mˣ) : M := (u * v)⁻¹

def quotientValue (a : M) (u v : Mˣ) : M := a /ₚ (u * v)

def powerValue (u v : Mˣ) (n : Int) : M := (u * v) ^ n

example (u v : Mˣ) : inverseValue u v = Units.val (Inv.inv (u * v)) := rfl

example (a : M) (u v : Mˣ) : quotientValue a u v = a /ₚ (u * v) := rfl

example (u v : Mˣ) (n : Int) : powerValue u v n = Units.val (HPow.hPow (u * v) n) := rfl

def inverseCoercedProduct (u v : Mˣ) : M := ((u : M) * (v : M))⁻¹

def quotientCoercedPower (a : M) (u : Mˣ) (n : Nat) : M := a /ₚ (u ^ n)

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

section CanonicalFamily

variable {K : Type*} [Field K] (a b c x : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)

/-- info: a / b * b = a : Prop -/
#guard_msgs in
#check (a / b * b = a : Prop)

/-- info: a ^ 2 / b ^ 2 = (a / b) ^ 2 : Prop -/
#guard_msgs in
#check (a ^ 2 / b ^ 2 = (a / b) ^ 2 : Prop)

-- The evidence of the left-hand side is unified from the term: no side goals.
example : x * (a / b * b) = x * a := by rw [div_mul_cancel₀]
example : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [mul_inv₀]
example : (a / b)⁻¹ = b / a := by rw [inv_div₀]
example : a / (b / c) = a * c / b := by rw [div_div_eq_mul_div₀]
example : a / (b * c) = a / b / c := by rw [div_mul_eq_div_div₀]
example : a ^ (-1 : ℤ) = a⁻¹ := by rw [zpow_neg_one₀]
example : (a / b) ^ 2 = a ^ 2 / b ^ 2 := by rw [div_pow₀]
example : a⁻¹⁻¹ = a := by simp

end CanonicalFamily

section NoncommutativeGroupWithZero

variable {G : Type*} [GroupWithZero G] (a b : G) (ha : a ≠ 0) (hb : b ≠ 0)

-- Groups with zero are Dedekind-finite, so a product's evidence gives its factors' evidence.
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev₀]
example : Checked.div b (a * b) = a⁻¹ := by rw [div_mul_cancel_right₀]

end NoncommutativeGroupWithZero

section MonoidEvidence

variable {M : Type*} [Monoid M] (a b : M) (ha : IsUnit a) (hb : IsUnit b)

example : a * a⁻¹ * b = b := by rw [mul_inv_cancel₀, one_mul]
example : IsUnit (a⁻¹ * b) := by checked_unit
example : IsUnit (Checked.div a b) := by checked_unit

end MonoidEvidence

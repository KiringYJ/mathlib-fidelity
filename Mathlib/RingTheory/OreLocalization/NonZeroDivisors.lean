/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Ore Localization over nonZeroDivisors in monoids with zeros.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

theorem nontrivial_of_nonZeroDivisorsLeft [Nontrivial R] (hS : S ≤ nonZeroDivisorsLeft R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (zero_mul _))

theorem nontrivial_of_nonZeroDivisorsRight [Nontrivial R] (hS : S ≤ nonZeroDivisorsRight R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (mul_zero _))

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

variable [Nontrivial R] [OreSet R⁰]

instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

/-- An Ore fraction with nonzero numerator is a unit. Its reciprocal is the fraction
with numerator and denominator interchanged. -/
def oreDivUnit (r : R) (s : R⁰) (hr : r ≠ 0) : (R[R⁰⁻¹])ˣ where
  val := r /ₒ s
  inv := (s : R) /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩
  val_inv := OreLocalization.mul_inv ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ s
  inv_val := OreLocalization.mul_inv s ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩

omit [Nontrivial R] in
@[simp] theorem val_oreDivUnit (r : R) (s : R⁰) (hr : r ≠ 0) :
    (oreDivUnit r s hr : R[R⁰⁻¹]) = r /ₒ s := rfl

omit [Nontrivial R] in
@[simp] theorem inv_oreDivUnit (r : R) (s : R⁰) (hr : r ≠ 0) :
    (↑(oreDivUnit r s hr)⁻¹ : R[R⁰⁻¹]) =
      (s : R) /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ := rfl

instance : GroupWithZero R[R⁰⁻¹] where
  isUnit_of_ne_zero {x} hx := by
    induction x with | _ r s
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hx
    exact ⟨oreDivUnit r s hr, rfl⟩

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [OreSet R⁰] [NoZeroDivisors R]

instance : CommGroupWithZero R[R⁰⁻¹] where

end CommMonoidWithZero

end OreLocalization

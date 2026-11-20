/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Conjugating by the square root of a positive element in a C⋆-algebra

This file defines `conjSqrt c a` as `sqrt c * a * sqrt c`, and develops API for this operation.

## Main declarations

* `conjSqrt c`: the map `fun a => sqrt c * a * sqrt c`, bundled as a continuous linear map,
-/

namespace CFC

open Ring

public section ConjSqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [SeparatelyContinuousMul A]

/-- Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`. -/
@[expose]
noncomputable def conjSqrt (c : A) : A →L[ℝ] A where
  toLinearMap := .mulLeftRight ℝ (sqrt c, sqrt c)

@[simp] lemma toLinearMap_conjSqrt (c : A) :
    (conjSqrt c).toLinearMap = .mulLeftRight ℝ (sqrt c, sqrt c) := rfl

lemma conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c := rfl

lemma conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 ≤ c) : conjSqrt c a = 0 := by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

lemma conjSqrt_monotone {c : A} : Monotone (conjSqrt c) := by
  intro a b hab
  by_cases hc : 0 ≤ c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

@[gcongr]
lemma conjSqrt_le_conjSqrt {c a b : A} (h : a ≤ b) : conjSqrt c a ≤ conjSqrt c b :=
  conjSqrt_monotone h

variable [IsSemitopologicalRing A] [T2Space A]

set_option linter.overlappingInstances false

@[grind =]
lemma isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    IsStrictlyPositive (conjSqrt c a) ↔ IsStrictlyPositive a := by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  exact (hc.isUnit_cfcSqrt c).isStrictlyPositive_iff_conjugate_of_isSelfAdjoint a (sqrt c) hc'

@[grind _=_]
lemma inv_conjSqrt (c a : A) {ha : IsUnit a} (hc : IsStrictlyPositive c := by cfc_tac) :
    Checked.inv (conjSqrt c a)
      (((hc.isUnit_cfcSqrt c).mul ha).mul (hc.isUnit_cfcSqrt c)) =
      conjSqrt (Checked.inv c hc.isUnit) (Checked.inv a ha) := by
  let s := (hc.isUnit_cfcSqrt c).unit
  let u := ha.unit
  have h : (s * u * s)⁻¹ = s⁻¹ * u⁻¹ * s⁻¹ := by
    simp [mul_inv_rev, mul_assoc]
  simpa only [conjSqrt_apply, sqrt_inv hc, Units.val_mul, Units.val_inv_eq_inv_val₀,
    s, u, IsUnit.unit_spec] using congrArg ((↑) : Aˣ → A) h

@[grind =]
lemma conjSqrt_inv_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt (Checked.inv c hc.isUnit) (conjSqrt c a) = a := by
  simp only [conjSqrt_apply, sqrt_inv hc, mul_assoc, inv_mul_cancel_left₀, mul_inv_cancel₀,
    mul_one]

@[grind =]
lemma conjSqrt_conjSqrt_inv (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c (conjSqrt (Checked.inv c hc.isUnit) a) = a := by
  simp only [conjSqrt_apply, sqrt_inv hc, mul_assoc, mul_inv_cancel_left₀, inv_mul_cancel₀,
    mul_one]
@[grind =]
lemma conjSqrt_one (c : A) (hc : 0 ≤ c := by cfc_tac) : conjSqrt c 1 = c := by
  rw [conjSqrt_apply, mul_one, sqrt_mul_sqrt_self _]

@[grind =]
lemma conjSqrt_inv_self (c : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt (Checked.inv c hc.isUnit) c = 1 := by
  calc
    _ = conjSqrt (Checked.inv c hc.isUnit) (conjSqrt c 1) :=
      congrArg (conjSqrt (Checked.inv c hc.isUnit)) (conjSqrt_one c hc.nonneg).symm
    _ = 1 := conjSqrt_inv_conjSqrt c 1 hc
end ConjSqrt

end CFC

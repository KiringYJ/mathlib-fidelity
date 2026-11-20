/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of `x ^ m`, `m : ℤ` within an open set

In this file we prove theorems about iterated derivatives of `x ^ m`, `m : ℤ` within an open set.

## Keywords

iterated, derivative, power, open set
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {s : Set 𝕜}

/-- Integer powers on an open set have the indicated unique derivative on their actual domain. -/
theorem hasIteratedDerivWithinAt_zpow_iff (m : ℤ) (k : ℕ) (hs : IsOpen s)
    (x : {y : 𝕜 // y ∈ s ∧ (m < 0 → IsUnit y)}) (d : 𝕜) :
    HasIteratedDerivAt k
      (fun y : {y : 𝕜 // y ∈ s ∧ (m < 0 → IsUnit y)} ↦ Checked.zpow y.val m y.property.2)
      d x Subtype.val ↔
      d = if hpol : 0 ≤ m ∧ m < (k : ℤ) then 0 else
        (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) *
          Checked.zpow x.val (m - k) (fun h ↦ x.property.2 (by omega)) := by
  let q : {y : 𝕜 // y ∈ s ∧ (m < 0 → IsUnit y)} → {y : 𝕜 // m < 0 → IsUnit y} :=
    fun y ↦ ⟨y.val, y.property.2⟩
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  have hp := (hasIteratedDerivAt_zpow m (q x) k).comp_domain (g := q) hq
  have hopen : IsOpen {y : 𝕜 | y ∈ s ∧ (m < 0 → IsUnit y)} :=
    hs.inter (isOpen_zpow_domain m)
  exact ⟨fun h ↦ h.unique hp hopen.isOpenEmbedding_subtypeVal, fun h ↦ h.symm ▸ hp⟩

/-- The reciprocal on the unit locus of an open set has the indicated unique derivative. -/
theorem hasIteratedDerivWithinAt_one_div_iff (k : ℕ) (hs : IsOpen s)
    (x : {y : 𝕜 // y ∈ s ∧ IsUnit y}) (d : 𝕜) :
    HasIteratedDerivAt k
      (fun y : {y : 𝕜 // y ∈ s ∧ IsUnit y} ↦ Checked.div 1 y.val y.property.2)
      d x Subtype.val ↔
      d = (-1) ^ k * k ! * Checked.zpow x.val (-1 - (k : ℤ)) (fun _ ↦ x.property.2) := by
  let q : {y : 𝕜 // y ∈ s ∧ IsUnit y} → 𝕜ˣ := fun y ↦ y.property.2.unit
  have hcoord : Units.val ∘ q = Subtype.val := funext fun y ↦ y.property.2.unit_spec
  have hq : Continuous q := Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
    (hcoord.symm ▸ continuous_subtype_val)
  have hp := (hasIteratedDerivAt_inv k (q x)).comp_domain (g := q) hq
  have hfun : ((fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) ∘ q) =
      (fun y ↦ Checked.div 1 y.val y.property.2) :=
    funext fun y ↦ (one_div₀ (ha := y.property.2)).symm
  have hpow : Checked.zpow x.val (-1 - (k : ℤ)) (fun _ ↦ x.property.2) =
      (↑(q x ^ (-1 - (k : ℤ))) : 𝕜) := x.property.2.zpow_eq_val_unit_zpow _
  rw [hfun, ← hpow, hcoord] at hp
  have hopen : IsOpen {y : 𝕜 | y ∈ s ∧ IsUnit y} := hs.inter Units.isOpen
  exact ⟨fun h ↦ h.unique hp hopen.isOpenEmbedding_subtypeVal, fun h ↦ h.symm ▸ hp⟩

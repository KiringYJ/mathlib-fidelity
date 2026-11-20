/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Basic

/-! Integer-power derivatives on their actual exponent-dependent domains. -/

noncomputable section

-- The chain rule pulls back both the power domain and the source coordinates.
example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f : D → ℂ) (d : ℂ) (x : D)
    (hf : HasDerivAt f d x coord) (hc : ContinuousAt coord x) (m : ℤ)
    (hx : m < 0 → IsUnit (f x)) :
    HasDerivAt (fun y : {y : D // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      ((if hm : m = 0 then 0 else (m : ℂ) * Checked.zpow (f x) (m - 1)
        (fun h ↦ hx (by omega))) * d) ⟨x, hx⟩ (coord ∘ Subtype.val) :=
  hf.zpow m hx hc

-- The constant exponent has derivative zero at the origin, without forming its negative power.
example : HasDerivAt
    (fun y : {y : ℝ // (0 : ℤ) < 0 → IsUnit y} ↦ Checked.zpow y.val 0 y.property)
    0 ⟨0, by intro h; omega⟩ Subtype.val := by
  have h := hasDerivAt_zpow 0 (⟨0, by intro h; omega⟩ : {y : ℝ // (0 : ℤ) < 0 → IsUnit y})
  rw [dite_eq_left rfl] at h
  exact h

-- Polynomial exhaustion is handled before a negative power could be evaluated at zero.
example : HasIteratedDerivAt 4
    (fun y : {y : ℝ // (3 : ℤ) < 0 → IsUnit y} ↦ Checked.zpow y.val 3 y.property)
    0 ⟨0, by intro h; omega⟩ Subtype.val := by
  simpa using hasIteratedDerivAt_zpow 3
    (⟨0, by intro h; omega⟩ : {y : ℝ // (3 : ℤ) < 0 → IsUnit y}) 4

example : HasIteratedDerivAt 4 (fun y : ℝ ↦ y ^ 3) 0 0 := by
  simpa only [Finset.prod_range_succ, Nat.cast_ofNat, sub_self, mul_zero, zero_mul] using
    hasIteratedDerivAt_pow 3 (0 : ℝ) 4

-- Negative powers retain their higher derivatives on the unit carrier.
example : HasIteratedDerivAt 3 (fun y : ℝˣ ↦ (↑y⁻¹ : ℝ)) (-6) 1 Units.val := by
  convert hasIteratedDerivAt_inv 3 (1 : ℝˣ) using 1
  norm_num [Nat.factorial]

-- A zero slope is allowed when the affine denominator is invertible.
example : HasIteratedDerivAt 2
    (fun y : {y : ℝ // IsUnit ((0 : ℝ) * y + 1)} ↦
      Checked.inv ((0 : ℝ) * y.val + 1) y.property)
    0 ⟨0, by simp⟩ Subtype.val := by
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using
    hasIteratedDerivAt_inv_linear 2 (0 : ℝ) 1 ⟨0, by simp⟩

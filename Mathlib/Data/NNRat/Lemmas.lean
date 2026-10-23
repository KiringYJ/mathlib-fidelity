/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Zify

/-!
# Field and action structures on the nonnegative rationals

This file provides additional results about `NNRat` that cannot live in earlier files due to import
cycles.
-/

@[expose] public section

open scoped NNRat

namespace NNRat
variable {α : Type*}

@[simp, norm_cast]
lemma coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x ↦ ↑(f x)) a :=
  map_indicator coeHom _ _ _

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

/-- A positive rational has a reciprocal in the nonnegative rational unit group. -/
lemma toNNRat_reciprocal (q : ℚ) (hq : 0 < q) :
    toNNRat (reciprocal q hq.ne') =
      ↑((NNRat.unit (toNNRat q) (by
        intro h
        have hc := congrArg (fun x : ℚ≥0 => (x : ℚ)) h
        exact hq.ne' (by simpa only [Rat.coe_toNNRat q hq.le, NNRat.coe_zero] using hc)))⁻¹) := by
  apply NNRat.ext
  rw [Rat.coe_toNNRat _ (Rat.reciprocal_nonneg hq.le hq.ne')]
  have hn : ((toNNRat q : ℚ≥0) : ℚ) ≠ 0 := by
    rw [Rat.coe_toNNRat q hq.le]
    exact hq.ne'
  change reciprocal q hq.ne' = reciprocal ((toNNRat q : ℚ≥0) : ℚ) hn
  simp only [Rat.coe_toNNRat q hq.le]

/-- Truncation preserves division when the numerator is nonnegative and the unit denominator
is positive, so its nonnegative counterpart is also invertible. -/
lemma toNNRat_divp (hp : 0 ≤ p) (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    toNNRat (p /ₚ u) = toNNRat p /ₚ
      NNRat.unit ⟨u, hu.le⟩ (fun h => u.ne_zero (congrArg Subtype.val h)) := by
  let v := NNRat.unit ⟨u, hu.le⟩ (fun h => u.ne_zero (congrArg Subtype.val h))
  have hv : Units.map NNRat.coeHom.toMonoidHom v = u := Units.ext rfl
  apply NNRat.ext
  rw [Rat.coe_toNNRat _ (divp_nonneg hp hu.le)]
  change p /ₚ u = NNRat.coeHom.toMonoidHom (toNNRat p /ₚ v)
  rw [map_divp, hv]
  change p /ₚ u = ((toNNRat p : ℚ≥0) : ℚ) /ₚ u
  rw [Rat.coe_toNNRat p hp]

end Rat

/-! ### Numerator and denominator -/

namespace NNRat

variable {q : ℚ≥0}

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*}
    (h : ∀ (m n : ℕ) (hn : n ≠ 0), α (divNat m n hn)) (q : ℚ≥0) : α q := by
  rw [← num_divNat_den q]
  apply h

theorem mul_num (q₁ q₂ : ℚ≥0) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  zify
  convert! Rat.mul_num q₁ q₂ <;> norm_cast

theorem mul_den (q₁ q₂ : ℚ≥0) :
    (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  convert! Rat.mul_den q₁ q₂
  norm_cast

/-- A version of `NNRat.mul_den` without division. -/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : ℚ≥0) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  convert! Rat.den_mul_den_eq_den_mul_gcd q₁ q₂
  norm_cast

/-- A version of `NNRat.mul_num` without division. -/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : ℚ≥0) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  zify
  convert! Rat.num_mul_num_eq_num_mul_gcd q₁ q₂ <;> norm_cast

end NNRat

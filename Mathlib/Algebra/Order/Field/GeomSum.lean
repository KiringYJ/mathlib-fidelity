/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Partial sums of geometric series in an ordered field

This file upper- and lower-bounds the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.
-/

public section

variable {K : Type*}

open Finset

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

lemma geom₂_sum_of_gt (h : y < x) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) =
      (x ^ n - y ^ n) /ₚ Units.mk0 (x - y) (tsub_pos_of_lt h).ne' :=
  eq_divp_iff_mul_eq.mpr (geom_sum₂_mul_of_ge h.le n)

lemma geom₂_sum_of_lt (h : x < y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) =
      (y ^ n - x ^ n) /ₚ Units.mk0 (y - x) (tsub_pos_of_lt h).ne' :=
  eq_divp_iff_mul_eq.mpr (geom_sum₂_mul_of_le h.le n)

lemma geom_sum_of_one_lt (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) /ₚ Units.mk0 (x - 1) (tsub_pos_of_lt h).ne' :=
  eq_divp_iff_mul_eq.mpr (geom_sum_mul_of_one_le h.le n)

lemma geom_sum_of_lt_one (h : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (1 - x ^ n) /ₚ Units.mk0 (1 - x) (tsub_pos_of_lt h).ne' :=
  eq_divp_iff_mul_eq.mpr (geom_sum_mul_of_le_one h.le n)

lemma geom_sum_lt (h0 : x ≠ 0) (h1 : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i < (↑(Units.mk0 (1 - x) (tsub_pos_of_lt h1).ne')⁻¹ : K) := by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1, divp_lt_iff (tsub_pos_of_lt h1), Units.inv_mul]
  exact tsub_lt_self_iff.mpr ⟨h0.trans h1, pow_pos h0 n⟩

end Semifield

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x : K} {m n : ℕ}

lemma geom_sum_Ico_le_of_lt_one (hx : 0 ≤ x) (h'x : x < 1) :
    ∑ i ∈ Ico m n, x ^ i ≤ x ^ m /ₚ Units.mk0 (1 - x) (sub_pos.2 h'x).ne' := by
  rcases le_or_gt m n with (hmn | hmn)
  · calc
      _ = (x ^ m - x ^ n) /ₚ Units.mk0 (1 - x) (sub_pos.2 h'x).ne' :=
        geom_sum_Ico' h'x.ne hmn
      _ ≤ _ := divp_le_divp_of_nonneg_right (sub_le_self _ (pow_nonneg hx _)) (sub_pos.2 h'x).le
  · rw [Ico_eq_empty (by omega), sum_empty]
    exact divp_nonneg (pow_nonneg hx _) (sub_pos.2 h'x).le

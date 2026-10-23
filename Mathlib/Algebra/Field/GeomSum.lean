/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Partial sums of geometric series in a field

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^iy^{n - 1 - i}=\frac{x^n-y^{n-m}x^m}{x-y}$
  in a field.

Several variants are recorded, generalising in particular to the case of a division ring in
which `x` and `y` commute.
-/

public section

assert_not_exists IsOrderedRing

variable {K : Type*}

open Finset

section DivisionRing
variable [DivisionRing K] {x y : K}

protected theorem Commute.geom_sum₂ (h' : Commute x y) (h : x ≠ y)
    (n : ℕ) : ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) =
      (x ^ n - y ^ n) /ₚ Units.mk0 (x - y) (sub_ne_zero.mpr h) := by
  apply eq_divp_iff_mul_eq.mpr
  exact h'.geom_sum₂_mul n

theorem geom_sum_eq (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) /ₚ Units.mk0 (x - 1) (sub_ne_zero.mpr h) := by
  apply eq_divp_iff_mul_eq.mpr
  exact geom_sum_mul x n

protected theorem Commute.geom_sum₂_Ico (h : Commute x y) (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i) =
      (x ^ n - y ^ (n - m) * x ^ m) /ₚ Units.mk0 (x - y) (sub_ne_zero.mpr hxy) := by
  apply eq_divp_iff_mul_eq.mpr
  exact h.geom_sum₂_Ico_mul hmn

lemma geom_sum_Ico (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i =
      (x ^ n - x ^ m) /ₚ Units.mk0 (x - 1) (sub_ne_zero.mpr hx) := by
  apply eq_divp_iff_mul_eq.mpr
  exact geom_sum_Ico_mul x hmn

lemma geom_sum_Ico' (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i =
      (x ^ m - x ^ n) /ₚ Units.mk0 (1 - x) (sub_ne_zero.mpr hx.symm) := by
  apply eq_divp_iff_mul_eq.mpr
  exact geom_sum_Ico_mul_neg x hmn

lemma geom_sum_inv (u : Kˣ) (hu : (u : K) ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, (↑u⁻¹ : K) ^ i =
      ((u : K) - (↑u⁻¹ : K) ^ n * u) /ₚ Units.mk0 ((u : K) - 1) (sub_ne_zero.mpr hu) := by
  apply eq_divp_iff_mul_eq.mpr
  have h := congrArg (fun z : K => z * u) (geom_sum_mul_neg (↑u⁻¹ : K) n)
  simpa only [Units.val_mk0, mul_assoc, sub_mul, one_mul, Units.inv_mul] using h

end DivisionRing

section Field
variable [Field K] {x y : K}

lemma geom₂_sum (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) =
      (x ^ n - y ^ n) /ₚ Units.mk0 (x - y) (sub_ne_zero.mpr h) :=
  (Commute.all x y).geom_sum₂ h n

lemma geom_sum₂_Ico (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) =
      (x ^ n - y ^ (n - m) * x ^ m) /ₚ Units.mk0 (x - y) (sub_ne_zero.mpr hxy) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

end Field

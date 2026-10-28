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
    (n : ℕ) : ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  rw [← h'.geom_sum₂_mul, mul_div_cancel_right₀]

theorem geom_sum_eq (h : x ≠ 1) (n : ℕ) : ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  rw [← geom_sum_mul, mul_div_cancel_right₀]

protected theorem Commute.geom_sum₂_Ico (h : Commute x y) (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel_right₀]

lemma geom_sum_Ico (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

lemma geom_sum_Ico' (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  rw [← geom_sum_Ico_mul_neg x hmn, mul_div_cancel_right₀]

lemma geom_sum_inv {hx0 : IsUnit x} (hx1 : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have hcomm : x * x⁻¹ ^ n = x⁻¹ ^ n * x :=
    (((Commute.refl x).inv_right₀ : Commute x x⁻¹).pow_right n).eq
  rw [eq_inv_mul_iff_mul_eq₀]
  calc (x - 1) * ∑ i ∈ range n, x⁻¹ ^ i = x * (1 - x⁻¹) * ∑ i ∈ range n, x⁻¹ ^ i := by
        rw [mul_sub, mul_one, mul_inv_cancel₀]
    _ = x * (1 - x⁻¹ ^ n) := by rw [mul_assoc, mul_neg_geom_sum]
    _ = x - x⁻¹ ^ n * x := by rw [mul_sub, mul_one, hcomm]

end DivisionRing

section Field
variable [Field K] {x y : K}

lemma geom₂_sum (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

lemma geom_sum₂_Ico (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

end Field

/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic functions

This file proves facts about periodic and antiperiodic functions from and to a field.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

public section

assert_not_exists TwoSidedIdeal

variable {α β γ : Type*} {f : α → β} {c x : α}

open Set

namespace Function

/-! ### Periodicity -/

protected theorem Periodic.const_smul₀ [AddMonoid α] [Monoid γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) {ha : IsUnit a} : Periodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀] using h (a • x)

protected theorem Periodic.const_mul [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a

theorem Periodic.const_inv_smul₀ [AddMonoid α] [Monoid γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) {ha : IsUnit a} : Periodic (fun x => f (a⁻¹ • x)) (a • c) :=
  fun x => by simpa only [smul_add, inv_smul_smul₀] using h (a⁻¹ • x)

theorem Periodic.const_inv_mul [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a

theorem Periodic.mul_const [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  fun x => by simpa only [add_mul, inv_mul_cancel_right₀] using h (x * a)

theorem Periodic.mul_const' [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (x * a)) (c / a) :=
  fun x => by simpa only [add_mul, div_mul_cancel₀] using h (x * a)

theorem Periodic.mul_const_inv [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  fun x => by simpa only [add_mul, mul_inv_cancel_right₀] using h (x * a⁻¹)

theorem Periodic.div_const [Semiring α] (h : Periodic f c) (a : α) {ha : IsUnit a} :
    Periodic (fun x => f (x / a)) (c * a) :=
  fun x => by simpa only [add_div, mul_div_cancel_right₀] using h (x / a)

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico₀ [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : ∃ y ∈ Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

theorem Periodic.image_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩

theorem Periodic.image_Icc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self

theorem Periodic.image_uIcc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : c ≠ 0) (a : α) : f '' uIcc a (a + c) = range f := by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le), ← h.neg.image_Icc (neg_pos.2 hc) (a + c),
      add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

/-! ### Antiperiodicity -/

theorem Antiperiodic.add_nat_mul_eq [NonAssocSemiring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

theorem Antiperiodic.sub_nat_mul_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

theorem Antiperiodic.nat_mul_sub_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

theorem Antiperiodic.const_smul₀ [AddMonoid α] [Neg β] [Monoid γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} {ha : IsUnit a} :
    Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀] using h (a • x)

theorem Antiperiodic.const_mul [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ (a := a)

theorem Antiperiodic.const_inv_smul₀ [AddMonoid α] [Neg β] [Monoid γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} {ha : IsUnit a} :
    Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) :=
  fun x => by simpa only [smul_add, inv_smul_smul₀] using h (a⁻¹ • x)

theorem Antiperiodic.const_inv_mul [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ (a := a)

theorem Antiperiodic.mul_const [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  fun x => by simpa only [add_mul, inv_mul_cancel_right₀] using h (x * a)

theorem Antiperiodic.mul_const' [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (x * a)) (c / a) :=
  fun x => by simpa only [add_mul, div_mul_cancel₀] using h (x * a)

theorem Antiperiodic.mul_const_inv [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  fun x => by simpa only [add_mul, mul_inv_cancel_right₀] using h (x * a⁻¹)

theorem Antiperiodic.div_inv [Semiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    {ha : IsUnit a} : Antiperiodic (fun x => f (x / a)) (c * a) :=
  fun x => by simpa only [add_div, mul_div_cancel_right₀] using h (x / a)

end Function

theorem Int.fract_periodic (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_intCast a 1

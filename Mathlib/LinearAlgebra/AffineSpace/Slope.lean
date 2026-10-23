/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

@[expose] public section

open AffineMap

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

/-- `slope f a b hab` is the slope of `f` between two distinct points `a` and `b`. -/
noncomputable def slope (f : k → PE) (a b : k) (hab : a ≠ b) : E :=
  (↑(Units.mk0 (b - a) (sub_ne_zero.mpr hab.symm))⁻¹ : k) • (f b -ᵥ f a)

theorem slope_def (f : k → PE) (a b : k) (hab : a ≠ b) :
    slope f a b hab =
      (↑(Units.mk0 (b - a) (sub_ne_zero.mpr hab.symm))⁻¹ : k) • (f b -ᵥ f a) :=
  rfl

theorem slope_def_field (f : k → k) (a b : k) (hab : a ≠ b) :
    slope f a b hab = (f b - f a) /ₚ Units.mk0 (b - a) (sub_ne_zero.mpr hab.symm) := by
  rw [slope, divp]
  exact mul_comm _ _

theorem slope_def_module (f : k → E) (a b : k) (hab : a ≠ b) :
    slope f a b hab =
      (↑(Units.mk0 (b - a) (sub_ne_zero.mpr hab.symm))⁻¹ : k) • (f b - f a) :=
  rfl

@[simp]
theorem sub_smul_slope (f : k → PE) (a b : k) (hab : a ≠ b) :
    (b - a) • slope f a b hab = f b -ᵥ f a := by
  rw [slope, smul_smul]
  let u := Units.mk0 (b - a) (sub_ne_zero.mpr hab.symm)
  change ((u : k) * (↑u⁻¹ : k)) • (f b -ᵥ f a) = f b -ᵥ f a
  rw [Units.mul_inv, one_smul]

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) (hab : a ≠ b) :
    (b - a) • slope f a b hab +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

@[simp]
theorem slope_vadd_const (f : k → E) (c : PE) (a b : k) (hab : a ≠ b) :
    slope (fun x => f x +ᵥ c) a b hab = slope f a b hab := by
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]
theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) :
    slope (fun x => (x - a) • f x) a b h = f b := by
  rw [slope]
  simp only [vsub_eq_sub, sub_self, zero_smul, sub_zero, smul_smul]
  let u := Units.mk0 (b - a) (sub_ne_zero.mpr h.symm)
  change ((↑u⁻¹ : k) * (u : k)) • f b = f b
  rw [Units.inv_mul, one_smul]

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (hab : a ≠ b)
    (h : slope f a b hab = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b hab, h, smul_zero, zero_vadd]

theorem AffineMap.slope_comp {F PF : Type*} [AddCommGroup F] [Module k F] [AddTorsor F PF]
    (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) (hab : a ≠ b) :
    slope (f ∘ g) a b hab = f.linear (slope g a b hab) := by
  simp only [slope, (· ∘ ·), f.linear.map_smul, f.linearMap_vsub]

theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E →ₗ[k] F) (g : k → E)
    (a b : k) (hab : a ≠ b) : slope (f ∘ g) a b hab = f (slope g a b hab) :=
  f.toAffineMap.slope_comp g a b hab

theorem slope_comm (f : k → PE) (a b : k) (hab : a ≠ b) :
    slope f a b hab = slope f b a hab.symm := by
  apply smul_right_injective E (sub_ne_zero.mpr hab.symm)
  change (b - a) • slope f a b hab = (b - a) • slope f b a hab.symm
  rw [sub_smul_slope]
  nth_rewrite 1 [show b - a = -(a - b) by abel]
  rw [neg_smul, sub_smul_slope, neg_vsub_eq_vsub_rev]

@[simp] lemma slope_neg (f : k → E) (x y : k) (hxy : x ≠ y) :
    slope (fun t ↦ -f t) x y hxy = -slope f x y hxy := by
  simp only [slope_def_module, neg_sub_neg, ← smul_neg, neg_sub]

lemma slope_eq_zero_iff {f : k → E} {a b : k} (hab : a ≠ b) :
    slope f a b hab = 0 ↔ f a = f b := by
  constructor
  · exact eq_of_slope_eq_zero hab
  · rintro h
    simp [slope, h]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `lineMap_slope_slope_sub_div_sub`. -/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ((b - a) /ₚ Units.mk0 (c - a) (sub_ne_zero.mpr hac.symm)) • slope f a b hab +
      ((c - b) /ₚ Units.mk0 (c - a) (sub_ne_zero.mpr hac.symm)) • slope f b c hbc =
        slope f a c hac := by
  let u := Units.mk0 (c - a) (sub_ne_zero.mpr hac.symm)
  apply smul_right_injective E (sub_ne_zero.mpr hac.symm)
  change (c - a) •
      (((b - a) /ₚ u) • slope f a b hab + ((c - b) /ₚ u) • slope f b c hbc) =
    (c - a) • slope f a c hac
  simp only [smul_add, smul_smul]
  change ((u : k) * ((b - a) /ₚ u)) • slope f a b hab +
      ((u : k) * ((c - b) /ₚ u)) • slope f b c hbc =
    (c - a) • slope f a c hac
  rw [mul_comm (u : k), divp_mul_cancel, mul_comm (u : k), divp_mul_cancel,
    sub_smul_slope, sub_smul_slope, sub_smul_slope]
  rw [add_comm, vsub_add_vsub_cancel]

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`lineMap` to express this property. -/
theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    lineMap (slope f a b hab) (slope f b c hbc)
      ((c - b) /ₚ Units.mk0 (c - a) (sub_ne_zero.mpr hac.symm)) = slope f a c hac := by
  let u := Units.mk0 (c - a) (sub_ne_zero.mpr hac.symm)
  have hpq : (b - a) /ₚ u + (c - b) /ₚ u = 1 := by
    simp only [divp, ← add_mul]
    rw [show b - a + (c - b) = c - a by abel]
    change (u : k) * (↑u⁻¹ : k) = 1
    exact Units.mul_inv u
  have hp : (b - a) /ₚ u = 1 - (c - b) /ₚ u := eq_sub_of_add_eq hpq
  rw [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c
    hab hbc hac, hp, sub_smul, one_smul]

/-- `slope f a b` is an affine combination of `slope f a (lineMap a b r)` and
`slope f (lineMap a b r) b`. We use `lineMap` to express this property. -/
theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k)
    (hab : a ≠ b) (hrb : lineMap a b r ≠ b) (har : a ≠ lineMap a b r) :
    lineMap (slope f (lineMap a b r) b hrb) (slope f a (lineMap a b r) har) r =
      slope f a b hab := by
  rw [slope_comm f a b hab, slope_comm f a (lineMap a b r) har,
    slope_comm f (lineMap a b r) b hrb]
  convert lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hrb.symm har.symm hab.symm using 2
  symm
  apply divp_eq_iff_mul_eq.mpr
  change r * (a - b) = a - lineMap a b r
  rw [lineMap_apply_ring, mul_sub, sub_mul, one_mul]
  abel

section Order

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

lemma slope_nonneg_iff_of_le (hxy : x ≤ y) (hne : x ≠ y) :
    0 ≤ slope f x y hne ↔ f x ≤ f y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [sub_smul_slope, vsub_eq_sub, sub_nonneg] at this
  · rw [slope]
    exact smul_nonneg ((Units.inv_nonneg _).2 (sub_nonneg.2 hxy))
      (by rwa [vsub_eq_sub, sub_nonneg])

lemma MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hne : x ≠ y) : 0 ≤ slope f x y hne := by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy hne).mpr (hf hx hy hxy)
  · exact slope_comm f x y hne ▸
      (slope_nonneg_iff_of_le hxy hne.symm).mpr (hf hy hx hxy)

lemma slope_nonpos_iff_of_le (hxy : x ≤ y) (hne : x ≠ y) :
    slope f x y hne ≤ 0 ↔ f y ≤ f x := by
  rw [← neg_nonneg, ← slope_neg, slope_nonneg_iff_of_le hxy hne, neg_le_neg_iff]

lemma AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hne : x ≠ y) : slope f x y hne ≤ 0 := by
  simpa using hf.neg.slope_nonneg hx hy hne

lemma slope_pos_iff_of_le (hxy : x ≤ y) (hne : x ≠ y) :
    0 < slope f x y hne ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy hne, Ne, eq_comm,
    slope_eq_zero_iff hne]

lemma StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < slope f x y hxy := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le hxy.ne).mpr (hf hx hy hxy)
  · exact slope_comm f x y hxy.ne' ▸
      (slope_pos_iff_of_le hxy.le hxy.ne).mpr (hf hy hx hxy)

lemma slope_neg_iff_of_le (hxy : x ≤ y) (hne : x ≠ y) :
    slope f x y hne < 0 ↔ f y < f x := by
  rw [← neg_pos, ← slope_neg, slope_pos_iff_of_le hxy hne, neg_lt_neg_iff]

lemma StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : slope f x y hxy < 0 := by
  simpa using hf.neg.slope_pos hx hy hxy

end Order

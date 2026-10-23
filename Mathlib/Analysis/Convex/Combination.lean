/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Basis

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `Finset.centerMass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `Finset.centerMass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Function Pointwise

universe u u'

section
variable {R R' E F ι ι' α : Type*} [Field R] [Field R'] [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup α] [LinearOrder α] [Module R E] [Module R F] [Module R α] {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
The sum of the weights must be nonzero; the weights need not be nonnegative or sum to one. -/
noncomputable def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E)
    (hw : ∑ i ∈ t, w i ≠ 0) : E :=
  (↑(Units.mk0 (∑ i ∈ t, w i) hw)⁻¹ : R) • ∑ i ∈ t, w i • z i

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset

theorem Finset.centerMass_pair [DecidableEq ι] (hne : i ≠ j) (hw : w i + w j ≠ 0) :
    ({i, j} : Finset ι).centerMass w z (by simpa only [sum_pair hne] using hw) =
      (w i /ₚ Units.mk0 (w i + w j) hw) • z i +
        (w j /ₚ Units.mk0 (w i + w j) hw) • z j := by
  simp only [centerMass, sum_pair hne, smul_add, divp, mul_smul]
  module

variable {w}

theorem Finset.centerMass_insert [DecidableEq ι] (ha : i ∉ t)
    (hw : ∑ j ∈ t, w j ≠ 0) (hwi : w i + ∑ j ∈ t, w j ≠ 0) :
    (insert i t).centerMass w z (by simpa only [sum_insert ha] using hwi) =
      (w i /ₚ Units.mk0 (w i + ∑ j ∈ t, w j) hwi) • z i +
        ((∑ j ∈ t, w j) /ₚ Units.mk0 (w i + ∑ j ∈ t, w j) hwi) •
          t.centerMass w z hw := by
  simp only [centerMass, sum_insert ha, smul_add, divp, mul_smul]
  have hcancel : (∑ j ∈ t, w j) *
      (↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R) = 1 :=
    Units.mul_inv (Units.mk0 (∑ j ∈ t, w j) hw)
  have hinv : (↑(Units.mk0 (w i + ∑ j ∈ t, w j) hwi)⁻¹ : R) =
      ((↑(Units.mk0 (w i + ∑ j ∈ t, w j) hwi)⁻¹ : R) * ∑ j ∈ t, w j) *
        (↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R) := by
    symm
    rw [mul_assoc, hcancel, mul_one]
  simp only [smul_smul]
  apply congrArg₂ (· + ·)
  · rw [mul_comm]
  · apply congrArg (· • ∑ j ∈ t, w j • z j)
    calc
      (↑(Units.mk0 (w i + ∑ j ∈ t, w j) hwi)⁻¹ : R) =
          ((↑(Units.mk0 (w i + ∑ j ∈ t, w j) hwi)⁻¹ : R) * ∑ j ∈ t, w j) *
            (↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R) := hinv
      _ = (∑ j ∈ t, w j) *
          ((↑(Units.mk0 (w i + ∑ j ∈ t, w j) hwi)⁻¹ : R) *
            (↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R)) := by ac_rfl

theorem Finset.centerMass_singleton (hw : w i ≠ 0) :
    ({i} : Finset ι).centerMass w z (by simpa only [sum_singleton] using hw) = z i := by
  simp only [centerMass, sum_singleton]
  rw [smul_smul]
  change ((↑(Units.mk0 (w i) hw)⁻¹ : R) * w i) • z i = z i
  rw [show (↑(Units.mk0 (w i) hw)⁻¹ : R) * w i = 1 by exact Units.inv_mul _, one_smul]

@[simp] lemma Finset.centerMass_neg_left (hw : ∑ i ∈ t, w i ≠ 0) :
    t.centerMass (-w) z (by simpa only [Pi.neg_apply, sum_neg_distrib] using neg_ne_zero.mpr hw) =
      t.centerMass w z hw := by
  let u := Units.mk0 (∑ i ∈ t, w i) hw
  let un := Units.mk0 (-(∑ i ∈ t, w i)) (neg_ne_zero.mpr hw)
  have hun : un = -u := by apply Units.ext; rfl
  simp only [centerMass, Pi.neg_apply, sum_neg_distrib, neg_smul]
  change (↑un⁻¹ : R) • -(∑ i ∈ t, w i • z i) = (↑u⁻¹ : R) • ∑ i ∈ t, w i • z i
  rw [hun]
  simp

lemma Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
    [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R E] (hc : c ≠ 0)
    (hw : ∑ i ∈ t, w i ≠ 0) :
    t.centerMass (c • w) z (by
      simp only [Pi.smul_apply, ← smul_sum]
      exact smul_ne_zero hc hw) =
      t.centerMass w z hw := by
  have hsum : ∑ i ∈ t, (c • w) i = c • ∑ i ∈ t, w i := by
    simp only [Pi.smul_apply, smul_sum]
  have hsumz : ∑ i ∈ t, (c • w) i • z i = c • ∑ i ∈ t, w i • z i := by
    simp only [Pi.smul_apply, smul_assoc, smul_sum]
  unfold centerMass
  simp only [hsum, hsumz]
  let v := Units.mk0 (∑ i ∈ t, w i) hw
  let q := Units.mk0 (c • ∑ i ∈ t, w i) (smul_ne_zero hc hw)
  apply smul_right_injective E q.ne_zero
  change (q : R) • ((↑q⁻¹ : R) • (c • ∑ i ∈ t, w i • z i)) =
    (q : R) • ((↑v⁻¹ : R) • ∑ i ∈ t, w i • z i)
  rw [smul_smul, Units.mul_inv, one_smul]
  symm
  change (c • ∑ i ∈ t, w i) •
      ((↑v⁻¹ : R) • ∑ i ∈ t, w i • z i) = c • ∑ i ∈ t, w i • z i
  rw [smul_smul, smul_mul_assoc,
    show (∑ i ∈ t, w i) * (↑v⁻¹ : R) = 1 by exact Units.mul_inv v, smul_assoc, one_smul]

theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i ∈ t, w i = 1) :
    t.centerMass w z (hw.symm ▸ one_ne_zero) = ∑ i ∈ t, w i • z i := by
  simp only [Finset.centerMass, hw, Units.mk0_one, inv_one]
  change (1 : R) • (∑ i ∈ t, w i • z i) = ∑ i ∈ t, w i • z i
  exact one_smul _ _

theorem Finset.centerMass_smul (hw : ∑ i ∈ t, w i ≠ 0) :
    (t.centerMass w (fun i => c • z i) hw) = c • t.centerMass w z hw := by
  simp only [Finset.centerMass, Finset.smul_sum, smul_comm c]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E)
    (wt : ι' → R) (zt : ι' → E) (hws : ∑ i ∈ s, ws i = 1) (hwt : ∑ i ∈ t, wt i = 1) (a b : R)
    (hab : a + b = 1) :
    a • s.centerMass ws zs (hws.symm ▸ one_ne_zero) +
      b • t.centerMass wt zt (hwt.symm ▸ one_ne_zero) =
        (s.disjSum t).centerMass
          (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt)
          (by
            simp only [sum_sumElim, ← mul_sum, hws, hwt, mul_one, hab]
            exact one_ne_zero) := by
  rw [s.centerMass_eq_of_sum_1 _ hws, t.centerMass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←
    Finset.sum_sumElim, Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z (hw₁.symm ▸ one_ne_zero) +
      b • s.centerMass w₂ z (hw₂.symm ▸ one_ne_zero) =
        s.centerMass (fun i => a * w₁ i + b * w₂ i) z
          (by
            simp only [← mul_sum, sum_add_distrib, hw₁, hw₂, mul_one, hab]
            exact one_ne_zero) := by
  have hw : (∑ i ∈ s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

theorem Finset.centerMass_ite_eq [DecidableEq ι] (hi : i ∈ t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z
      (by simp only [sum_ite_eq, ite_eq_left hi]; exact one_ne_zero) = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j ∈ t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, ite_eq_left hi]
  · rw [sum_ite_eq, ite_eq_left hi]

variable {t}

theorem Finset.centerMass_subset {t' : Finset ι} (ht : t ⊆ t')
    (h : ∀ i ∈ t', i ∉ t → w i = 0) (hw : ∑ i ∈ t, w i ≠ 0) :
    t.centerMass w z hw = t'.centerMass w z (by simpa only [sum_subset ht h] using hw) := by
  have hsum : ∑ i ∈ t, w i = ∑ i ∈ t', w i := sum_subset ht h
  have hsumz : ∑ i ∈ t, w i • z i = ∑ i ∈ t', w i • z i := by
    apply sum_subset ht
    intro i hit' hit
    rw [h i hit' hit, zero_smul]
  simp only [centerMass, hsum, hsumz]

theorem Finset.centerMass_filter_ne_zero [∀ i, Decidable (w i ≠ 0)]
    (hw : ∑ i ∈ t, w i ≠ 0) :
    {i ∈ t | w i ≠ 0}.centerMass w z
      (by simpa only [sum_filter_ne_zero] using hw) = t.centerMass w z hw :=
  Finset.centerMass_subset z (filter_subset _ _) (fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit') _

namespace Finset

variable [LinearOrder R] [IsOrderedAddMonoid α] [PosSMulMono R α]

theorem centerMass_le_sup {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.centerMass w f hw₁.ne' ≤ s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
  rw [centerMass]
  change (Units.mk0 (∑ i ∈ s, w i) hw₁.ne')⁻¹ • (∑ i ∈ s, w i • f i) ≤ _
  rw [inv_smul_le_iff_of_pos hw₁, sum_smul]
  exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) <| hw₀ i hi

theorem inf_le_centerMass {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f ≤
      s.centerMass w f hw₁.ne' :=
  centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

end Finset

variable {z}

lemma Finset.centerMass_const (hw : ∑ j ∈ t, w j ≠ 0) (c : E) :
    t.centerMass w (Function.const _ c) hw = c := by
  simp only [centerMass, Function.const_apply, ← sum_smul]
  rw [smul_smul]
  change ((↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R) * (∑ j ∈ t, w j)) • c = c
  rw [show (↑(Units.mk0 (∑ j ∈ t, w j) hw)⁻¹ : R) * (∑ j ∈ t, w j) = 1 by
    exact Units.inv_mul _, one_smul]

lemma Finset.centerMass_congr [DecidableEq ι] {t' : Finset ι} {w' : ι → R} {z' : ι → E}
    (h : ∀ i, (i ∈ t ∧ w i ≠ 0 ∨ i ∈ t' ∧ w' i ≠ 0) →
      i ∈ t ∩ t' ∧ w i = w' i ∧ z i = z' i)
    (hw : ∑ i ∈ t, w i ≠ 0) (hw' : ∑ i ∈ t', w' i ≠ 0) :
    t.centerMass w z hw = t'.centerMass w' z' hw' := by
  classical
  let ft := {i ∈ t | w i ≠ 0}
  let ft' := {i ∈ t' | w' i ≠ 0}
  have hft : ft = ft' := by
    ext i
    simp only [ft, ft', mem_filter]
    constructor <;> rintro hi
    · have hh := h i (Or.inl hi)
      exact ⟨(mem_inter.mp hh.1).2, hh.2.1 ▸ hi.2⟩
    · have hh := h i (Or.inr hi)
      exact ⟨(mem_inter.mp hh.1).1, hh.2.1.symm ▸ hi.2⟩
  have hsw : ∑ i ∈ t, w i = ∑ i ∈ t', w' i := by
    rw [← sum_filter_ne_zero t, ← sum_filter_ne_zero t', show {i ∈ t | w i ≠ 0} = ft from rfl,
      show {i ∈ t' | w' i ≠ 0} = ft' from rfl, hft]
    exact sum_congr rfl fun i hi ↦ by
      have hi' : i ∈ t' ∧ w' i ≠ 0 := by simpa only [ft', mem_filter] using hi
      exact (h i (Or.inr hi')).2.1
  have hsz : ∑ i ∈ t, w i • z i = ∑ i ∈ t', w' i • z' i := by
    calc
      ∑ i ∈ t, w i • z i = ∑ i ∈ ft, w i • z i := by
        symm
        apply sum_subset (filter_subset _ _)
        intro i hit hif
        simp only [mem_filter, hit, true_and, not_not] at hif
        simp [hif]
      _ = ∑ i ∈ ft', w' i • z' i := by
        rw [hft]
        exact sum_congr rfl fun i hi ↦ by
          have hi' : i ∈ t' ∧ w' i ≠ 0 := by simpa only [ft', mem_filter] using hi
          rw [(h i (Or.inr hi')).2.1, (h i (Or.inr hi')).2.2]
      _ = ∑ i ∈ t', w' i • z' i := by
        apply sum_subset (filter_subset _ _)
        intro i hit hif
        simp only [mem_filter, hit, true_and, not_not] at hif
        simp [hif]
  unfold centerMass
  simp only [hsw, hsz]

lemma Finset.centerMass_congr_finset [DecidableEq ι] {t' : Finset ι}
    (h : ∀ i ∈ t ∪ t', w i ≠ 0 → i ∈ t ∩ t')
    (hw : ∑ i ∈ t, w i ≠ 0) (hw' : ∑ i ∈ t', w i ≠ 0) :
    t.centerMass w z hw = t'.centerMass w z hw' :=
  centerMass_congr (by grind) hw hw'

lemma Finset.centerMass_congr_weights {w' : ι → R} (h : ∀ i ∈ t, w i = w' i)
    (hw : ∑ i ∈ t, w i ≠ 0) (hw' : ∑ i ∈ t, w' i ≠ 0) :
    t.centerMass w z hw = t.centerMass w' z hw' := by
  classical
  exact centerMass_congr (by grind) hw hw'

lemma Finset.centerMass_congr_fun {z' : ι → E} (h : ∀ i ∈ t, w i ≠ 0 → z i = z' i)
    (hw : ∑ i ∈ t, w i ≠ 0) : t.centerMass w z hw = t.centerMass w z' hw := by
  classical
  exact centerMass_congr (by grind) hw hw

lemma Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι}
    (hw : ∑ i ∈ s, w i + ∑ i ∈ t, w i = 0)
    (hz : ∑ i ∈ s, w i • z i + ∑ i ∈ t, w i • z i = 0)
    (hs : ∑ i ∈ s, w i ≠ 0) (ht : ∑ i ∈ t, w i ≠ 0) :
    s.centerMass w z hs = t.centerMass w z ht := by
  have hsum : ∑ i ∈ t, (-w) i = ∑ i ∈ s, w i := by
    simp only [Pi.neg_apply, sum_neg_distrib, eq_neg_of_add_eq_zero_right hw, neg_neg]
  have hsumz : ∑ i ∈ t, (-w i) • z i = ∑ i ∈ s, w i • z i := by
    simp only [neg_smul, sum_neg_distrib, eq_neg_of_add_eq_zero_right hz, neg_neg]
  calc
    s.centerMass w z hs = t.centerMass (-w) z (by simpa only [hsum] using hs) := by
      unfold centerMass
      let us := Units.mk0 (∑ i ∈ s, w i) hs
      let unt := Units.mk0 (∑ i ∈ t, (-w) i) (by simpa only [hsum] using hs)
      have hu : unt = us := by apply Units.ext; exact hsum
      change (↑us⁻¹ : R) • (∑ i ∈ s, w i • z i) =
        (↑unt⁻¹ : R) • (∑ i ∈ t, (-w i) • z i)
      rw [hu, hsumz]
    _ = t.centerMass w z ht := centerMass_neg_left (t := t) (w := w) (z := z) ht

variable [LinearOrder R] [IsStrictOrderedRing R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem Convex.centerMass_mem (hs : Convex R s) :
    ∀ (_h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i ∈ t, w i) (_hmem : ∀ i ∈ t, z i ∈ s),
      t.centerMass w z hpos.ne' ∈ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j ∈ t, w j = 0
    · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j ∈ t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [smul_smul]
      change ((↑(Units.mk0 (w i) hpos.ne')⁻¹ : R) * w i) • z i ∈ s
      rw [show (↑(Units.mk0 (w i) hpos.ne')⁻¹ : R) * w i = 1 by
        exact Units.inv_mul (Units.mk0 (w i) hpos.ne'), one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t hpos.ne']
      let u := Units.mk0 (w i + ∑ j ∈ t, w j) hpos.ne'
      refine hs zi (ht hs₀ ?_ ?_)
        (divp_nonneg (h₀ _ (mem_insert_self _ _)) hpos.le)
        (divp_nonneg (sum_nonneg hs₀) hpos.le) ?_
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · rw [Units.divp_add_divp_same]
        exact divp_self u

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : (∑ i ∈ t, w i • z i) ∈ s := by
  rw [← t.centerMass_eq_of_sum_1 z h₁]
  exact hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/-- A version of `Convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0`, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`PartitionOfUnity.finsum_smul_mem_convex`. -/
theorem Convex.finsum_mem {ι : Sort*} {w : ι → R} {z : ι → E} {s : Set E} (hs : Convex R s)
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) :
    (∑ᶠ i, w i • z i) ∈ s := by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum, dite_eq_right H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) ⊆ hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dite_eq_left hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi

theorem convex_iff_sum_mem : Convex R s ↔ ∀ (t : Finset E) (w : E → R),
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ x ∈ t, x ∈ s) → (∑ x ∈ t, w x • x) ∈ s := by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert! h { x, y } (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, ite_eq_right h_cases, ite_eq_left trivial]
    · grind
    · simp only [sum_pair h_cases, ite_eq_right h_cases, ite_eq_left trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption

theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z hws.ne' ∈ convexHull R s :=
  (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s <| hz i hi

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
lemma Finset.centerMass_mem_convexHull_of_nonpos (t : Finset ι) (hw₀ : ∀ i ∈ t, w i ≤ 0)
    (hws : ∑ i ∈ t, w i < 0) (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z hws.ne ∈ convexHull R s := by
  rw [← centerMass_neg_left (t := t) (w := w) (z := z) hws.ne]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi ↦ neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

/-- A refinement of `Finset.centerMass_mem_convexHull` when the indexed family is a `Finset` of
the space. -/
theorem Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) : t.centerMass w id hws.ne' ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
lemma Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E → R}
    (hw₀ : ∀ i ∈ t, w i ≤ 0) (hws : ∑ i ∈ t, w i < 0) :
    t.centerMass w id hws.ne ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ ↦ mem_coe.2

theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R}
    (hw₂ : ∑ i ∈ t, w i = 1) :
    t.affineCombination R p w = centerMass t w p (hw₂.symm ▸ one_ne_zero) := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_zero, t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι → E} {w : ι → R}
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w ∈ convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

/-- The centroid can be regarded as a center of mass. -/
@[simp]
theorem Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid R p (Nat.cast_ne_zero.mpr (card_ne_zero.mpr hs)) =
      s.centerMass (s.centroidWeights R (Nat.cast_ne_zero.mpr (card_ne_zero.mpr hs))) p
        ((s.sum_centroidWeights_eq_one_of_nonempty R hs).symm ▸ one_ne_zero) :=
  affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)

theorem Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) :
    s.centroid R id (Nat.cast_ne_zero.mpr (card_ne_zero.mpr hs)) ∈ convexHull R (s : Set E) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · intro i hi
    exact (Units.inv_nonneg _).2 (Nat.cast_nonneg _)
  · rw [s.sum_centroidWeights_eq_one_of_nonempty R hs]
    exact zero_lt_one

theorem convexHull_range_eq_exists_affineCombination (v : ι → E) : convexHull R (range v) =
    { x | ∃ (s : Finset ι) (w : ι → R), (∀ i ∈ s, 0 ≤ w i) ∧ s.sum w = 1 ∧
      s.affineCombination R v w = x } := by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι → R := fun i => (if i ∈ s then a * w i else 0) + if i ∈ s' then b * w' i else 0
    have hW₁ : (s ∪ s').sum W = 1 := by
      rw [sum_add_distrib, ← sum_subset subset_union_left,
        ← sum_subset subset_union_right, sum_ite_of_true,
        sum_ite_of_true, ← mul_sum, ← mul_sum, hw₁, hw₁', ← add_mul, hab,
        mul_one] <;> intros <;> simp_all
    refine ⟨s ∪ s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i ∈ s <;> by_cases hi' : i ∈ s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s ∪ s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left, ← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

/--
Convex hull of `s` is equal to the set of all centers of masses of `Finset`s `t`, `z '' t ⊆ s`.
For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use convexity of the convex hull instead.
-/
theorem convexHull_eq (s : Set E) : convexHull R s =
    { x : E | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E),
      ∃ hw : ∑ i ∈ t, w i = 1, (∀ i ∈ t, 0 ≤ w i) ∧ (∀ i ∈ t, z i ∈ s) ∧
        t.centerMass w z (hw.symm ▸ one_ne_zero) = x } := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, sum_singleton _ _,
      fun _ _ => zero_le_one, fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, Units.mk0_one, inv_one, smul_smul]
    change ((1 : R) * 1) • x = x
    rw [one_mul, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₁, hwx₀, hzx, rfl⟩
      y ⟨ι', sy, wy, zy, hwy₁, hwy₀, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · simp [← mul_sum, *]
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₁, hw₀, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

/-- Universe polymorphic version of the reverse implication of `mem_convexHull_iff_exists_fintype`.
-/
lemma mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι → R) (z : ι → E)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hz : ∀ i, z i ∈ s) (hx : ∑ i, w i • z i = x) :
    x ∈ convexHull R s := by
  rw [← hx, ← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

/-- The convex hull of `s` is equal to the set of centers of masses of finite families of points in
`s`.

For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use `mem_convexHull_of_exists_fintype` of the convex hull instead. -/
lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ convexHull R s ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → R) (z : ι → E), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  constructor
  · simp only [convexHull_eq, mem_ofPred_eq]
    rintro ⟨ι, t, w, z, hw, h₀, hz, hcm⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h₀
    · simpa [← sum_attach t] using hw
    · simpa using hz
    · simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ hw] using hcm
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | ∃ (w : E → R) (hw : ∑ y ∈ s, w y = 1), (∀ y ∈ s, 0 ≤ w y) ∧
      s.centerMass w id (hw.symm ▸ one_ne_zero) = x } := by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · rw [Finset.sum_ite_eq, ite_eq_left hx]
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
  · rintro x ⟨wx, hwx₁, hwx₀, rfl⟩ y ⟨wy, hwy₁, hwy₀, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
  · rintro _ ⟨w, hw₁, hw₀, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

theorem Finset.mem_convexHull {s : Finset E} {x : E} : x ∈ convexHull R (s : Set E) ↔
    ∃ (w : E → R) (hw : ∑ y ∈ s, w y = 1), (∀ y ∈ s, 0 ≤ w y) ∧
      s.centerMass w id (hw.symm ▸ one_ne_zero) = x := by
  rw [Finset.convexHull_eq, Set.mem_ofPred_eq]

/-- This is a version of `Finset.mem_convexHull` stated without `Finset.centerMass`. -/
lemma Finset.mem_convexHull' {s : Finset E} {x : E} :
    x ∈ convexHull R (s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x := by
  rw [mem_convexHull]
  constructor
  · rintro ⟨w, hw, h₀, hcm⟩
    exact ⟨w, h₀, hw, by simpa only [centerMass_eq_of_sum_1 _ _ hw, id_eq] using hcm⟩
  · rintro ⟨w, h₀, hw, hsum⟩
    exact ⟨w, hw, h₀, by simpa only [centerMass_eq_of_sum_1 _ _ hw, id_eq] using hsum⟩

theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | ∃ (w : E → R) (hw : ∑ y ∈ hs.toFinset, w y = 1),
      (∀ y ∈ s, 0 ≤ w y) ∧ hs.toFinset.centerMass w id (hw.symm ▸ one_ne_zero) = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (_ : ↑t ⊆ s), convexHull R ↑t := by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₁, hw₀, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

/-- The `vectorSpan` of a segment is the span of the difference of its endpoints. -/
theorem vectorSpan_segment {p₁ p₂ : E} :
    vectorSpan R (segment R p₁ p₂) = R ∙ (p₂ -ᵥ p₁) := by
  rw [← convexHull_pair, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub]

theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s)
    (hy : y ∈ convexHull R t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hw₁, hv₁, mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p ↦ (f p.1, g p.2),
    fun p ↦ mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p ↦ ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]
theorem convexHull_prod (s : Set E) (t : Set F) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
        (convex_convexHull _ _).prod <| convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx

theorem convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

variable (R E)

/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
noncomputable def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

variable {R E}

theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]

theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l

theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s

theorem convexHull_sum {ι} (s : Finset ι) (t : ι → Set E) :
    convexHull R (∑ i ∈ s, t i) = ∑ i ∈ s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _

/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
theorem AffineBasis.convexHull_eq_nonneg_coord {ι : Type*} (b : AffineBasis ι R E) :
    convexHull R (range b) = { x | ∀ i, 0 ≤ b.coord i x } := by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i ∈ s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x ∈ affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

variable {s t₁ t₂ : Finset E}

/-- Two simplices glue nicely if the union of their vertices is affine independent. -/
lemma AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s → E))
    (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ := by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x ∈ t₁ then w₁ x else 0) - if x ∈ t₂ then w₂ x else 0
  have h₁w : ∑ i ∈ s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
  replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w <| by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x ∈ t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ ↦ h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

/-- Two simplices glue nicely if the union of their vertices is affine independent.

Note that `AffineIndependent.convexHull_inter` should be more versatile in most use cases. -/
lemma AffineIndependent.convexHull_inter' [DecidableEq E]
    (hs : AffineIndependent R ((↑) : ↑(t₁ ∪ t₂) → E)) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ :=
  hs.convexHull_inter subset_union_left subset_union_right

end

section pi
variable {𝕜 ι : Type*} {E : ι → Type*} [Finite ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {x : Π i, E i}

open Finset Fintype

lemma mem_convexHull_pi (h : ∀ i ∈ s, x i ∈ convexHull 𝕜 (t i)) : x ∈ convexHull 𝕜 (s.pi t) := by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ ↦ ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i ↦ ∏ i, w i (k i)) (fun g i ↦ f _ (g i))
    (fun g ↦ prod_nonneg fun _ _ ↦ hw₀ _ _) ?_ (fun _ _ _ ↦ hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ ↦ hw₁ _
  ext i
  calc
    _ = ∑ g : ∀ i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : ∀ k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : ∀ i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : ∀ k, κ k ↦ g i]
    _ = ∑ j : κ i, (∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g ∈ piFinset fun k ↦ if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ ↦ g) (fun g hg ↦ ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum, ← prod_mul_prod_compl, Finset.prod_singleton, Finset.sum_eq_single,
        Finset.prod_eq_one, mul_one] <;> simp +contextual [hw₁]

@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i ↦ convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ ↦ subset_convexHull _ _) <| convex_pi <|
    fun _ _ ↦ convex_convexHull _ _) fun _ ↦ mem_convexHull_pi

end pi

/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Constructions.Pi


/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occurring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the probability over
the entire sample space when `s = Set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `ProbabilityTheory.uniformOn`: given a finite nonempty measurable set `s`, `uniformOn s hs` is the
  counting measure conditioned on `s`, the uniform probability measure on `s`. Its argument `hs`
  states that the counting measure can be conditioned on `s` (`isConditionable_count_iff`).

## Notes

The original aim of this file is to provide a measure-theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allows us to describe this by abusing the definitional equality of sets and predicates by simply
writing `uniformOn s hs P`. We should avoid this however as none of the lemmas are written for
predicates.
-/

@[expose] public section


noncomputable section

open ProbabilityTheory

open MeasureTheory SigmaAlgebra Finset

namespace ProbabilityTheory

variable {Ω : Type*} [SigmaAlgebra Ω] {s : Set Ω}

/-- The counting measure can be conditioned exactly on the finite nonempty measurable sets. -/
lemma isConditionable_count_iff :
    IsConditionable Measure.count s ↔ MeasurableSet s ∧ s.Finite ∧ s.Nonempty := by
  have hm : NullMeasurableSet s Measure.count ↔ MeasurableSet s := by
    refine ⟨fun h ↦ ?_, MeasurableSet.nullMeasurableSet⟩
    have h' := h.toMeasurable_ae_eq
    rw [ae_eq_set, Measure.count_eq_zero_iff, Measure.count_eq_zero_iff, Set.sdiff_eq_empty,
      Set.sdiff_eq_empty] at h'
    exact h'.1.antisymm h'.2 ▸ measurableSet_toMeasurable _ _
  rw [isConditionable_iff, hm, Measure.count_ne_zero_iff]
  refine ⟨fun ⟨hs, hne, hfin⟩ ↦ ⟨hs, ?_, hne⟩, fun ⟨hs, hfin, hne⟩ ↦ ⟨hs, hne, ?_⟩⟩
  · exact (Measure.count_apply_lt_top' hs).1 (lt_top_iff_ne_top.2 hfin)
  · exact ((Measure.count_apply_lt_top' hs).2 hfin).ne

lemma IsConditionable.count (hm : MeasurableSet s) (hs : s.Finite) (hs' : s.Nonempty) :
    IsConditionable Measure.count s :=
  isConditionable_count_iff.2 ⟨hm, hs, hs'⟩

lemma IsConditionable.count_of_finite [MeasurableSingletonClass Ω] (hs : s.Finite)
    (hs' : s.Nonempty) : IsConditionable Measure.count s :=
  .count hs.measurableSet hs hs'

lemma IsConditionable.measurableSet_of_count (hs : IsConditionable Measure.count s) :
    MeasurableSet s :=
  (isConditionable_count_iff.1 hs).1

lemma IsConditionable.finite_of_count (hs : IsConditionable Measure.count s) : s.Finite :=
  (isConditionable_count_iff.1 hs).2.1

lemma IsConditionable.nonempty_of_count (hs : IsConditionable Measure.count s) : s.Nonempty :=
  (isConditionable_count_iff.1 hs).2.2

/-- Given a finite nonempty measurable set `s`, `uniformOn s hs` is the uniform measure on `s`,
defined as the counting measure conditioned by `s`. One should think of `uniformOn s hs t` as the
proportion of `s` that is contained in `t`. The argument `hs` states that the counting measure can
be conditioned on `s`, that is, `s` is finite, nonempty, and measurable
(`isConditionable_count_iff`, `IsConditionable.count_of_finite`). -/
def uniformOn (s : Set Ω) (hs : IsConditionable Measure.count s) : Measure Ω :=
  Measure.count[|s]

/-- The uniform measure on a finite nonempty measurable set is a probability measure. -/
instance isProbabilityMeasure_uniformOn (hs : IsConditionable Measure.count s) :
    IsProbabilityMeasure (uniformOn s hs) :=
  isProbabilityMeasure_cond hs

theorem uniformOn_empty (hs : IsConditionable Measure.count s) : uniformOn s hs ∅ = 0 := by simp

theorem uniformOn_univ [Fintype Ω] [Nonempty Ω] {s : Set Ω} :
    uniformOn Set.univ .univ s = Measure.count s / Fintype.card Ω := by
  simp [uniformOn, cond_apply, ← ENNReal.div_eq_inv_mul]

lemma uniformOn_apply_finset' {Ω : Type*} [DecidableEq Ω] {_ : SigmaAlgebra Ω} {s t : Finset Ω}
    (hs : IsConditionable Measure.count (s : Set Ω)) (ht : MeasurableSet (t : Set Ω)) :
    uniformOn (s : Set Ω) hs (t : Set Ω) = #(s ∩ t) / #s := by
  rw [uniformOn, cond_apply hs, Measure.count_apply_finset' hs.measurableSet_of_count,
    ← coe_inter, Measure.count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.measurableSet_of_count.inter ht

theorem uniformOn_singleton (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)]
    (hω : IsConditionable Measure.count {ω}) :
    uniformOn {ω} hω t = if ω ∈ t then 1 else 0 := by
  rw [uniformOn, cond_apply hω, Measure.count_singleton' hω.measurableSet_of_count, inv_one,
    one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = {ω}), Measure.count_singleton' hω.measurableSet_of_count]
  · simpa

variable {t u : Set Ω}

theorem uniformOn_inter_self (hs : IsConditionable Measure.count s) :
    uniformOn s hs (s ∩ t) = uniformOn s hs t := by
  rw [uniformOn, cond_inter_self hs]

theorem uniformOn_self (hs : IsConditionable Measure.count s) : uniformOn s hs s = 1 := by
  rw [uniformOn, cond_apply_self hs]

theorem uniformOn_eq_one_of (hs : IsConditionable Measure.count s) (ht : s ⊆ t) :
    uniformOn s hs t = 1 := by
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt, ← uniformOn_self hs]
  exact measure_mono ht

theorem uniformOn_of_univ (hs : IsConditionable Measure.count s) : uniformOn s hs Set.univ = 1 :=
  uniformOn_eq_one_of hs s.subset_univ

theorem uniformOn_inter (hs : IsConditionable Measure.count s)
    (hst : IsConditionable Measure.count (s ∩ t)) :
    uniformOn s hs (t ∩ u) = uniformOn (s ∩ t) hst u * uniformOn s hs t := by
  rw [uniformOn, uniformOn, cond_apply hs, cond_apply hs, cond_apply hst,
    mul_comm _ (Measure.count (s ∩ t)), ← mul_assoc, mul_comm _ (Measure.count (s ∩ t)),
    ← mul_assoc, ENNReal.mul_inv_cancel hst.measure_ne_zero hst.measure_ne_top, one_mul, mul_comm,
    Set.inter_assoc]

theorem uniformOn_inter' (hs : IsConditionable Measure.count s)
    (hsu : IsConditionable Measure.count (s ∩ u)) :
    uniformOn s hs (t ∩ u) = uniformOn (s ∩ u) hsu t * uniformOn s hs u := by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs hsu

variable [MeasurableSingletonClass Ω]

lemma uniformOn_apply_finset [DecidableEq Ω] {s t : Finset Ω}
    (hs : IsConditionable Measure.count (s : Set Ω)) :
    uniformOn (s : Set Ω) hs (t : Set Ω) = #(s ∩ t) / #s :=
  uniformOn_apply_finset' hs t.measurableSet

theorem pred_true_of_uniformOn_eq_one (hs : IsConditionable Measure.count s)
    (h : uniformOn s hs t = 1) : s ⊆ t := by
  have hsf := hs.finite_of_count
  rw [uniformOn, cond_apply hs, mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv, Measure.count_apply_finite _ hsf, Measure.count_apply_finite _ (hsf.inter_of_left _),
    Nat.cast_inj] at h
  suffices s ∩ t = s by exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono s.inter_subset_left) h.ge

theorem uniformOn_eq_zero_iff (hs : IsConditionable Measure.count s) :
    uniformOn s hs t = 0 ↔ s ∩ t = ∅ := by
  simp [uniformOn, cond_apply hs, Measure.count_apply_eq_top, Set.not_infinite.2 hs.finite_of_count,
    Measure.count_apply_finite _ (hs.finite_of_count.inter_of_left _)]

theorem uniformOn_union (hs : IsConditionable Measure.count s) (htu : Disjoint t u) :
    uniformOn s hs (t ∪ u) = uniformOn s hs t + uniformOn s hs u := by
  rw [uniformOn, cond_apply hs, cond_apply hs, cond_apply hs, Set.inter_union_distrib_left,
    measure_union, mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.finite_of_count.inter_of_left _).measurableSet]

theorem uniformOn_compl (t : Set Ω) (hs : IsConditionable Measure.count s) :
    uniformOn s hs t + uniformOn s hs tᶜ = 1 := by
  rw [← uniformOn_union hs disjoint_compl_right, Set.union_compl_self, measure_univ]

theorem uniformOn_disjoint_union (hs : IsConditionable Measure.count s)
    (ht : IsConditionable Measure.count t) (hst : Disjoint s t) :
    uniformOn s hs u * uniformOn (s ∪ t) (hs.union ht) s +
        uniformOn t ht u * uniformOn (s ∪ t) (hs.union ht) t =
      uniformOn (s ∪ t) (hs.union ht) u := by
  rw [uniformOn, uniformOn, uniformOn, cond_apply hs, cond_apply ht, cond_apply (hs.union ht),
    cond_apply (hs.union ht), cond_apply (hs.union ht)]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right,
      mul_comm (Measure.count (s ∪ t))⁻¹, mul_comm (Measure.count (s ∪ t))⁻¹, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Measure.count s), mul_comm _ (Measure.count t), ← mul_assoc,
      ← mul_assoc]
  rw [ENNReal.mul_inv_cancel, ENNReal.mul_inv_cancel, one_mul, one_mul, ← add_mul, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts [hst.mono inf_le_left inf_le_left, (ht.finite_of_count.inter_of_left _).measurableSet,
    ht.measure_ne_zero, ht.measure_ne_top, hs.measure_ne_zero, hs.measure_ne_top]

/-- A version of the law of total probability for counting probabilities. -/
theorem uniformOn_add_compl_eq (u t : Set Ω) (hs : IsConditionable Measure.count s)
    (hsu : IsConditionable Measure.count (s ∩ u)) (hsu' : IsConditionable Measure.count (s ∩ uᶜ)) :
    uniformOn (s ∩ u) hsu t * uniformOn s hs u + uniformOn (s ∩ uᶜ) hsu' t * uniformOn s hs uᶜ =
      uniformOn s hs t := by
  have key := uniformOn_disjoint_union (u := t) hsu hsu'
    (disjoint_compl_right.mono inf_le_right inf_le_right)
  have hs' : s ∩ u ∪ s ∩ uᶜ = s := by simp
  have hrw (v : Set Ω) : uniformOn (s ∩ u ∪ s ∩ uᶜ) (hsu.union hsu') v = uniformOn s hs v := by
    simp only [hs']
  rw [hrw, hrw, hrw, uniformOn_inter_self hs, uniformOn_inter_self hs] at key
  rw [← key, mul_comm (uniformOn (s ∩ u) hsu t), mul_comm (uniformOn (s ∩ uᶜ) hsu' t)]

variable {ι : Type*} [Fintype ι]

/-- The uniform measure on a product of sets is the product of the uniform measures. -/
lemma uniformOn_pi [Finite Ω] {f : ι → Set Ω} (hf : ∀ i, (f i).Nonempty) :
    uniformOn (Set.univ.pi f) (.count_of_finite (Set.toFinite _) (Set.univ_pi_nonempty_iff.2 hf)) =
      Measure.pi fun i ↦ uniformOn (f i) (.count_of_finite (Set.toFinite _) (hf i)) := by
  refine (MeasureTheory.Measure.pi_eq fun t ht ↦ ?_).symm
  lift f to ι → Finset Ω using by simp [Set.toFinite]
  lift t to ι → Finset Ω using by simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne_top]

end ProbabilityTheory

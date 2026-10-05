/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. It is defined when `μ` can
be conditioned on `s` (`ProbabilityTheory.IsConditionable μ s`): `s` is null-measurable and has
positive finite measure. The scaling then makes it a probability measure concentrated on `s`.

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `t : Set Ω`, we have `μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Domain

Conditional probability is defined given an event of positive probability (A. N. Kolmogorov,
*Foundations of the Theory of Probability*, Chapter I, §4), and the same formula conditions any
measure on a set of positive finite measure. Null-measurable sets are the events of the completion,
and conditioning on one is conditioning on any measurable set almost everywhere equal to it. For a
set that is not null-measurable the formula still gives a probability measure, but not one
concentrated on the set: for a Bernstein set `B ⊆ [0, 1]`, which together with its complement meets
every uncountable closed set, conditioning Lebesgue measure on `[0, 1] \ B` by this formula gives
`B` probability `1`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t | s] = (μ s)⁻¹ * μ[s | t] * (μ t)`.

## Notation

This file uses the notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t | s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`). Both find the proof that `μ` can be conditioned on `s` with the tactic
`conditionable`, which uses the local hypotheses.

These notations are contained in the scope `ProbabilityTheory`.

## Tags

conditional, conditioned, bayes
-/

@[expose] public section

noncomputable section

open ENNReal MeasureTheory MeasureTheory.Measure SigmaAlgebra Set

variable {Ω Ω' α : Type*} {m : SigmaAlgebra Ω} {m' : SigmaAlgebra Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

/-- The measure `μ` can be conditioned on the set `s`: `s` is null-measurable and has positive
finite measure. -/
@[mk_iff]
structure IsConditionable (μ : Measure Ω) (s : Set Ω) : Prop where
  /-- The conditioning set is null-measurable. -/
  nullMeasurableSet : NullMeasurableSet s μ
  /-- The conditioning set has positive measure. -/
  measure_ne_zero : μ s ≠ 0
  /-- The conditioning set has finite measure. -/
  measure_ne_top : μ s ≠ ∞

lemma IsConditionable.of_measurableSet (hs : MeasurableSet s) (h₀ : μ s ≠ 0) (h : μ s ≠ ∞) :
    IsConditionable μ s :=
  ⟨hs.nullMeasurableSet, h₀, h⟩

lemma IsConditionable.of_isFiniteMeasure [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (h₀ : μ s ≠ 0) : IsConditionable μ s :=
  ⟨hs.nullMeasurableSet, h₀, MeasureTheory.measure_ne_top μ s⟩

/-- A nonzero finite measure can be conditioned on the whole space. -/
lemma IsConditionable.univ [IsFiniteMeasure μ] [NeZero μ] : IsConditionable μ Set.univ :=
  ⟨.univ, measure_univ_ne_zero.2 (NeZero.ne μ), MeasureTheory.measure_ne_top μ Set.univ⟩

/-- The measurable hull of a conditionable set is conditionable. -/
lemma IsConditionable.toMeasurable (hs : IsConditionable μ s) :
    IsConditionable μ (toMeasurable μ s) :=
  ⟨(measurableSet_toMeasurable μ s).nullMeasurableSet,
    (measure_toMeasurable s).symm ▸ hs.measure_ne_zero,
    (measure_toMeasurable s).symm ▸ hs.measure_ne_top⟩

/-- The default discharger for `IsConditionable μ s`: a hypothesis, the instance `univ` for a
nonzero finite measure, or the three conditions from hypotheses, where a measurable set is
null-measurable and a finite measure is finite on `s`. -/
macro (name := conditionable) "conditionable" : tactic => `(tactic| first
  | assumption
  | exact ProbabilityTheory.IsConditionable.univ
  | exact ProbabilityTheory.IsConditionable.mk (by assumption) (by assumption) (by assumption)
  | exact ProbabilityTheory.IsConditionable.of_measurableSet (by assumption) (by assumption)
      (by assumption)
  | exact ProbabilityTheory.IsConditionable.mk (by assumption) (by assumption)
      (MeasureTheory.measure_ne_top _ _)
  | exact ProbabilityTheory.IsConditionable.of_isFiniteMeasure (by assumption) (by assumption)
  | fail "conditioning on this set needs a proof `IsConditionable μ s` that it is null-measurable \
      and has positive finite measure")

variable (μ) in
/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. It is defined when `μ` can be conditioned on `s`, which `hs` states:
`s` is null-measurable and has positive finite measure. -/
@[wikidata Q327069, nolint unusedArguments]
def cond (s : Set Ω) (_hs : IsConditionable μ s := by conditionable) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s

@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `((ProbabilityTheory.cond $μ $s : MeasureTheory.Measure _) $t)

/-!
We can't use `notation` or `notation3` as it does not support `noWs`, and so we have to write
our own delaborators.
-/

section delaborators
open Lean PrettyPrinter.Delaborator SubExpr

/-- Unexpander for `μ[|s]` notation. -/
@[app_unexpander ProbabilityTheory.cond]
meta def condUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $μ $s $_) => `($μ[|$s])
  | _ => throw ()

/-- info: fun hs ↦ μ[|s] : IsConditionable μ s → Measure Ω -/
#guard_msgs in
#check fun hs : IsConditionable μ s ↦ μ[|s]

/-- Delaborator for `μ[t | s]` notation. -/
@[app_delab DFunLike.coe]
meta def delabCondApplied : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 6 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``DFunLike.coe 6
    guard <| (e.getArg!' 4).isAppOf' ``ProbabilityTheory.cond
    let t ← withAppArg delab
    withAppFn <| withAppArg do
      let μ ← withNaryArg 2 delab
      let s ← withNaryArg 3 delab
      `($μ[$t|$s])

/-- info: fun hs ↦ μ[t | s] : IsConditionable μ s → ℝ≥0∞ -/
#guard_msgs in
#check fun hs : IsConditionable μ s ↦ μ[t | s]
/-- info: fun hs ↦ μ[t | s] : IsConditionable μ s → ℝ≥0∞ -/
#guard_msgs in
#check fun hs : IsConditionable μ s ↦ μ[|s] t

end delaborators

/-- The conditional probability measure of measure `μ` on `{ω | X ω ∈ s}`.

It is `μ` restricted to `{ω | X ω ∈ s}` and scaled by the inverse of `μ {ω | X ω ∈ s}`
(to make it a probability measure): `(μ {ω | X ω ∈ s})⁻¹ • μ.restrict {ω | X ω ∈ s}`. -/
scoped macro:max μ:term noWs "[|" X:term " in " s:term "]" : term => `($μ[|$X ⁻¹' $s])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " in " t:term "]" : term =>
  `($μ[$s | $X ⁻¹' $t])

/-- The conditional probability measure of measure `μ` on `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[|" X:term " ← " x:term "]" : term => `($μ[|$X in {$x:term}])

/-- The conditional probability measure of measure `μ` on set `{ω | X ω = x}`.

It is `μ` restricted to `{ω | X ω = x}` and scaled by the inverse of `μ {ω | X ω = x}`
(to make it a probability measure): `(μ {ω | X ω = x})⁻¹ • μ.restrict {ω | X ω = x}`. -/
scoped macro:max μ:term noWs "[" s:term " | " X:term " ← " x:term "]" : term =>
  `($μ[$s | $X in {$x:term}])

/-- The conditional probability measure is a probability measure. -/
instance isProbabilityMeasure_cond (hs : IsConditionable μ s) : IsProbabilityMeasure μ[|s] :=
  ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hs.measure_ne_zero hs.measure_ne_top⟩

variable (μ) in
theorem cond_toMeasurable_eq (hs : IsConditionable μ s) :
    cond μ (toMeasurable μ s) hs.toMeasurable = μ[|s] := by
  unfold cond
  simp [Measure.restrict_toMeasurable hs.measure_ne_top]

lemma cond_absolutelyContinuous (hs : IsConditionable μ s) : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous

lemma absolutelyContinuous_cond_univ (hu : IsConditionable μ univ) : μ ≪ μ[|univ] := by
  rw [cond, restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [hu.measure_ne_top]

lemma ae_cond_of_forall_mem (hs : IsConditionable μ s) {p : Ω → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ[|s], p x :=
  ae_smul_measure ((ae_restrict_mem₀ hs.nullMeasurableSet).mono h) _

lemma ae_cond_mem (hs : IsConditionable μ s) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_cond_of_forall_mem hs fun _ ↦ id

section Bayes

variable (μ) in
@[simp] lemma cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
theorem cond_apply (hs : IsConditionable μ s) (t : Set Ω) : μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply₀' hs.nullMeasurableSet, Set.inter_comm,
    smul_eq_mul]

@[simp] lemma cond_apply_self (hs : IsConditionable μ s) : μ[s | s] = 1 := by
  rw [cond_apply hs, Set.inter_self, ENNReal.inv_mul_cancel hs.measure_ne_zero hs.measure_ne_top]

theorem cond_inter_self (hs : IsConditionable μ s) (t : Set Ω) : μ[s ∩ t | s] = μ[t | s] := by
  rw [cond_apply hs, ← Set.inter_assoc, Set.inter_self, ← cond_apply hs]

theorem inter_pos_of_cond_ne_zero (hs : IsConditionable μ s) (hcst : μ[t | s] ≠ 0) :
    0 < μ (s ∩ t) := by
  rw [cond_apply hs] at hcst
  exact pos_iff_ne_zero.mpr (right_ne_zero_of_mul hcst)

lemma cond_pos_of_inter_ne_zero (hs : IsConditionable μ s) (hci : μ (s ∩ t) ≠ 0) :
    0 < μ[t | s] := by
  rw [cond_apply hs]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hs.measure_ne_top) hci

/-- If `μ` can be conditioned on `s` and `μ[|s]` on `t`, then `μ` can be conditioned on
`s ∩ t`. -/
lemma IsConditionable.inter_of_cond (hs : IsConditionable μ s) (ht : IsConditionable μ[|s] t) :
    IsConditionable μ (s ∩ t) := by
  have hc : (μ s)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hs.measure_ne_top
  refine ⟨?_, ?_, measure_ne_top_of_subset inter_subset_left hs.measure_ne_top⟩
  · have := ht.nullMeasurableSet
    rw [cond, nullMeasurableSet_smul_measure_iff hc,
      nullMeasurableSet_restrict hs.nullMeasurableSet, inter_comm] at this
    exact this
  · have := ht.measure_ne_zero
    rw [cond_apply hs] at this
    exact right_ne_zero_of_mul this

/-- If `μ` can be conditioned on `s` and on `t`, then it can be conditioned on `s ∪ t`. -/
lemma IsConditionable.union (hs : IsConditionable μ s) (ht : IsConditionable μ t) :
    IsConditionable μ (s ∪ t) :=
  ⟨hs.nullMeasurableSet.union ht.nullMeasurableSet,
    (measure_pos_of_superset subset_union_left hs.measure_ne_zero).ne',
    measure_union_ne_top hs.measure_ne_top ht.measure_ne_top⟩

/-- Conditioning first on `s` and then on `t` results in the same measure as conditioning
on `s ∩ t`. -/
theorem cond_cond_eq_cond_inter (hs : IsConditionable μ s) (ht : IsConditionable μ[|s] t) :
    μ[|s][|t] = cond μ (s ∩ t) (hs.inter_of_cond ht) := by
  have hst := hs.inter_of_cond ht
  ext u
  rw [cond_apply ht, cond_apply hs, cond_apply hs, cond_apply hst, ← Set.inter_assoc,
    ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hs.measure_ne_top))
      (Or.inl (ENNReal.inv_ne_top.2 hs.measure_ne_zero)), inv_inv, mul_comm (μ s), mul_assoc,
    ← mul_assoc (μ s), ENNReal.mul_inv_cancel hs.measure_ne_zero hs.measure_ne_top, one_mul]

theorem cond_mul_eq_inter (hs : IsConditionable μ s) (t : Set Ω) : μ[t | s] * μ s = μ (s ∩ t) := by
  rw [cond_apply hs, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hs.measure_ne_zero
    hs.measure_ne_top, one_mul]

/-- A version of the law of total probability. -/
theorem cond_add_cond_compl_eq (hs : IsConditionable μ s) (hsc : IsConditionable μ sᶜ)
    (t : Set Ω) : μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter hs, cond_mul_eq_inter hsc, Set.inter_comm _ t, Set.inter_comm _ t,
    ← Set.sdiff_eq]
  exact measure_inter_add_sdiff₀ t hs.nullMeasurableSet

/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul (hs : IsConditionable μ s) (ht : IsConditionable μ t) :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t := by
  rw [mul_assoc, cond_mul_eq_inter ht s, Set.inter_comm, cond_apply hs]

end Bayes

/-- The pullback of a conditionable set along a measurable embedding whose range has full
measure is conditionable for the pulled-back measure. -/
lemma IsConditionable.comap {i : Ω' → Ω} (hi : MeasurableEmbedding i)
    (hi' : ∀ᵐ ω ∂μ, ω ∈ range i) (hs : IsConditionable μ s) (hms : MeasurableSet s) :
    IsConditionable (Measure.comap i μ) (i ⁻¹' s) := by
  change μ (range i)ᶜ = 0 at hi'
  have h : Measure.comap i μ (i ⁻¹' s) = μ s := by
    rw [comap_apply _ hi.injective hi.measurableSet_image' _ (hi.measurable hms),
      image_preimage_eq_inter_range, measure_inter_conull hi']
  exact ⟨MeasurableSet.nullMeasurableSet (hi.measurable hms), h ▸ hs.measure_ne_zero,
    h ▸ hs.measure_ne_top⟩

lemma comap_cond {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ ω ∂μ, ω ∈ range i)
    (hs : IsConditionable μ s) (hms : MeasurableSet s) :
    Measure.comap i μ[|s] = cond (Measure.comap i μ) (i ⁻¹' s) (hs.comap hi hi' hms) := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply (hs.comap hi hi' hms), comap_apply, cond_apply hs, comap_apply, comap_apply,
    image_inter, image_preimage_eq_inter_range, inter_right_comm, measure_inter_conull hi',
    measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hms
  | exact ht
  | exact hi.measurable hms
  | exact m'.inter_mem (hi.measurable hms) ht

variable [Fintype α] [SigmaAlgebra α] [DiscreteSigmaAlgebra α]

/-- The **law of total probability** for a random variable taking finitely many values: a measure
`μ` is the combination of its conditional measures `μ[|X ← x]` on the fibers of positive measure of
a random variable `X` valued in a fintype. -/
lemma sum_meas_smul_cond_fiber {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x : {x // μ (X ⁻¹' {x}) ≠ 0}, μ (X ⁻¹' {x.1}) •
      cond μ (X ⁻¹' {x.1}) (.of_isFiniteMeasure (hX MeasurableSet.of_discrete) x.2) = μ := by
  classical
  ext E hE
  calc
    _ = ∑ x : {x // μ (X ⁻¹' {x}) ≠ 0}, μ (X ⁻¹' {x.1} ∩ E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun x _ ↦ by rw [mul_comm, cond_mul_eq_inter]
    _ = ∑ x, μ (X ⁻¹' {x} ∩ E) := by
      rw [← Finset.sum_subtype (Finset.univ.filter fun x ↦ μ (X ⁻¹' {x}) ≠ 0) (by simp)
        (fun x ↦ μ (X ⁻¹' {x} ∩ E))]
      exact Finset.sum_filter_of_ne fun x _ hx h ↦ hx (measure_mono_null inter_subset_left h)
    _ = _ := by
      have : ⋃ x ∈ Finset.univ, X ⁻¹' {x} ∩ E = E := by ext; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦
        m.inter_mem (hX MeasurableSet.of_discrete) hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory

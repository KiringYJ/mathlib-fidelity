/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Conditional expectation of indicator functions

This file proves that conditional expectations are local for indicators: on a set `s` of the
conditioning σ-algebra `m`, the indicator of a conditional expectation of `f` is one of the
indicator of `f`. With the locality for the restricted measure, `MeasureTheory.IsCondExp.restrict`,
two σ-algebras that agree on `s` have conditional expectations that agree almost everywhere on
`s`.

## Main results

* `MeasureTheory.IsCondExp.indicator`: if `g` is a conditional expectation of `f` given `m` and
  `s ∈ m`, then `s.indicator g` is one of `s.indicator f`.
* `MeasureTheory.IsCondExp.ae_eq_restrict_of_sigmaAlgebra_eq_on`: conditional expectations of an
  integrable function given two sub-σ-algebras that agree on `s` agree almost everywhere on `s`.
* `MeasureTheory.IsCondExp.indicator_iUnion`: for a function integrable on the union, the sum of
  conditional expectations of the indicators of countably many pairwise disjoint null-measurable
  sets, which need not be `m`-measurable, is one of the indicator of their union.
  `MeasureTheory.IsCondExp.indicator_sdiff` and `MeasureTheory.IsCondExp.indicator_compl` are the
  companions for differences and complements; for the constant `1` they are the elementary
  properties of conditional probabilities.
* `MeasureTheory.condExp_indicator_empty`, `MeasureTheory.condExp_indicator_univ_one`,
  `MeasureTheory.condExp_indicator_compl_one`: the conditional probabilities of `∅`, of the whole
  space, and of a complement, as almost everywhere classes.

-/

public section

noncomputable section

open MeasureTheory.Lp Filter

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E : Type*} {m m₂ m0 : SigmaAlgebra α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {f g g' : α → E} {s t : Set α}

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The indicator of an almost everywhere `m`-strongly measurable function on a set of `m` is
almost everywhere `m`-strongly measurable, for a measure on another σ-algebra. -/
private theorem aestronglyMeasurable_indicator {g : α → E} (hg : AEStronglyMeasurable[m] g μ)
    (hs : s ∈ m) : AEStronglyMeasurable[m] (s.indicator g) μ :=
  ⟨s.indicator (hg.mk g), hg.stronglyMeasurable_mk.indicator hs, by
    filter_upwards [hg.ae_eq_mk] with x hx
    by_cases hxs : x ∈ s <;> simp [hxs, hx]⟩

namespace IsCondExp

/-- **Locality**: if `g` is a conditional expectation of `f` given a sub-σ-algebra `m` and `s ∈ m`,
then `s.indicator g` is a conditional expectation of `s.indicator f`. -/
theorem indicator (hm : m ≤ m0) (h : IsCondExp m μ f g) (hs : s ∈ m) :
    IsCondExp m μ (s.indicator f) (s.indicator g) where
  aestronglyMeasurable := aestronglyMeasurable_indicator h.aestronglyMeasurable hs
  integrableOn t ht hf := by
    rw [IntegrableOn, integrable_indicator_iff (hm hs), IntegrableOn,
      Measure.restrict_restrict (hm hs)] at hf ⊢
    exact h.integrableOn _ (m.inter_mem hs ht) hf
  setIntegral_eq t ht hf := by
    rw [IntegrableOn, integrable_indicator_iff (hm hs), IntegrableOn,
      Measure.restrict_restrict (hm hs)] at hf
    rw [integral_indicator (hm hs), integral_indicator (hm hs), Measure.restrict_restrict (hm hs),
      h.setIntegral_eq _ (m.inter_mem hs ht) hf]

/-- If the restrictions to a set `s ∈ m` of a sub-σ-algebra `m` and of a σ-algebra `m₂` agree, then
the indicator of a conditional expectation of `f` given `m` is a conditional expectation of the
indicator of `f` given `m₂`. -/
theorem indicator_of_sigmaAlgebra_eq_on (hm : m ≤ m0) (h : IsCondExp m μ f g) (hs_m : s ∈ m)
    (hs : ∀ t, s ∩ t ∈ m ↔ s ∩ t ∈ m₂) :
    IsCondExp m₂ μ (s.indicator f) (s.indicator g) := by
  have hs_m₂ : s ∈ m₂ := by simpa only [Set.inter_univ] using (hs Set.univ).mp (by simpa using hs_m)
  refine ⟨(aestronglyMeasurable_indicator h.aestronglyMeasurable hs_m).of_sigmaAlgebra_le_on hm hs_m
      (fun t ↦ (hs t).mp) (indicator_ae_eq_restrict_compl (hm hs_m)), fun t ht hf ↦ ?_,
    fun t ht hf ↦ ?_⟩
  · have hst : s ∩ t ∈ m := (hs t).mpr (m₂.inter_mem hs_m₂ ht)
    rw [IntegrableOn, integrable_indicator_iff (hm hs_m), IntegrableOn,
      Measure.restrict_restrict (hm hs_m)] at hf ⊢
    exact h.integrableOn _ hst hf
  · have hst : s ∩ t ∈ m := (hs t).mpr (m₂.inter_mem hs_m₂ ht)
    rw [IntegrableOn, integrable_indicator_iff (hm hs_m), IntegrableOn,
      Measure.restrict_restrict (hm hs_m)] at hf
    rw [integral_indicator (hm hs_m), integral_indicator (hm hs_m),
      Measure.restrict_restrict (hm hs_m), h.setIntegral_eq _ hst hf]

/-- Conditional expectations of an integrable function given two sub-σ-algebras `m` and `m₂` whose
restrictions to a set `s ∈ m` agree are almost everywhere equal on `s`. -/
theorem ae_eq_restrict_of_sigmaAlgebra_eq_on (hm : m ≤ m0) (hm₂ : m₂ ≤ m0) (hs_m : s ∈ m)
    (hs : ∀ t, s ∩ t ∈ m ↔ s ∩ t ∈ m₂) (hf : Integrable f μ) (h : IsCondExp m μ f g)
    (h₂ : IsCondExp m₂ μ f g') : g =ᵐ[μ.restrict s] g' := by
  have hs_m₂ : s ∈ m₂ := by simpa only [Set.inter_univ] using (hs Set.univ).mp (by simpa using hs_m)
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm hs_m)]
  exact (h.indicator_of_sigmaAlgebra_eq_on hm hs_m hs).ae_eq hm₂ (hf.indicator (hm hs_m))
    (h₂.indicator hm₂ hs_m₂)

end IsCondExp

/-! ### Indicators of null-measurable sets

For a fixed function, conditional expectations of its indicators vanish for the empty set, depend
on the set only up to null sets, and are additive on differences, complements, and countable
disjoint unions of null-measurable sets, which need not be `m`-measurable. For the constant `1`,
these are the conditional probabilities. -/

theorem isCondExp_indicator_empty : IsCondExp m μ ((∅ : Set α).indicator f) 0 := by
  simpa only [Set.indicator_empty'] using IsCondExp.zero

theorem isCondExp_indicator_univ (c : E) :
    IsCondExp m μ (Set.univ.indicator fun _ ↦ c) fun _ ↦ c := by
  simpa only [Set.indicator_univ] using isCondExp_const c

namespace IsCondExp

/-- Conditional expectations of the indicators of null-measurable sets `t ⊆ s`, for a function
integrable on `s`, give one of the indicator of `s \ t` by subtraction. -/
theorem indicator_sdiff (hs : IsCondExp m μ (s.indicator f) g)
    (ht : IsCondExp m μ (t.indicator f) g') (hs_null : NullMeasurableSet s μ)
    (ht_null : NullMeasurableSet t μ) (hts : t ⊆ s) (hf : IntegrableOn f s μ) :
    IsCondExp m μ ((s \ t).indicator f) (g - g') := by
  rw [Set.indicator_sdiff hts]
  exact hs.sub ht (hf.integrable_indicator₀ hs_null)
    ((hf.mono_set hts).integrable_indicator₀ ht_null)

/-- Conditional expectations of an integrable function and of its indicator on a null-measurable
set `s` give one of its indicator on `sᶜ` by subtraction. -/
theorem indicator_compl (h : IsCondExp m μ f g) (hs : IsCondExp m μ (s.indicator f) g')
    (hs_null : NullMeasurableSet s μ) (hf : Integrable f μ) :
    IsCondExp m μ (sᶜ.indicator f) (g - g') := by
  rw [Set.indicator_compl]
  exact h.sub hs hf (hf.integrableOn.integrable_indicator₀ hs_null)

/-- For a finite measure, `1` minus a conditional probability of a null-measurable set `s` is a
conditional probability of its complement. -/
theorem indicator_compl_one [IsFiniteMeasure μ] {g : α → ℝ}
    (hs : IsCondExp m μ (s.indicator fun _ ↦ (1 : ℝ)) g) (hs_null : NullMeasurableSet s μ) :
    IsCondExp m μ (sᶜ.indicator fun _ ↦ (1 : ℝ)) (1 - g) :=
  (isCondExp_const (1 : ℝ)).indicator_compl hs hs_null (integrable_const 1)

open Function in
/-- The sum of conditional expectations of the indicators of countably many pairwise disjoint
null-measurable sets, for a function integrable on their union, is a conditional expectation of the
indicator of the union, given a σ-finite sub-σ-algebra. -/
theorem indicator_iUnion {ι : Type*} [Countable ι] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {s : ι → Set α} {g : ι → α → E} (h : ∀ i, IsCondExp m μ ((s i).indicator f) (g i))
    (hs : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (Disjoint on s))
    (hf : IntegrableOn f (⋃ i, s i) μ) :
    IsCondExp m μ ((⋃ i, s i).indicator f) fun a ↦ ∑' i, g i a := by
  rw [indicator_iUnion_of_pairwise_disjoint s hd f]
  refine IsCondExp.tsum hm h
    (fun i ↦ ((hf.mono_set (Set.subset_iUnion s i)).integrable_indicator₀ (hs i)).1) ?_
  have h_int (i : ι) : ∫⁻ a, ‖(s i).indicator f a‖ₑ ∂μ = ∫⁻ a in s i, ‖f a‖ₑ ∂μ := by
    simp_rw [enorm_indicator_eq_indicator_enorm]
    exact lintegral_indicator₀ (hs i) _
  simp_rw [h_int]
  rw [← lintegral_iUnion₀ hs (hd.mono fun i j h ↦ h.aedisjoint)]
  exact hf.2.ne

end IsCondExp

/-! ### Conditional probabilities as almost everywhere classes -/

/-- The conditional expectation of the indicator of `∅` is `0`. -/
theorem condExp_indicator_empty (h : HasUniqueCondExp m μ ((∅ : Set α).indicator f)) :
    condExp m μ ((∅ : Set α).indicator f) h = 0 := by
  rw [isCondExp_indicator_empty.condExp_eq h, Germ.coe_zero]

/-- The conditional probability of the whole space is `1`. -/
theorem condExp_indicator_univ_one (h : HasUniqueCondExp m μ (Set.univ.indicator fun _ ↦ (1 : ℝ))) :
    condExp m μ (Set.univ.indicator fun _ ↦ (1 : ℝ)) h = 1 :=
  (isCondExp_indicator_univ (1 : ℝ)).condExp_eq h

/-- For a finite measure, the conditional probability of the complement of a null-measurable set is
`1` minus that of the set. -/
theorem condExp_indicator_compl_one [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (h : HasUniqueCondExp m μ (s.indicator fun _ ↦ (1 : ℝ)))
    (h' : HasUniqueCondExp m μ (sᶜ.indicator fun _ ↦ (1 : ℝ))) :
    condExp m μ (sᶜ.indicator fun _ ↦ (1 : ℝ)) h' =
      1 - condExp m μ (s.indicator fun _ ↦ (1 : ℝ)) h := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  rw [hg.condExp_eq h, (hg.indicator_compl_one hs).condExp_eq h', Germ.coe_sub, Germ.coe_one]

/-- Almost everywhere equal sets have the same conditional expectations of indicators. -/
theorem condExp_indicator_congr_ae_set (hst : s =ᵐ[μ] t) (h : HasUniqueCondExp m μ (s.indicator f))
    (h' : HasUniqueCondExp m μ (t.indicator f)) :
    condExp m μ (s.indicator f) h = condExp m μ (t.indicator f) h' :=
  condExp_congr_ae h (indicator_ae_eq_of_ae_eq_set hst)

end MeasureTheory

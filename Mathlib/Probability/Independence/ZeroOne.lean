/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Kolmogorov's 0-1 law

Let `s : ι → SigmaAlgebra Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s atTop` has probability 0 or 1.

## Main statements

* `measure_zero_or_one_of_measurableSet_limsup_atTop`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s atTop` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.
* `MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_measurableSet_limsup_atTop`: Kolmogorov's 0-1 law
  given a sub-σ-algebra `m`. For a sequence of σ-algebras `s` that are conditionally independent
  given `m`, every version of the conditional probability of a set of `limsup s atTop` is `0` or `1`
  almost everywhere.
* `limsup_atTop_le_eventuallySigmaAlgebra_of_iCondIndep`: equivalently
  (`MeasureTheory.IsCondExp.ae_eq_zero_or_one_iff`), each set of `limsup s atTop` is almost
  everywhere equal to a set of `m`.
-/

public section

open MeasureTheory SigmaAlgebra

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {α Ω ι : Type*} {_mα : SigmaAlgebra α} {s : ι → SigmaAlgebra Ω}
  {m m0 : SigmaAlgebra Ω} {κ : Kernel α Ω} {μα : Measure α} {μ : Measure Ω}

theorem Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : Kernel.IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 ∨ κ a t = ∞ := by
  specialize h_indep t t (SigmaAlgebra.mem_generateFrom (Set.mem_singleton t))
    (SigmaAlgebra.mem_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (t ∩ t)), Set.inter_self, ENNReal.mul_left_inj h0 h_top] at ha
  exact Or.inr (Or.inl ha.symm)

theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep

theorem Kernel.measure_eq_zero_or_one_of_indepSet_self' (h : ∀ᵐ a ∂μα, IsFiniteMeasure (κ a))
    {t : Set Ω} (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

theorem Kernel.measure_eq_zero_or_one_of_indepSet_self [h : ∀ a, IsFiniteMeasure (κ a)] {t : Set Ω}
    (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep

lemma Kernel.measure_eq_zero_or_one_of_indep_self [h : ∀ a, IsFiniteMeasure (κ a)]
    (hm : Indep m m κ μα) {t : Set Ω} (ht : t ∈ m) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    (indep_of_indep_of_le hm (generateFrom_singleton_le ht) (generateFrom_singleton_le ht))

theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep

lemma measure_eq_zero_or_one_of_indep_self [IsFiniteMeasure μ] (hm : Indep m m μ)
    {t : Set Ω} (ht : t ∈ m) :
    μ t = 0 ∨ μ t = 1 := by
  simpa using Kernel.measure_eq_zero_or_one_of_indep_self hm ht

/-- Every version `g` of the conditional probability of a set that is conditionally independent of
itself given `m` is `0` or `1` almost everywhere: by the conditional independence, `g * g` is also a
version, so `g = g * g` almost everywhere. -/
theorem _root_.MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_condIndepSet_self
    (hm : m ≤ m0) [IsFiniteMeasure μ] {t : Set Ω} (h_indep : CondIndepSet m hm t t μ)
    {g : Ω → ℝ} (hg : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) g) :
    ∀ᵐ ω ∂μ, g ω = 0 ∨ g ω = 1 := by
  have ht := h_indep.nullMeasurableSet_left
  have h_mul := (condIndepSet_iff m hm t t μ ht ht).1 h_indep hg hg
  rw [Set.inter_self] at h_mul
  filter_upwards [hg.ae_eq hm ((integrable_const 1).indicator₀ ht) h_mul] with ω hω
  rw [Pi.mul_apply] at hω
  have h0 : g ω * (g ω - 1) = 0 := by
    rw [mul_sub, mul_one, ← hω, sub_self]
  rcases mul_eq_zero.1 h0 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

/-- A version `g` of the conditional probability of a null-measurable set `t` of finite measure
given `m` is `0` or `1` almost everywhere exactly when `t` is almost everywhere equal to a set of
`m`. If `g` is `0` or `1` almost everywhere, it is almost everywhere the indicator of the set
`s ∈ m` on which an `m`-strongly measurable modification of `g` is `1`, so `μ s` is finite; then
`μ (t ∩ B) = μ (s ∩ B)` for every `B ∈ m`, and `B = sᶜ` and `B = s` give `t =ᵐ[μ] s`. Conversely,
if `t =ᵐ[μ] s` for some `s ∈ m`, the indicator of `s` is a version, and versions agree almost
everywhere. For a finite measure, `finiteness` proves `μ t ≠ ∞`. -/
theorem _root_.MeasureTheory.IsCondExp.ae_eq_zero_or_one_iff (hm : m ≤ m0) {t : Set Ω}
    (ht : NullMeasurableSet t μ) {g : Ω → ℝ} (hg : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) g)
    (hμt : μ t ≠ ∞ := by finiteness) :
    (∀ᵐ ω ∂μ, g ω = 0 ∨ g ω = 1) ↔ t ∈ eventuallySigmaAlgebra m (ae μ) := by
  have hf : Integrable (t.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrableOn_const hμt).integrable_indicator₀ ht
  have hμ_inter (B : Set Ω) : μ (t ∩ B) ≠ ∞ := measure_ne_top_of_subset Set.inter_subset_left hμt
  constructor
  · intro h01
    obtain ⟨g', hg', hgg'⟩ := hg.aestronglyMeasurable
    let s : Set Ω := {ω | g' ω = 1}
    have hs : s ∈ m := hg'.measurable (measurableSet_singleton 1)
    have hs' : MeasurableSet s := measurableSet_iff_mem.2 (hm hs)
    have hc : g =ᵐ[μ] s.indicator fun _ ↦ (1 : ℝ) := by
      filter_upwards [h01, hgg'] with ω hω hω'
      by_cases h1 : g' ω = 1
      · simp [s, h1, hω']
      · simp [s, h1, hω.resolve_right fun h ↦ h1 (hω'.symm.trans h)]
    have hμs : μ s ≠ ∞ := by
      have h_int : IntegrableOn (fun _ ↦ (1 : ℝ)) s μ :=
        (integrable_indicator_iff hs').1 ((hg.integrable hf).congr hc)
      exact (by simpa using h_int : μ s < ∞).ne
    have h_meas {B : Set Ω} (hB : B ∈ m) : μ.real (t ∩ B) = μ.real (s ∩ B) := by
      have hB' : MeasurableSet B := measurableSet_iff_mem.2 (hm hB)
      have h := hg.setIntegral_eq B hB hf.integrableOn
      rw [setIntegral_congr_ae hB' (hc.mono fun ω hω _ ↦ hω), setIntegral_indicator hs',
        integral_indicator₀ (ht.mono Measure.restrict_le_self), setIntegral_const,
        setIntegral_const, measureReal_restrict_apply' hB'] at h
      simpa [Set.inter_comm] using h.symm
    change ∃ s ∈ m, t =ᵐ[μ] s
    refine ⟨s, hs, ae_eq_set.2 ⟨?_, ?_⟩⟩
    · have h := h_meas (m.compl_mem hs)
      rw [Set.inter_compl_self, measureReal_empty, measureReal_eq_zero_iff (hμ_inter _)] at h
      exact h
    · have h := h_meas hs
      rw [Set.inter_self, measureReal_def, measureReal_def,
        ENNReal.toReal_eq_toReal_iff' (hμ_inter s) hμs] at h
      rw [← Set.sdiff_inter_self_eq_sdiff, measure_sdiff Set.inter_subset_right
        (ht.inter hs'.nullMeasurableSet) (hμ_inter s), h, tsub_self]
  · rintro ⟨s, hs, hts⟩
    have hs_ver : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) (s.indicator fun _ ↦ (1 : ℝ)) :=
      (isCondExp_self (stronglyMeasurable_const.indicator hs).aestronglyMeasurable).congr_left
        (indicator_ae_eq_of_ae_eq_set hts).symm
    filter_upwards [hg.ae_eq hm hf hs_ver] with ω hω
    by_cases hω' : ω ∈ s <;> simp [hω, hω']

/-- A σ-algebra is conditionally independent of itself given `m'` exactly when each of its sets is
almost everywhere equal to a set of `m'`, that is, when it is contained in
`eventuallySigmaAlgebra m' (ae μ)`; sufficiency is `condIndep_of_le_eventuallySigmaAlgebra_left`.
Conversely, if it is conditionally independent of itself, every version of the conditional
probability of each of its sets is `0` or `1` almost everywhere
(`MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_condIndepSet_self`), hence each of its sets is
almost everywhere equal to a set of `m'` (`MeasureTheory.IsCondExp.ae_eq_zero_or_one_iff`). -/
theorem condIndep_self_iff {m' m₁ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ}
    {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₁ hm' μ ↔ m₁ ≤ eventuallySigmaAlgebra m' (ae μ) := by
  refine ⟨fun h t ht ↦ ?_, fun h ↦ condIndep_of_le_eventuallySigmaAlgebra_left h
    (h.trans (eventuallySigmaAlgebra_mono hm'))⟩
  have ht' := h.nullMeasurableSet_left t ht
  obtain ⟨g, -, hg⟩ :=
    exists_stronglyMeasurable_isCondExp hm' ((integrable_const (1 : ℝ)).indicator₀ ht')
  exact (hg.ae_eq_zero_or_one_iff hm' ht').1
    (hg.ae_eq_zero_or_one_of_condIndepSet_self hm' (h.condIndepSet_of_measurableSet ht ht))

open Filter

theorem Kernel.indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) κ μα :=
  indep_iSup_of_disjoint h_le h_indep disjoint_compl_right

theorem indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  Kernel.indep_biSup_compl h_le h_indep t

theorem condIndep_biSup_compl (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) (t : Set ι) :
    CondIndep m (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) hm μ :=
  condIndep_iSup_of_disjoint h_indep disjoint_compl_right

section Abstract

variable {β : Type*} {p : Set ι → Prop} {f : Filter ι} {ns : β → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/

theorem Kernel.indep_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) κ μα := by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

theorem indep_biSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht

theorem condIndep_biSup_limsup (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι} (ht : p t) :
    CondIndep m (⨆ n ∈ t, s n) (limsup s f) hm μ := by
  refine condIndep_of_condIndep_of_le_right (condIndep_biSup_compl hm h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

theorem Kernel.indep_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) κ μα := by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply indep_iSup_of_directed_le
  · exact fun a => indep_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine ⟨c, ?_, ?_⟩ <;> refine iSup_mono fun n => iSup_mono' fun hn => ⟨?_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn

theorem indep_iSup_directed_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

theorem condIndep_iSup_directed_limsup (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns)
    (hnsp : ∀ a, p (ns a)) :
    CondIndep m (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) hm μ := by
  refine condIndep_iSup_of_directed_le (fun a ↦ condIndep_biSup_limsup hm h_indep hf (hnsp a))
    (fun t ht ↦ h_indep.nullMeasurableSet_iSup ((limsup_le_iSup : limsup s f ≤ ⨆ n, s n) ht)) ?_
  intro a b
  obtain ⟨c, hc⟩ := hns a b
  refine ⟨c, ?_, ?_⟩ <;> refine iSup_mono fun n ↦ iSup_mono' fun hn ↦ ⟨?_, le_rfl⟩
  · exact hc.1 hn
  · exact hc.2 hn

theorem Kernel.indep_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) κ μα := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  have : Nonempty (∃ i : β, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]

theorem indep_iSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

theorem condIndep_iSup_limsup (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (⨆ n, s n) (limsup s f) hm μ := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact condIndep_iSup_directed_limsup hm h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n ↦ ?_
  have h : ⨆ (i : β) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  have : Nonempty (∃ i : β, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]

theorem Kernel.indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) κ μα :=
  indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

theorem indep_limsup_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

theorem condIndep_limsup_self (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (limsup s f) (limsup s f) hm μ :=
  condIndep_of_condIndep_of_le_left (condIndep_iSup_limsup hm h_indep hf hns hnsp hns_univ)
    limsup_le_iSup

theorem Kernel.measure_zero_or_one_of_measurableSet_limsup (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : t ∈ limsup s f) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

theorem measure_zero_or_one_of_measurableSet_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : t ∈ limsup s f) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail

/-- **Kolmogorov's 0-1 law**, conditional version for the σ-algebra `limsup s f`: every version of
the conditional probability of one of its sets is `0` or `1` almost everywhere, for a sequence of
sub-σ-algebras `s` that are conditionally independent given `m`. -/
theorem _root_.MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_measurableSet_limsup (hm : m ≤ m0)
    [IsFiniteMeasure μ] (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : t ∈ limsup s f) {g : Ω → ℝ}
    (hg : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) g) :
    ∀ᵐ ω ∂μ, g ω = 0 ∨ g ω = 1 :=
  hg.ae_eq_zero_or_one_of_condIndepSet_self hm
    ((condIndep_limsup_self hm h_indep hf hns hnsp hns_univ).condIndepSet_of_measurableSet
      ht_tail ht_tail)

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

theorem Kernel.indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atTop) (limsup s atTop) κ μα := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, i < c from lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep

theorem condIndep_limsup_atTop_self (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atTop) (limsup s atTop) hm μ := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i ↦ bddAbove_Iic
  refine condIndep_limsup_self hm h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine ⟨b, fun c hc hct ↦ ?_⟩
    suffices ∀ i ∈ t, i < c from lt_irrefl c (this c hct)
    exact fun i hi ↦ (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki ↦ le_trans hki hij
  · exact fun n ↦ ⟨n, le_rfl⟩

theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : t ∈ limsup s atTop) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop
    (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : t ∈ limsup s atTop) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail

/-- **Kolmogorov's 0-1 law**, conditional version: every version of the conditional probability of
an event in the tail σ-algebra of a conditionally independent sequence of sub-σ-algebras is `0` or
`1` almost everywhere. -/
theorem _root_.MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_measurableSet_limsup_atTop
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_indep : iCondIndep m hm s μ) {t : Set Ω}
    (ht_tail : t ∈ limsup s atTop) {g : Ω → ℝ}
    (hg : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) g) :
    ∀ᵐ ω ∂μ, g ω = 0 ∨ g ω = 1 :=
  hg.ae_eq_zero_or_one_of_condIndepSet_self hm
    ((condIndep_limsup_atTop_self hm h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

/-- **Kolmogorov's 0-1 law**, conditional version for the tail σ-algebra itself: the tail σ-algebra
of a sequence of sub-σ-algebras that are conditionally independent given `m` is contained in `m` up
to null sets, that is, each of its sets is almost everywhere equal to a set of `m`. -/
theorem limsup_atTop_le_eventuallySigmaAlgebra_of_iCondIndep (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) : limsup s atTop ≤ eventuallySigmaAlgebra m (ae μ) :=
  condIndep_self_iff.1 (condIndep_limsup_atTop_self hm h_indep)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

theorem Kernel.indep_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atBot) (limsup s atBot) κ μα := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, c < i from lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ ↦ Set.Ici_subset_Ici.2
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atBot_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

theorem condIndep_limsup_atBot_self (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atBot) (limsup s atBot) hm μ := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i ↦ bddBelow_Ici
  refine condIndep_limsup_self hm h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine ⟨b, fun c hc hct ↦ ?_⟩
    suffices ∀ i ∈ t, c < i from lt_irrefl c (this c hct)
    exact fun i hi ↦ hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ ↦ Set.Ici_subset_Ici.2
  · exact fun n ↦ ⟨n, le_rfl⟩

/-- **Kolmogorov's 0-1 law**, kernel version: any event in the tail σ-algebra of an independent
sequence of sub-σ-algebras has probability 0 or 1 almost surely. -/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : t ∈ limsup s atBot) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) {t : Set Ω}
    (ht_tail : t ∈ limsup s atBot) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using! Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

/-- **Kolmogorov's 0-1 law**, conditional version: every version of the conditional probability of
an event in the tail σ-algebra at `atBot` of a conditionally independent sequence of
sub-σ-algebras is `0` or `1` almost everywhere. -/
theorem _root_.MeasureTheory.IsCondExp.ae_eq_zero_or_one_of_measurableSet_limsup_atBot
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_indep : iCondIndep m hm s μ) {t : Set Ω}
    (ht_tail : t ∈ limsup s atBot) {g : Ω → ℝ}
    (hg : IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) g) :
    ∀ᵐ ω ∂μ, g ω = 0 ∨ g ω = 1 :=
  hg.ae_eq_zero_or_one_of_condIndepSet_self hm
    ((condIndep_limsup_atBot_self hm h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

/-- **Kolmogorov's 0-1 law**, conditional version for the tail σ-algebra at `atBot` itself: each of
its sets is almost everywhere equal to a set of `m`. -/
theorem limsup_atBot_le_eventuallySigmaAlgebra_of_iCondIndep (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_indep : iCondIndep m hm s μ) : limsup s atBot ≤ eventuallySigmaAlgebra m (ae μ) :=
  condIndep_self_iff.1 (condIndep_limsup_atBot_self hm h_indep)

end AtBot

end ProbabilityTheory

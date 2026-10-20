/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality. We follow the proof in
[Hytonen_VanNeerven_Veraar_Wies_2016].

A conditional expectation is determined only up to almost everywhere equality, so the inequalities
are stated for conditional expectations, or versions: `g` is a version of `f` and `k` is a version
of `φ ∘ f`, written `IsCondExp m μ f g` and `IsCondExp m μ (φ ∘ f) k`. They hold for every choice of
the versions, and so for every representative of the germs `μ[f | m]` and `μ[φ ∘ f | m]`
(`MeasureTheory.mem_condExp_iff`).

The measure `μ` need not be σ-finite on the sub-σ-algebra `m`. The proofs first treat the σ-finite
case. In general, the versions of an integrable function are integrable, so they vanish outside a
set of `m` on which `μ` is σ-finite on `m` (`MeasureTheory.exists_mem_sigmaFinite_trim_restrict`),
and the σ-finite case applies on that set. If `μ` is infinite, the integrability of `f` and of
`φ ∘ f` forces `0 ∈ s` and `φ 0 ≤ 0`, which settles the inequalities outside that set. If `μ` is
finite, it is σ-finite on `m`.

## Main Statement

* `Convex.condExp_mem`: in a Banach space `E`, if an integrable `f` lies in a closed convex set `s`
  a.e., then every conditional expectation of `f` given a sub-σ-algebra `m` lies in `s` a.e.
* `ConvexOn.map_condExp_le`: if `φ : E → ℝ` is convex and lower-semicontinuous on a closed set `s`
  containing `f` a.e., and `f` and `φ ∘ f` are integrable, then `φ ∘ g ≤ᵐ[μ] k` for every
  conditional expectation `g` of `f` and `k` of `φ ∘ f`. The variants
  `ConvexOn.map_condExp_le_univ` and `ConvexOn.map_condExp_le_of_finiteDimensional` treat
  `s = univ`, and `ConvexOn.map_condExp_le_trim` states the inequality for `μ.trim hm`.
  `ConcaveOn.condExp_map_le` and its variants are the concave counterparts.
* `MeasureTheory.IsCondExp.norm_le` and `MeasureTheory.IsCondExp.norm_rpow_le`: the norm of a
  conditional expectation of an integrable function is at most a conditional expectation of the
  norm, and the same holds for the `p`-th power, `1 ≤ p`.

-/

public section

open MeasureTheory Function Set Filter

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f g : α → E} {φ : E → ℝ} {k : α → ℝ} {m mα : SigmaAlgebra α} {μ : Measure α}
  {s : Set E}

/-- A conditional expectation of a function with values in a closed convex set `s` has values in `s`
almost everywhere, for a finite measure and a hereditarily Lindelof space `E`. -/
private lemma Convex.condExp_mem_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hf_int : Integrable f μ) (hs : IsClosed s)
    (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hg : IsCondExp m μ f g) :
    ∀ᵐ a ∂μ, g a ∈ s := by
  obtain ⟨L, c, hLc⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hc hs
  simp_all only [← hLc, RCLike.re_to_real, mem_iInter, ae_all_iff]
  intro n
  exact (hg.comp_continuousLinearMap hf_int (L n)).mono hm (isCondExp_const (c n))
    ((L n).integrable_comp hf_int) (integrable_const (c n)) (hf n)

/-- A conditional expectation of a function with values in a closed convex set `s` has values in `s`
almost everywhere, for a finite measure. The function is almost everywhere valued in a separable
closed subspace, where the previous lemma applies. -/
private lemma Convex.condExp_mem_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hg : IsCondExp m μ f g) : ∀ᵐ a ∂μ, g a ∈ s := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have lem2 : ∀ᵐ a ∂μ, fY a ∈ Y.subtypeL ⁻¹' s := by
    filter_upwards [lem0, hf] with a ha hs
    simpa [fY, ha]
  have hfY_int : Integrable fY μ := by
    refine (hf_int.congr lem1).mono ?_ (by simp [fX])
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset
      ((Submodule.isClosed_topologicalClosure _).measurableSet) Nonempty.of_subtype lem0
    refine ⟨codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha
    have : g a ∈ Y := hg2 a
    simp_all [fY, codRestrict]
  obtain ⟨gY, -, hgY⟩ := exists_stronglyMeasurable_isCondExp hm hfY_int
  have lem3 : g =ᵐ[μ] Y.subtypeL ∘ gY :=
    hg.ae_eq hm hf_int ((hgY.comp_continuousLinearMap hfY_int Y.subtypeL).congr_left lem1.symm)
  filter_upwards [(hc.linear_preimage Y.subtype).condExp_mem_of_hereditarilyLindelofSpace
    hm hfY_int (hs.preimage Y.subtypeL.continuous) lem2 hgY, lem3] with a ha hb
  rwa [hb]

/-- To prove that a property holds almost everywhere for a measure that is σ-finite on a
sub-σ-algebra `m`, it suffices to prove it almost everywhere on each set of `m` of finite
measure. -/
private lemma ae_of_forall_mem_measure_lt_top_ae_restrict (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    {p : α → Prop} (h : ∀ A ∈ m, μ A < ∞ → ∀ᵐ a ∂μ.restrict A, p a) : ∀ᵐ a ∂μ, p a := by
  apply (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null <;>
    rintro - ⟨n, rfl⟩
  · exact hm (measurableSet_spanningSets (μ.trim hm) n)
  exact h _ (measurableSet_iff_mem.mp (measurableSet_spanningSets (μ.trim hm) n))
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n))

/-- A conditional expectation of a function with values in a closed convex set `s` has values in `s`
almost everywhere, for a measure that is σ-finite on the sub-σ-algebra `m`. -/
private lemma Convex.condExp_mem_of_sigmaFinite (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hg : IsCondExp m μ f g) : ∀ᵐ a ∂μ, g a ∈ s := by
  refine ae_of_forall_mem_measure_lt_top_ae_restrict hm fun A hA hAμ ↦ ?_
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hAμ.ne
  exact hc.condExp_mem_of_isFiniteMeasure hm hf_int.restrict hs (ae_restrict_of_ae hf)
    (hg.restrict hm hA)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- If an integrable function has values in a closed set `s` almost everywhere and the measure is
infinite, then `0 ∈ s`: otherwise its norm is bounded below almost everywhere, which makes the
measure finite. -/
private lemma zero_mem_of_not_isFiniteMeasure (hf_int : Integrable f μ) (hs : IsClosed s)
    (hf : ∀ᵐ a ∂μ, f a ∈ s) (hμ : ¬ IsFiniteMeasure μ) : (0 : E) ∈ s := by
  by_contra h0
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.1 (hs.isOpen_compl.mem_nhds h0)
  refine hμ ⟨(measure_mono_ae (hf.mono fun a ha _ ↦ ?_)).trans_lt
    (hf_int.measure_norm_ge_lt_top hδ)⟩
  by_contra h
  exact hδs (mem_ball_zero_iff.2 (not_le.1 h)) ha

/-- If an integrable `f` lies in a closed convex set `s` almost everywhere, then every conditional
expectation `g` of `f` given a sub-σ-algebra `m` lies in `s` almost everywhere. No σ-finiteness of
the measure on `m` is needed. -/
lemma Convex.condExp_mem (hm : m ≤ mα) (hf_int : Integrable f μ) (hs : IsClosed s)
    (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hg : IsCondExp m μ f g) : ∀ᵐ a ∂μ, g a ∈ s := by
  by_cases hμ : IsFiniteMeasure μ
  · exact hc.condExp_mem_of_isFiniteMeasure hm hf_int hs hf hg
  have h0 := zero_mem_of_not_isFiniteMeasure hf_int hs hf hμ
  obtain ⟨t, ht, hσ, hgt⟩ :=
    exists_mem_sigmaFinite_trim_restrict hm (hg.integrable hf_int) hg.aestronglyMeasurable
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ ?_
  · exact hc.condExp_mem_of_sigmaFinite (μ := μ.restrict t) hm hf_int.restrict hs
      (ae_restrict_of_ae hf) (hg.restrict hm ht)
  · filter_upwards [hgt] with a ha
    simpa [ha] using h0

/-- Conditional Jensen's inequality for conditional expectations, for a finite measure and a
hereditarily Lindelof space `E`. -/
private lemma ConvexOn.map_condExp_le_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ s φ)
    (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) (hg : IsCondExp m μ f g)
    (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k := by
  obtain ⟨L, c, hLc1, hLc2⟩ := hφ_cvx.real_sSup_of_nat_affine_eq hs hφ_cont
  have hw : ∀ᵐ a ∂μ, ∀ i : ℕ, L i (g a) + c i ≤ k a := by
    refine ae_all_iff.2 fun i => ?_
    have hi := (hg.comp_continuousLinearMap hf_int (L i)).add (isCondExp_const (c i))
      ((L i).integrable_comp hf_int) (integrable_const (c i))
    refine hi.mono hm hk (((L i).integrable_comp hf_int).add (integrable_const (c i))) hφ_int ?_
    filter_upwards [hf] with a ha using hLc1 i ⟨f a, ha⟩
  filter_upwards [hw, hφ_cvx.1.condExp_mem hm hf_int hs hf hg] with a hw hq
  rw [comp_apply, show φ (g a) = s.domRestrict φ ⟨g a, hq⟩ by simp, ← hLc2]
  simpa using! ciSup_le hw

/-- Conditional Jensen's inequality for conditional expectations, for a finite measure. -/
private theorem ConvexOn.map_condExp_le_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have hfY_int : Integrable fY μ := by
    refine (hf_int.congr lem1).mono ?_ (by simp [fX])
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset
      ((Submodule.isClosed_topologicalClosure _).measurableSet) Nonempty.of_subtype lem0
    refine ⟨codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha
    have : g a ∈ Y := hg2 a
    simp_all [fY, codRestrict]
  obtain ⟨gY, -, hgY⟩ := exists_stronglyMeasurable_isCondExp hm hfY_int
  have lem2 : g =ᵐ[μ] Y.subtypeL ∘ gY :=
    hg.ae_eq hm hf_int ((hgY.comp_continuousLinearMap hfY_int Y.subtypeL).congr_left lem1.symm)
  have lem3 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  have h : φY ∘ gY ≤ᵐ[μ] k := by
    refine (hφ_cvx.comp_linearMap Y.subtype).map_condExp_le_of_hereditarilyLindelofSpace
      (s := Y.subtypeL ⁻¹' s) hm ?_ ?_ ?_ hfY_int (Integrable.congr hφ_int lem3) hgY
      (hk.congr_left lem3)
    · exact hφ_cont.comp (by fun_prop) fun x => by
        #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
        (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
        goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem
        in the new canonicalizer; a minimization would help. The original proof was: `grind` -/
        simp
    · filter_upwards [lem0, hf] with a ha hb
      simp_all [fY]
    · exact hs.preimage Y.subtypeL.continuous
  filter_upwards [lem2, h] with a ha hb
  simpa [φY, ha] using hb

/-- Conditional Jensen's inequality for conditional expectations, for a measure that is σ-finite on
the sub-σ-algebra `m`. -/
private theorem ConvexOn.map_condExp_le_of_sigmaFinite (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k := by
  refine ae_of_forall_mem_measure_lt_top_ae_restrict hm fun A hA hAμ ↦ ?_
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hAμ.ne
  exact hφ_cvx.map_condExp_le_of_isFiniteMeasure hm hφ_cont (ae_restrict_of_ae hf) hs
    hf_int.restrict hφ_int.restrict (hg.restrict hm hA) (hk.restrict hm hA)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- If `f` and `φ ∘ f` are integrable, `f` has values in a closed set `s` almost everywhere, `φ` is
lower-semicontinuous on `s` and the measure is infinite, then `φ 0 ≤ 0`: otherwise `φ ∘ f` is
bounded below by a positive constant on a set of infinite measure, as `f` is small outside a set of
finite measure. -/
private lemma apply_zero_nonpos_of_not_isFiniteMeasure (hφ_cont : LowerSemicontinuousOn φ s)
    (hs : IsClosed s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) (hμ : ¬ IsFiniteMeasure μ) : φ 0 ≤ 0 := by
  by_contra! hφ0
  have h0 := zero_mem_of_not_isFiniteMeasure hf_int hs hf hμ
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 <| eventually_nhdsWithin_iff.1 <|
    hφ_cont 0 h0 (φ 0 / 2) (half_lt_self hφ0)
  refine hμ ⟨(measure_mono_ae (s := univ) (t := {a | δ ≤ ‖f a‖} ∪ {a | φ 0 / 2 ≤ ‖(φ ∘ f) a‖})
    (hf.mono fun a ha _ ↦ ?_)).trans_lt <| (measure_union_le _ _).trans_lt <|
    ENNReal.add_lt_top.2 ⟨hf_int.measure_norm_ge_lt_top hδ,
      hφ_int.measure_norm_ge_lt_top (half_pos hφ0)⟩⟩
  by_cases hfa : δ ≤ ‖f a‖
  · exact Or.inl hfa
  · refine Or.inr ?_
    have := hδs (by simpa using not_le.1 hfa) ha
    simpa using this.le.trans (le_abs_self _)

/-- **Conditional Jensen's inequality**: in a Banach space `E`, if `φ : E → ℝ` is convex and
lower-semicontinuous on a closed set `s`, then for any `f : α → E` such that `f` and `φ ∘ f` are
integrable, and `f` lies in `s` a.e., we have `φ ∘ g ≤ᵐ[μ] k` for every conditional expectation `g`
of `f` and `k` of `φ ∘ f` given a sub-σ-algebra `m`. No σ-finiteness of the measure on `m` is
needed. -/
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ s φ)
    (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) (hg : IsCondExp m μ f g)
    (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k := by
  by_cases hμ : IsFiniteMeasure μ
  · exact hφ_cvx.map_condExp_le_of_isFiniteMeasure hm hφ_cont hf hs hf_int hφ_int hg hk
  have h0 := apply_zero_nonpos_of_not_isFiniteMeasure hφ_cont hs hf hf_int hφ_int hμ
  -- the pair of versions `(g, k)` is integrable, so it vanishes outside a set `t ∈ m` on which `μ`
  -- is σ-finite on `m`
  obtain ⟨t, ht, hσ, hgk⟩ := exists_mem_sigmaFinite_trim_restrict hm
    ((hg.integrable hf_int).prodMk (hk.integrable hφ_int))
    (hg.aestronglyMeasurable.prodMk hk.aestronglyMeasurable)
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ ?_
  · exact hφ_cvx.map_condExp_le_of_sigmaFinite (μ := μ.restrict t) hm hφ_cont
      (ae_restrict_of_ae hf) hs hf_int.restrict hφ_int.restrict (hg.restrict hm ht)
      (hk.restrict hm ht)
  · filter_upwards [hgk] with a ha
    simp only [Pi.zero_apply, Prod.mk_eq_zero] at ha
    simpa [ha.1, ha.2] using h0

/-- **Conditional Jensen's inequality** for the trimmed measure: for `m`-strongly measurable
conditional expectations `g` of `f` and `k` of `φ ∘ f`, we have `φ ∘ g ≤ k` almost everywhere
with respect to `μ.trim hm`, when `φ` is strongly measurable. -/
theorem ConvexOn.map_condExp_le_trim {mE : SigmaAlgebra E} [BorelSpace E] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k)
    (hgm : StronglyMeasurable[m] g) (hkm : StronglyMeasurable[m] k) :
    φ ∘ g ≤ᵐ[μ.trim hm] k := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (hφ_meas.comp_measurable hgm.measurable) hkm]
  exact hφ_cvx.map_condExp_le hm hφ_cont hf hs hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality**, concave version: in a Banach space `E`, if `φ : E → ℝ` is
concave and upper-semicontinuous on a closed set `s`, then for any `f : α → E` such that `f` and
`φ ∘ f` are integrable, and `f` lies in `s` a.e., we have `k ≤ᵐ[μ] φ ∘ g` for every conditional
expectation `g` of `f` and `k` of `φ ∘ f` given a sub-σ-algebra `m`. -/
theorem ConcaveOn.condExp_map_le (hm : m ≤ mα) (hφ_cvx : ConcaveOn ℝ s φ)
    (hφ_cont : UpperSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) (hg : IsCondExp m μ f g)
    (hk : IsCondExp m μ (φ ∘ f) k) : k ≤ᵐ[μ] φ ∘ g := by
  filter_upwards [hφ_cvx.neg.map_condExp_le hm hφ_cont.neg hf hs hf_int hφ_int.neg hg hk.neg]
    with a h
  simpa using h

/-- The concave **conditional Jensen's inequality** for the trimmed measure: for `m`-strongly
measurable conditional expectations `g` of `f` and `k` of `φ ∘ f`, we have `k ≤ φ ∘ g` almost
everywhere with respect to `μ.trim hm`, when `φ` is strongly measurable. -/
theorem ConcaveOn.condExp_map_le_trim {mE : SigmaAlgebra E} [BorelSpace E] (hm : m ≤ mα)
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k)
    (hgm : StronglyMeasurable[m] g) (hkm : StronglyMeasurable[m] k) :
    k ≤ᵐ[μ.trim hm] φ ∘ g := by
  rw [StronglyMeasurable.ae_le_trim_iff hm hkm (hφ_meas.comp_measurable hgm.measurable)]
  exact hφ_cvx.condExp_map_le hm hφ_cont hf hs hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality**: in a Banach space `E`, if `φ : E → ℝ` is convex and
lower-semicontinuous, then for any `f : α → E` such that `f` and `φ ∘ f` are integrable, we have
`φ ∘ g ≤ᵐ[μ] k` for every conditional expectation `g` of `f` and `k` of `φ ∘ f` given a
sub-σ-algebra `m`. -/
theorem ConvexOn.map_condExp_le_univ (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ univ φ)
    (hφ_cont : LowerSemicontinuous φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k :=
  ConvexOn.map_condExp_le hm hφ_cvx (lowerSemicontinuousOn_univ_iff.2 hφ_cont) (by simp)
    isClosed_univ hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality** for the trimmed measure and `s = univ`: for `m`-strongly
measurable conditional expectations `g` of `f` and `k` of `φ ∘ f`, we have `φ ∘ g ≤ k` almost
everywhere with respect to `μ.trim hm`, when `φ` is strongly measurable. -/
theorem ConvexOn.map_condExp_le_trim_univ {mE : SigmaAlgebra E} [BorelSpace E] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k)
    (hgm : StronglyMeasurable[m] g) (hkm : StronglyMeasurable[m] k) :
    φ ∘ g ≤ᵐ[μ.trim hm] k := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (hφ_meas.comp_measurable hgm.measurable) hkm]
  exact hφ_cvx.map_condExp_le_univ hm hφ_cont hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality**, concave version: in a Banach space `E`, if `φ : E → ℝ` is
concave and upper-semicontinuous, then for any `f : α → E` such that `f` and `φ ∘ f` are
integrable, we have `k ≤ᵐ[μ] φ ∘ g` for every conditional expectation `g` of `f` and `k` of `φ ∘ f`
given a sub-σ-algebra `m`. -/
theorem ConcaveOn.condExp_map_le_univ (hm : m ≤ mα) (hφ_cvx : ConcaveOn ℝ univ φ)
    (hφ_cont : UpperSemicontinuous φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : k ≤ᵐ[μ] φ ∘ g := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_univ hm hφ_cont.neg hf_int hφ_int.neg hg hk.neg]
    with a h
  simpa using h

/-- The concave **conditional Jensen's inequality** for the trimmed measure and `s = univ`: for
`m`-strongly measurable conditional expectations `g` of `f` and `k` of `φ ∘ f`, we have
`k ≤ φ ∘ g` almost everywhere with respect to `μ.trim hm`, when `φ` is strongly measurable. -/
theorem ConcaveOn.condExp_map_le_trim_univ {mE : SigmaAlgebra E} [BorelSpace E] (hm : m ≤ mα)
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k)
    (hgm : StronglyMeasurable[m] g) (hkm : StronglyMeasurable[m] k) :
    k ≤ᵐ[μ.trim hm] φ ∘ g := by
  rw [StronglyMeasurable.ae_le_trim_iff hm hkm (hφ_meas.comp_measurable hgm.measurable)]
  exact hφ_cvx.condExp_map_le_univ hm hφ_cont hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality**: in a finite dimensional Banach space `E`, if `φ : E → ℝ` is
convex, then for any `f : α → E` such that `f` and `φ ∘ f` are integrable, we have
`φ ∘ g ≤ᵐ[μ] k` for every conditional expectation `g` of `f` and `k` of `φ ∘ f` given a
sub-σ-algebra `m`. -/
theorem ConvexOn.map_condExp_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ univ φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : φ ∘ g ≤ᵐ[μ] k :=
  hφ_cvx.map_condExp_le_univ hm
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int hg hk

/-- **Conditional Jensen's inequality**, concave version: in a finite dimensional Banach space `E`,
if `φ : E → ℝ` is concave, then for any `f : α → E` such that `f` and `φ ∘ f` are integrable, we
have `k ≤ᵐ[μ] φ ∘ g` for every conditional expectation `g` of `f` and `k` of `φ ∘ f` given a
sub-σ-algebra `m`. -/
theorem ConcaveOn.condExp_map_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    (hφ_cvx : ConcaveOn ℝ univ φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ)
    (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (φ ∘ f) k) : k ≤ᵐ[μ] φ ∘ g := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_of_finiteDimensional hm hf_int hφ_int.neg hg hk.neg]
    with a h
  simpa using h

namespace MeasureTheory.IsCondExp

/-- The norm of a conditional expectation of an integrable function `f` given a sub-σ-algebra `m`
is at most any conditional expectation of the norm of `f`. -/
theorem norm_le (hm : m ≤ mα) (hg : IsCondExp m μ f g) (hk : IsCondExp m μ (‖f ·‖) k)
    (hf : Integrable f μ) : (‖g ·‖) ≤ᵐ[μ] k :=
  convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf hf.norm hg hk

/-- The `p`-th power of the norm of a conditional expectation of an integrable function `f` given
a sub-σ-algebra `m`, `1 ≤ p`, is at most any conditional expectation of the `p`-th power of the
norm of `f`, when it is integrable. -/
theorem norm_rpow_le {p : ℝ} (hp : 1 ≤ p) (hm : m ≤ mα) (hg : IsCondExp m μ f g)
    (hk : IsCondExp m μ (‖f ·‖ ^ p) k) (hf : Integrable f μ) (hfp : Integrable (‖f ·‖ ^ p) μ) :
    (‖g ·‖ ^ p) ≤ᵐ[μ] k := by
  have hp' : 0 < p := by linarith
  have hcvx : ConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ p := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    calc ‖a • x + b • y‖ ^ p
        ≤ (a * ‖x‖ + b * ‖y‖) ^ p := by
          refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp'.le
          simpa using convexOn_univ_norm.2 (mem_univ x) (mem_univ y) ha hb hab
      _ ≤ a * ‖x‖ ^ p + b * ‖y‖ ^ p := by
          simpa using (convexOn_rpow hp).2 (mem_Ici.2 (norm_nonneg x))
            (mem_Ici.2 (norm_nonneg y)) ha hb hab
  exact hcvx.map_condExp_le_univ hm
    ((Real.continuous_rpow_const hp'.le).comp continuous_norm).lowerSemicontinuous hf hfp hg hk

end MeasureTheory.IsCondExp

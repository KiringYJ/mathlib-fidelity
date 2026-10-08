/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Composition-Product of a measure and a kernel

This file develops the composition-product `μ ⊗ₘ κ : Measure (α × β)` of `μ : Measure α` and
`κ : Kernel α β`, defined in `Mathlib.Probability.Kernel.Composition.MeasureCompProd.Defs` on the
domain `μ.HasCompProd κ`. Its value on a measurable set `s` is `∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ`, and
on the whole domain the integral of a measurable function against it is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`
(`MeasureTheory.Measure.lintegral_compProd`).

`μ ⊗ₘ κ` is the composition-product of kernels
`((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ))` evaluated at the point of `Unit`
(`MeasureTheory.Measure.compProd_eq_compProd_const_apply`).

## Notation

* `μ ⊗ₘ κ = μ.compProd κ`
-/

@[expose] public section

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- The composition-product of `μ` and `κ` gives the composition-product of the constant kernel
`μ` with `κ` over the one-point space. -/
instance [μ.HasCompProd κ] : (Kernel.const Unit μ).HasCompProd (Kernel.prodMkLeft Unit κ) where
  hasCompProd_apply _ := ‹μ.HasCompProd κ›
  measurable_lintegral _ _ := Subsingleton.measurable

/-- The composition-product of a measure and a kernel is the composition-product of kernels from
the one-point space. -/
lemma compProd_eq_compProd_const_apply [μ.HasCompProd κ] :
    μ ⊗ₘ κ = (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) () := by
  ext s hs
  rw [compProd_apply hs, Kernel.compProd_apply hs]
  rfl

@[simp]
lemma compProd_apply_univ [IsMarkovKernel κ] : (μ ⊗ₘ κ) univ = μ univ := by
  simp [compProd_apply MeasurableSet.univ]

lemma compProd_apply_prod [μ.HasCompProd κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with a
  by_cases ha : a ∈ s <;> simp [ha]

/-- Two kernels whose measures of the sections of each measurable set agree almost everywhere have
the same composition-product. -/
lemma compProd_congr_sections [μ.HasCompProd κ] [μ.HasCompProd η]
    (h : ∀ ⦃s : Set (α × β)⦄, MeasurableSet s →
      (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] fun a ↦ η a (Prod.mk a ⁻¹' s)) :
    μ ⊗ₘ κ = μ ⊗ₘ η := by
  ext s hs
  rw [compProd_apply hs, compProd_apply hs]
  exact lintegral_congr_ae (h hs)

lemma compProd_congr [μ.HasCompProd κ] [μ.HasCompProd η] (h : κ =ᵐ[μ] η) :
    μ ⊗ₘ κ = μ ⊗ₘ η :=
  compProd_congr_sections fun _ _ ↦ h.mono fun _ ha ↦ by simp only [ha]

/-- Equal measures have the same composition-product with a kernel. Since the domain of the
composition-product depends on the measure, this transports it along an equation `μ = ν`. -/
lemma compProd_congr_measure (h : μ = ν) [μ.HasCompProd κ] [ν.HasCompProd κ] :
    μ ⊗ₘ κ = ν ⊗ₘ κ := by
  subst h
  rfl

@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by
  ext s hs
  simp [compProd_apply hs]

@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : Kernel α β) = 0 := by
  ext s hs
  simp [compProd_apply hs]

lemma compProd_eq_zero_iff [μ.HasCompProd κ] :
    μ ⊗ₘ κ = 0 ↔ ∀ᵐ a ∂μ, κ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ, ← compProd_apply_prod .univ .univ, h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h

/-- The composition-product of a measure with a deterministic kernel is the law of the graph of
the function, for every measure. -/
lemma compProd_deterministic {f : α → β} (hf : Measurable f) :
    μ ⊗ₘ Kernel.deterministic f hf = μ.map (fun a ↦ (a, f a)) := by
  ext s hs
  rw [compProd_apply hs, Measure.map_apply hs (measurable_id'.prodMk hf).aemeasurable]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.deterministic_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 (f a) ∂μ
  _ = ∫⁻ a, ((fun a ↦ (a, f a)) ⁻¹' s).indicator 1 a ∂μ := rfl
  _ = μ ((fun a ↦ (a, f a)) ⁻¹' s) := by
    rw [lintegral_indicator_one]
    exact (measurable_id'.prodMk hf) hs

lemma compProd_id : μ ⊗ₘ Kernel.id = μ.map Function.diag :=
  compProd_deterministic measurable_id

/-- The composition-product of a measure with the image of a kernel under a measurable map exists
when the one with the kernel does: the sections of a measurable set for the image are the sections
of its preimage under `Prod.map id f`. -/
instance hasCompProd_map {γ : Type*} {mγ : SigmaAlgebra γ} [μ.HasCompProd κ] {f : β → γ}
    {hf : Measurable f} : μ.HasCompProd (κ.map f hf) where
  exists_measurable_ge_lintegral_eq s hs := by
    have h_eq (a : α) :
        κ.map f hf a (Prod.mk a ⁻¹' s) = κ a (Prod.mk a ⁻¹' (Prod.map id f ⁻¹' s)) := by
      rw [Kernel.map_apply' _ _ (measurable_prodMk_left hs) hf]
      rfl
    simp_rw [h_eq]
    exact HasCompProd.exists_measurable_ge_lintegral_eq ((measurable_id.prodMap hf) hs)

/-- The composition-product passes along a measurable equivalence `e` of the first factor: the
sections of a measurable set for the image of `μ` under `e` are those of its preimage under
`Prod.map e id` for `μ`. -/
lemma HasCompProd.map_measurableEquiv {γ : Type*} {mγ : SigmaAlgebra γ} (e : α ≃ᵐ γ)
    [μ.HasCompProd κ] :
    (μ.map e e.measurable.aemeasurable).HasCompProd (κ.comap e.symm e.symm.measurable) where
  exists_measurable_ge_lintegral_eq s hs := by
    obtain ⟨g, hg, hle, heq⟩ := HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ) (κ := κ)
      ((e.measurable.prodMap measurable_id) hs)
    refine ⟨g ∘ e.symm, hg.comp e.symm.measurable, fun x ↦ ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := e.surjective x
      simp only [Kernel.comap_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
      exact hle a
    · rw [lintegral_map_equiv, lintegral_map_equiv]
      simp only [Kernel.comap_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
      exact heq

/-- The composition-product of a measure with the image of a kernel under a measurable map is the
image of the composition-product. -/
lemma compProd_map {γ : Type*} {mγ : SigmaAlgebra γ} [μ.HasCompProd κ] {f : β → γ}
    (hf : Measurable f) :
    μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f) := by
  ext s hs
  rw [compProd_apply hs, Measure.map_apply hs (measurable_id.prodMap hf).aemeasurable,
    compProd_apply ((measurable_id.prodMap hf) hs)]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.map_apply' _ _ (measurable_prodMk_left hs) hf]
  rfl

lemma ae_compProd_of_ae_ae [μ.HasCompProd κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x := by
  have hp' : MeasurableSet {x | ¬p x} := hp.compl
  rw [ae_iff, compProd_apply hp', HasCompProd.lintegral_eq_zero_iff hp']
  exact h.mono fun _ ha ↦ ae_iff.mp ha

lemma ae_ae_of_ae_compProd [μ.HasCompProd κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) := by
  obtain ⟨t, hpt, ht, ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  rw [compProd_apply ht, HasCompProd.lintegral_eq_zero_iff ht] at ht0
  filter_upwards [ht0] with a ha
  exact ae_iff.mpr (measure_mono_null (fun b hb ↦ hpt hb) ha)

lemma ae_compProd_iff [μ.HasCompProd κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  ⟨ae_ae_of_ae_compProd, ae_compProd_of_ae_ae hp⟩

lemma ae_compProd_of_ae_fst (κ : Kernel α β) [μ.HasCompProd κ] {p : α → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x.1 :=
  ae_compProd_of_ae_ae (measurable_fst hp) <| by filter_upwards [h] with a ha using by simp [ha]

lemma ae_eq_compProd_of_ae_eq_fst {γ : Type*} {mγ : SigmaAlgebra γ} [MeasurableEq γ]
    (κ : Kernel α β) [μ.HasCompProd κ] {f g : α → γ} (hf : Measurable f) (hg : Measurable g)
    (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma compProd_const {ν : Measure β} [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.productBySections ν := by
  ext s hs
  simp only [compProd_apply hs,
    productBySections_apply, hs, Kernel.const_apply]

@[simp]
lemma fst_compProd (μ : Measure α) (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s hs
  rw [fst_apply hs, compProd_apply (measurable_fst hs)]
  simp_rw [← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage, Function.const_apply]
  have h_eq a : κ a {_b | a ∈ s} = s.indicator 1 a := by
    by_cases ha : a ∈ s <;> simp [ha]
  simp_rw [h_eq, lintegral_indicator_one hs]

/-- The first marginal of the composition-product of a σ-finite measure with a Markov kernel is
σ-finite, since it is the measure (`MeasureTheory.Measure.fst_compProd`). -/
instance sigmaFinite_fst_compProd (μ : Measure α) [SigmaFinite μ] (κ : Kernel α β)
    [IsMarkovKernel κ] : SigmaFinite (μ ⊗ₘ κ).fst := by
  rwa [fst_compProd]

/-- Against counting measure on a space with measurable singletons, the value of a
composition-product on a measurable set is the sum of the measures of the sections. -/
lemma count_compProd_apply [MeasurableSingletonClass α] {s : Set (α × β)} (hs : MeasurableSet s) :
    (count ⊗ₘ κ) s = ∑' a, κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs, lintegral_count]

lemma dirac_compProd_apply [MeasurableSingletonClass α] {a : α}
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs, lintegral_dirac]

lemma dirac_unit_compProd (κ : Kernel Unit β) :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply hs measurable_prodMk_left.aemeasurable]

lemma dirac_unit_compProd_const (μ : Measure β) :
    Measure.dirac () ⊗ₘ Kernel.const Unit μ = μ.map (Prod.mk ()) := by
  ext s hs
  rw [dirac_compProd_apply hs, Kernel.const_apply,
    Measure.map_apply hs measurable_prodMk_left.aemeasurable]

lemma snd_dirac_unit_compProd_const (μ : Measure β) :
    snd (Measure.dirac () ⊗ₘ Kernel.const Unit μ) = μ := by
  ext s hs
  rw [snd_apply hs, dirac_compProd_apply (measurable_snd hs), Kernel.const_apply]
  rfl

instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (μ ⊗ₘ κ) := by
  rw [compProd_eq_compProd_const_apply]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd_eq_compProd_const_apply]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd_eq_compProd_const_apply]; infer_instance

instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd_eq_compProd_const_apply]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

/-- The composition-product of `μ` with `κ ⊗ₖ η` exists when the composition-products `μ ⊗ₘ κ`,
`κ ⊗ₖ η`, and `(μ ⊗ₘ κ) ⊗ₘ η` exist; an s-finite `η` supplies the last one. For a measurable
`s ⊆ α × β × γ` and `s' = MeasurableEquiv.prodAssoc ⁻¹' s`, the measures of the sections of `s` are
the section integrals of the function `p ↦ η p (Prod.mk p ⁻¹' s')`, whose majorant against
`μ ⊗ₘ κ` has section integrals with a measurable majorant, and Tonelli's theorem bounds the
integrals.

Without the domain of `(μ ⊗ₘ κ) ⊗ₘ η` the conclusion can fail (paper proof): for Lebesgue measure
`μ` on `ℝ`, `κ = Kernel.const ℝ (dirac 0)`, and `η` the constant kernel of `Σ_{t ∈ T} dirac t` for
a set `T ⊆ [0, 1]` that is not Lebesgue measurable, the measures of the sections of
`{(a, b, c) | c = a}` against `κ ⊗ₖ η` form the indicator of `T`. -/
instance hasCompProd_compProd {γ : Type*} {mγ : SigmaAlgebra γ} {η : Kernel (α × β) γ}
    [μ.HasCompProd κ] [κ.HasCompProd η] [(μ ⊗ₘ κ).HasCompProd η] : μ.HasCompProd (κ ⊗ₖ η) where
  exists_measurable_ge_lintegral_eq s hs := by
    obtain ⟨G, hG, hFG, hG_eq⟩ := HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ ⊗ₘ κ)
      (κ := η) (MeasurableEquiv.prodAssoc.measurable hs)
    obtain ⟨M, hM, hGM, hM_eq⟩ :=
      HasCompProd.exists_measurable_ge_lintegral_lintegral_eq (μ := μ) (κ := κ) hG
    have h_sec (a : α) : (κ ⊗ₖ η) a (Prod.mk a ⁻¹' s)
        = ∫⁻ b, η (a, b) (Prod.mk (a, b) ⁻¹' (MeasurableEquiv.prodAssoc ⁻¹' s)) ∂κ a :=
      Kernel.compProd_apply (measurable_prodMk_left hs) κ η a
    simp_rw [h_sec]
    have h_le (a : α) : ∫⁻ b, η (a, b) (Prod.mk (a, b) ⁻¹' (MeasurableEquiv.prodAssoc ⁻¹' s)) ∂κ a
        ≤ M a :=
      (lintegral_mono fun b ↦ hFG (a, b)).trans (hGM a)
    refine ⟨M, hM, h_le, le_antisymm (lintegral_mono h_le) ?_⟩
    rw [← hM_eq, ← lintegral_compProd hG, ← hG_eq]
    exact lintegral_compProd_le _

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. The hypotheses are the
domains of `μ ⊗ₘ κ`, `κ ⊗ₖ η`, and `(μ ⊗ₘ κ) ⊗ₘ η`, which give that of `μ ⊗ₘ (κ ⊗ₖ η)`
(`MeasureTheory.Measure.hasCompProd_compProd`); an s-finite `η` supplies the last one. -/
@[simp]
lemma compProd_assoc {γ : Type*} {mγ : SigmaAlgebra γ} {η : Kernel (α × β) γ}
    [μ.HasCompProd κ] [κ.HasCompProd η] [(μ ⊗ₘ κ).HasCompProd η] :
    (μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm = μ ⊗ₘ κ ⊗ₘ η := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hs (by fun_prop),
    Measure.compProd_apply (hs.preimage (by fun_prop)),
    lintegral_compProd_of_exists_measurable_ge
      (HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ ⊗ₘ κ) (κ := η) hs)]
  congr with a
  rw [Kernel.compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
@[simp]
lemma compProd_assoc' {γ : Type*} {mγ : SigmaAlgebra γ} {η : Kernel (α × β) γ}
    [μ.HasCompProd κ] [κ.HasCompProd η] [(μ ⊗ₘ κ).HasCompProd η] :
    (μ ⊗ₘ κ ⊗ₘ η).map MeasurableEquiv.prodAssoc = μ ⊗ₘ (κ ⊗ₖ η) := by
  simp [← Measure.compProd_assoc]

section AbsolutelyContinuous

/-- If `μ ≪ ν` and `κ a ≪ η a` for `μ`-almost every `a`, then `μ ⊗ₘ κ ≪ ν ⊗ₘ η`: a set that is
null for `ν ⊗ₘ η` has `η`-null sections for `ν`-almost every point, hence for `μ`-almost every
point, where its sections are also `κ`-null. -/
lemma AbsolutelyContinuous.compProd [μ.HasCompProd κ] [ν.HasCompProd η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.compProd_apply hs, HasCompProd.lintegral_eq_zero_iff hs] at hs_zero ⊢
  filter_upwards [hμν.ae_eq hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

lemma AbsolutelyContinuous.compProd_left (hμν : μ ≪ ν) (κ : Kernel α β) [μ.HasCompProd κ]
    [ν.HasCompProd κ] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ :=
  hμν.compProd (.of_forall fun _ ↦ .rfl)

lemma AbsolutelyContinuous.compProd_right [μ.HasCompProd κ] [μ.HasCompProd η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
  AbsolutelyContinuous.rfl.compProd hκη

lemma absolutelyContinuous_of_compProd [μ.HasCompProd κ] [ν.HasCompProd η]
    [h_zero : ∀ a, NeZero (κ a)] (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  have h1 : (ν ⊗ₘ η) (s ×ˢ univ) = 0 := by
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ ⊗ₘ κ) (s ×ˢ univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : ∃ a, κ a univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out

lemma absolutelyContinuous_compProd_left_iff [μ.HasCompProd κ] [ν.HasCompProd κ]
    [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν :=
  ⟨absolutelyContinuous_of_compProd, fun h ↦ h.compProd_left κ⟩

lemma AbsolutelyContinuous.compProd_of_compProd [μ.HasCompProd κ] [μ.HasCompProd η]
    [ν.HasCompProd η]
    (hμν : μ ≪ ν) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η := by
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  suffices (μ ⊗ₘ η) s = 0 from hκη this
  rw [measure_eq_zero_iff_ae_notMem, ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

end AbsolutelyContinuous

section MutuallySingular

lemma MutuallySingular.compProd_of_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α β) [μ.HasCompProd κ]
    [ν.HasCompProd η] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ, compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp

lemma mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α}
    [μ.HasCompProd κ] [ν.HasCompProd η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, κ x ⟂ₘ η x := by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ ⊗ₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν ⊗ₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply hs, HasCompProd.lintegral_eq_zero_iff hs] at hμ_zero
  rw [compProd_apply hs.compl, HasCompProd.lintegral_eq_zero_iff hs.compl] at hν_zero
  filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
  exact ⟨Prod.mk x ⁻¹' h.nullSet, measurable_prodMk_left hs, ⟨hxμ, hxν⟩⟩

lemma mutuallySingular_compProd_left_iff [SFinite μ] [SigmaFinite ν]
    [μ.HasCompProd κ] [ν.HasCompProd κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

lemma AbsolutelyContinuous.mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν]
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (hμν : μ ≪ ν) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η := by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left, MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h ↦ h.mono_ac .rfl ?_, fun h ↦ h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuous_withDensity_rnDeriv hμν).compProd_left _
  · exact (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).compProd_left _

lemma mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ]
    [IsSFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ ∀ ξ, SFinite ξ → ξ ≪ μ → ξ ≪ ν → ξ ⊗ₘ κ ⟂ₘ ξ ⊗ₘ η := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left, MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun h ξ hξ hξμ hξν ↦ ?_, fun h ↦ ?_⟩
  · exact h.mono_ac ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
      ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
  · refine h _ ?_ ?_ ?_
    · infer_instance
    · exact absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _)
    · exact withDensity_absolutelyContinuous ν (μ.rnDeriv ν)

end MutuallySingular

lemma absolutelyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν]
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (hκη : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ, compProd_add_left, add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_compProd_iff
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h ↦ h.1.compProd_of_compProd h.2⟩

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

open MeasureTheory

variable {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}

/-- The value at `a` of the first marginal of a kernel `κ` is the first marginal of the measure
`κ a`. -/
lemma fst_apply_eq_fst (κ : Kernel α (β × γ)) (a : α) : fst κ a = (κ a).fst := by
  rw [fst_apply]
  rfl

/-- The value at `a` of the second marginal of a kernel `κ` is the second marginal of the measure
`κ a`. -/
lemma snd_apply_eq_snd (κ : Kernel α (β × γ)) (a : α) : snd κ a = (κ a).snd := by
  rw [snd_apply]
  rfl

/-- The first marginal of the measure `κ a` is σ-finite when the first marginal of `κ` is σ-finite
at `a`. -/
instance sigmaFinite_fst_apply (κ : Kernel α (β × γ)) (a : α) [SigmaFinite (fst κ a)] :
    SigmaFinite (κ a).fst := by
  rw [← fst_apply_eq_fst]
  infer_instance

/-- The first marginal of the measure `κ a` is s-finite when the first marginal of `κ` is s-finite
at `a`. -/
instance sFinite_fst_apply (κ : Kernel α (β × γ)) (a : α) [SFinite (fst κ a)] :
    SFinite (κ a).fst := by
  rw [← fst_apply_eq_fst]
  infer_instance

end ProbabilityTheory.Kernel

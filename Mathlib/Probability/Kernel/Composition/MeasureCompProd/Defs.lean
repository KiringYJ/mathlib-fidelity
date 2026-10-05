/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Yi-Jing Tseng
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Composition-product of a measure and a kernel

For `μ : Measure α` and `κ : Kernel α β`, the composition-product `μ ⊗ₘ κ` is the measure on
`α × β` that integrates the measures of the sections: on a measurable set `s`,
`(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ`.

The section-measure function `a ↦ κ a (Prod.mk a ⁻¹' s)` need not be measurable. The class
`MeasureTheory.Measure.HasCompProd μ κ` asks that, for every measurable set `s`, it have a
measurable majorant with the same integral, that is, equal lower and upper integrals, so that its
integral does not depend on a convention for integrating functions that are not measurable. The
section integrals are then countably additive, and a measure on `α × β` is determined by its values
on measurable sets, so they are the values of a unique measure. This class is the domain of
`μ ⊗ₘ κ`. It holds whenever the section-measure functions are almost everywhere measurable, in
particular for every s-finite kernel `κ` and every measure `μ`, and instance search also supplies it
when `μ` or `κ` is zero or when `μ` is a Dirac measure on a space with measurable singletons.
Neither `μ` nor `κ` has to be s-finite: the composition-product of counting measure on `ℝ`, which
is not s-finite, with the constant kernel `dirac 0` is the image of counting measure under
`a ↦ (a, 0)`, and on a space with measurable singletons a Dirac measure has a composition-product
with every kernel, such as the constant kernel of counting measure on `ℝ`.

The composition-product of kernels `ProbabilityTheory.Kernel.compProd` is a measurable family of
these measures.

## Main definitions

* `MeasureTheory.Measure.HasCompProd μ κ`: the section integrals of `κ` against `μ` are
  unambiguous.
* `MeasureTheory.Measure.compProd μ κ`: the composition-product, with notation `μ ⊗ₘ κ`.

## Main statements

* `MeasureTheory.Measure.HasCompProd.lintegral_iUnion`: the section integrals are countably
  additive.
* `MeasureTheory.Measure.HasCompProd.lintegral_eq_zero_iff`: a section integral vanishes exactly
  when the measures of the sections vanish almost everywhere.
* `MeasureTheory.Measure.compProd_apply`: the value of `μ ⊗ₘ κ` on a measurable set.
-/

@[expose] public section

open scoped ENNReal

open Function ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {μ : Measure α} {κ : Kernel α β}

/-- The composition-product of a measure `μ` and a kernel `κ` exists: for every measurable set
`s ⊆ α × β`, the measures `κ a (Prod.mk a ⁻¹' s)` of its sections have a measurable majorant with
the same integral against `μ`. Since `∫⁻` is the lower integral of a function that is not
measurable, this says that their lower and upper integrals agree, so that the section integral
`∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` does not depend on a convention for integrating such functions.
The section integrals are then countably additive
(`MeasureTheory.Measure.HasCompProd.lintegral_iUnion`), so that they are the values of a unique
measure.

This is the exact domain of `MeasureTheory.Measure.compProd`. It holds whenever the
section-measure functions are almost everywhere measurable
(`MeasureTheory.Measure.HasCompProd.of_aemeasurable`), in particular for an s-finite kernel `κ`
and every measure `μ` (`MeasureTheory.Measure.hasCompProd_of_isSFiniteKernel`), and instance search
also supplies it when `μ` or `κ` is zero or when `μ` is a Dirac measure on a space with measurable
singletons. -/
class HasCompProd (μ : Measure α) (κ : Kernel α β) : Prop where
  /-- For every measurable set, the measures of its sections have a measurable majorant with the
  same integral. -/
  exists_measurable_ge_lintegral_eq ⦃s : Set (α × β)⦄ (hs : MeasurableSet s) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ (fun a ↦ κ a (Prod.mk a ⁻¹' s)) ≤ g ∧
      ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ = ∫⁻ a, g a ∂μ

/-- The section integrals of the composition-product are countably additive: on a countable
disjoint union, measurable majorants bound them from above and measurable minorants from below. -/
lemma HasCompProd.lintegral_iUnion [h : μ.HasCompProd κ] ⦃f : ℕ → Set (α × β)⦄
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    ∫⁻ a, κ a (Prod.mk a ⁻¹' ⋃ i, f i) ∂μ = ∑' i, ∫⁻ a, κ a (Prod.mk a ⁻¹' f i) ∂μ := by
  have hsum (a : α) : κ a (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, κ a (Prod.mk a ⁻¹' f i) := by
    rw [preimage_iUnion, measure_iUnion (hd.mono fun _ _ ↦ .preimage _)
      fun i ↦ measurable_prodMk_left (hf i)]
  simp_rw [hsum]
  refine le_antisymm ?_ ?_
  · choose g hg hfg hg_eq using fun i ↦ h.exists_measurable_ge_lintegral_eq (hf i)
    calc ∫⁻ a, ∑' i, κ a (Prod.mk a ⁻¹' f i) ∂μ
    _ ≤ ∫⁻ a, ∑' i, g i a ∂μ := lintegral_mono fun a ↦ ENNReal.tsum_le_tsum fun i ↦ hfg i a
    _ = ∑' i, ∫⁻ a, g i a ∂μ := lintegral_tsum fun i ↦ (hg i).aemeasurable
    _ = ∑' i, ∫⁻ a, κ a (Prod.mk a ⁻¹' f i) ∂μ := by simp_rw [hg_eq]
  · choose g hg hgf hg_eq using fun i ↦
      exists_measurable_le_lintegral_eq (μ := μ) fun a ↦ κ a (Prod.mk a ⁻¹' f i)
    calc ∑' i, ∫⁻ a, κ a (Prod.mk a ⁻¹' f i) ∂μ
    _ = ∑' i, ∫⁻ a, g i a ∂μ := by simp_rw [hg_eq]
    _ = ∫⁻ a, ∑' i, g i a ∂μ := (lintegral_tsum fun i ↦ (hg i).aemeasurable).symm
    _ ≤ ∫⁻ a, ∑' i, κ a (Prod.mk a ⁻¹' f i) ∂μ :=
      lintegral_mono fun a ↦ ENNReal.tsum_le_tsum fun i ↦ hgf i a

/-- A section integral vanishes exactly when the measures of the sections vanish almost
everywhere: a measurable majorant with the same integral then vanishes almost everywhere. -/
lemma HasCompProd.lintegral_eq_zero_iff [h : μ.HasCompProd κ] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ = 0 ↔ (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ (lintegral_congr_ae h0).trans lintegral_zero⟩
  obtain ⟨g, hg, hfg, hg_eq⟩ := h.exists_measurable_ge_lintegral_eq hs
  rw [hg_eq, MeasureTheory.lintegral_eq_zero_iff hg] at h0
  filter_upwards [h0] with a ha
  exact le_antisymm ((hfg a).trans_eq ha) zero_le

/-- The composition-product of a measure `μ` and a kernel `κ`: the measure on `α × β` whose value
on a measurable set is the integral against `μ` of the `κ`-measures of its sections. Its domain is
`μ.HasCompProd κ`. -/
noncomputable def compProd (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] :
    Measure (α × β) :=
  ofMeasurable (fun s _ ↦ ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ) (by simp) HasCompProd.lintegral_iUnion

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

lemma compProd_apply [μ.HasCompProd κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ :=
  ofMeasurable_apply s hs

/-- A measure is the composition-product of `μ` and `κ` if and only if its values on measurable sets
are the section integrals. -/
lemma eq_compProd_iff [μ.HasCompProd κ] {ρ : Measure (α × β)} :
    ρ = μ ⊗ₘ κ ↔ ∀ s, MeasurableSet s → ρ s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  refine ⟨fun h s hs ↦ h ▸ compProd_apply hs, fun h ↦ ext fun s hs ↦ ?_⟩
  rw [h s hs, compProd_apply hs]

/-- The composition-product exists when the measures of the sections of every measurable set
depend almost everywhere measurably on the point: a measurable function that agrees with them
almost everywhere, raised to `∞` on a measurable null set, is a majorant with the same integral. -/
lemma HasCompProd.of_aemeasurable
    (h : ∀ ⦃s : Set (α × β)⦄, MeasurableSet s → AEMeasurable (fun a ↦ κ a (Prod.mk a ⁻¹' s)) μ) :
    μ.HasCompProd κ where
  exists_measurable_ge_lintegral_eq s hs := by
    obtain ⟨G, hG, hFG⟩ := h hs
    set N := toMeasurable μ {a | κ a (Prod.mk a ⁻¹' s) ≠ G a}
    have hN : μ N = 0 := by rw [measure_toMeasurable]; exact hFG
    classical
    refine ⟨N.piecewise (fun _ ↦ ∞) G,
      measurable_const.piecewise (measurableSet_toMeasurable _ _) hG, fun a ↦ ?_, ?_⟩
    · by_cases ha : a ∈ N
      · simp [ha]
      · have : κ a (Prod.mk a ⁻¹' s) = G a :=
          not_not.mp fun h' ↦ ha (subset_toMeasurable _ _ h')
        simp [ha, this]
    · refine lintegral_congr_ae (hFG.trans ?_)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN] with a ha
      simp [ha]

/-- The composition-product of an s-finite kernel with any measure exists, since the measures of
the sections of a measurable set depend measurably on the point. -/
instance hasCompProd_of_isSFiniteKernel [IsSFiniteKernel κ] : μ.HasCompProd κ :=
  .of_aemeasurable fun _ hs ↦ (Kernel.measurable_kernel_prodMk_left hs).aemeasurable

instance hasCompProd_zero_left : (0 : Measure α).HasCompProd κ :=
  .of_aemeasurable fun _ _ ↦ aemeasurable_zero_measure

instance hasCompProd_zero_right : μ.HasCompProd (0 : Kernel α β) :=
  .of_aemeasurable fun _ _ ↦ by simp

/-- Against a Dirac measure on a space with measurable singletons, every function is almost
everywhere constant. -/
instance hasCompProd_dirac [MeasurableSingletonClass α] (x : α) : (dirac x).HasCompProd κ :=
  .of_aemeasurable fun _ _ ↦ ⟨_, measurable_const, ae_eq_dirac _⟩

end MeasureTheory.Measure

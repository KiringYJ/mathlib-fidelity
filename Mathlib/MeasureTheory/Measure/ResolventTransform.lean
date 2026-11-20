/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity

/-!
# Resolvent Transform of a Measure

Given a normed algebra `A` over a normed field `𝕜` and a measure `μ` on `𝕜`, the
resolvent transform at `a : A` integrates the inverse of `algebraMap 𝕜 A x - a`.
Its input carries the a.e. invertibility condition, and the integral is taken over the
resolvent set with the pullback of `μ` to that set.

For `𝕜 = ℝ` and `A = ℂ` this gives the Stieltjes transform. For `𝕜 = A = ℂ` it gives
the Cauchy transform.

## Main statements

* `hasDerivAt_resolventTransform`: Away from the image of the support of a finite measure,
  the derivative is the integral of the squared resolvent over the support.
* `analyticOn_resolventTransform`: For `A = ℂ`, the transform is holomorphic on that
  open complement.
-/

public section

variable {𝕜 A : Type*}

open Filter MeasureTheory Measure Metric Complex Set spectrum
open scoped Topology

namespace MeasureTheory

section Definition

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [NormedAlgebra ℝ A]
  [SigmaAlgebra 𝕜]

/-- The points where the resolvent of `a` exists `μ`-almost everywhere. -/
@[expose]
def resolventTransformDomain (μ : Measure 𝕜) : Set A := {a | resolventSet 𝕜 a ∈ ae μ}

/-- The integral of the resolvent over its `μ`-conull domain. -/
@[expose]
noncomputable def resolventTransform (μ : Measure 𝕜)
    (a : resolventTransformDomain (A := A) μ) : A :=
  ∫ x : resolventSet 𝕜 a.val, resolvent a.val x ∂μ.comap Subtype.val

lemma resolventTransform_def (μ : Measure 𝕜) :
    resolventTransform μ = fun (a : resolventTransformDomain (A := A) μ) ↦
      ∫ x : resolventSet 𝕜 a.val, resolvent a.val x ∂μ.comap Subtype.val := rfl

lemma resolventTransform_apply (μ : Measure 𝕜) (a : resolventTransformDomain (A := A) μ) :
    resolventTransform μ a =
      ∫ x : resolventSet 𝕜 a.val, resolvent a.val x ∂μ.comap Subtype.val := rfl

@[simp]
lemma resolventTransform_zero_measure : resolventTransform (0 : Measure 𝕜) =
    (0 : resolventTransformDomain (A := A) (0 : Measure 𝕜) → A) := by
  ext a
  simp [resolventTransform]

@[simp]
lemma resolventTransform_dirac [MeasurableSingletonClass 𝕜] [CompleteSpace A]
    (x : 𝕜) (a : A) (hx : x ∈ resolventSet 𝕜 a) :
    resolventTransform (.dirac x) ⟨a, by simpa [resolventTransformDomain, ae_dirac_eq] using hx⟩ =
      resolvent a ⟨x, hx⟩ := by
  let y : resolventSet 𝕜 a := ⟨x, hx⟩
  have hnull : NullMeasurableSet (resolventSet 𝕜 a) (.dirac x) := by
    apply NullMeasurableSet.compl_iff.mp
    exact NullMeasurableSet.of_null (by simp [Measure.dirac_apply, hx])
  have hImage (s : Set (resolventSet 𝕜 a)) (hs : MeasurableSet s) :
      NullMeasurableSet (Subtype.val '' s) (.dirac x) := by
    obtain ⟨t, ht, rfl⟩ := hs
    rw [image_preimage_eq_inter_range, Subtype.range_val]
    exact (show MeasurableSet t from ht).nullMeasurableSet.inter hnull
  have hcomap : (Measure.dirac x).comap (Subtype.val : resolventSet 𝕜 a → 𝕜) = .dirac y := by
    ext1 s hs
    rw [Measure.comap_apply₀ _ _ Subtype.val_injective hImage hs.nullMeasurableSet]
    have hmem : x ∈ Subtype.val '' s ↔ y ∈ s := by
      constructor
      · rintro ⟨z, hz, hz'⟩
        have hy : z = y := Subtype.ext hz'
        exact hy ▸ hz
      · exact fun hy ↦ ⟨y, hy, rfl⟩
    rw [Measure.dirac_apply, Measure.dirac_apply]
    by_cases hx' : x ∈ Subtype.val '' s
    · rw [indicator_of_mem hx', indicator_of_mem (hmem.mp hx')]
      rfl
    · rw [indicator_of_notMem hx', indicator_of_notMem (hmem.not.mp hx')]
  change ∫ z : resolventSet 𝕜 a, resolvent a z ∂(Measure.dirac x).comap Subtype.val = resolvent a y
  rw [hcomap, integral_dirac]

end Definition

section Resolvent

variable [NontriviallyNormedField 𝕜] [SigmaAlgebra 𝕜]

@[fun_prop]
theorem measurable_resolvent {a : A} [OpensSigmaAlgebra 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] [SigmaAlgebra A] [BorelSpace A] :
    Measurable (resolvent (R := 𝕜) a) :=
  (continuous_iff_continuousAt.mpr fun x ↦
    (hasDerivAt_resolvent_const_left x).hasFDerivAt.continuousAt
      continuous_subtype_val.continuousAt).measurable

variable [NormedDivisionRing A] [NormedAlgebra 𝕜 A]

theorem mem_resolventSet_of_mem_support {μ : Measure 𝕜} {a : A}
    (ha : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x ∈ μ.support) :
    x ∈ resolventSet 𝕜 a :=
  (sub_ne_zero.mpr fun h ↦ ha ⟨x, hx, h⟩).isUnit

theorem mem_resolventTransformDomain_of_notMem_image_support [HereditarilyLindelofSpace 𝕜]
    {μ : Measure 𝕜} {a : A} (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    a ∈ resolventTransformDomain μ :=
  Filter.mem_of_superset (support_mem_ae (μ := μ)) fun _ hx ↦
    mem_resolventSet_of_mem_support ha hx

private theorem isClosed_image_support [CompleteSpace 𝕜] (μ : Measure 𝕜) :
    IsClosed (algebraMap 𝕜 A '' μ.support) :=
  (algebraMap_isometry 𝕜 A).isClosedEmbedding.isClosed_iff_image_isClosed.mp isClosed_support

/-- A point outside the embedded nonempty support has positive distance from it. -/
theorem infDist_image_support_pos [CompleteSpace 𝕜] {μ : Measure 𝕜} {a : A}
    (ha : a ∉ algebraMap 𝕜 A '' μ.support) (hμ : μ.support.Nonempty) :
    0 < infDist a (algebraMap 𝕜 A '' μ.support) :=
  (IsClosed.notMem_iff_infDist_pos (isClosed_image_support μ) (hμ.image _)).mp ha

omit [SigmaAlgebra 𝕜] in
private theorem norm_resolvent_eq_inv_norm {a : A} (x : resolventSet 𝕜 a) :
    ‖resolvent a x‖ = Checked.inv ‖algebraMap 𝕜 A x - a‖
      (norm_ne_zero_iff.mpr x.property.ne_zero).isUnit := by
  change ‖Checked.inv (algebraMap 𝕜 A x - a) x.property‖ = _
  exact norm_inv _

theorem norm_resolvent_le_inv_infDist_support [CompleteSpace 𝕜] {μ : Measure 𝕜} {a : A}
    (ha : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x ∈ μ.support) :
    ‖resolvent a ⟨x, mem_resolventSet_of_mem_support ha hx⟩‖ ≤
      Checked.inv (infDist a (algebraMap 𝕜 A '' μ.support))
        (infDist_image_support_pos ha ⟨x, hx⟩).ne'.isUnit := by
  have hdist := infDist_image_support_pos ha ⟨x, hx⟩
  have hle : infDist a (algebraMap 𝕜 A '' μ.support) ≤ ‖algebraMap 𝕜 A x - a‖ := by
    simpa only [dist_comm a, dist_eq_norm] using
      (infDist_le_dist_of_mem (x := a) (mem_image_of_mem (algebraMap 𝕜 A) hx))
  rw [norm_resolvent_eq_inv_norm]
  exact (inv_le_inv₀ (hdist.trans_le hle) hdist).mpr hle

variable [OpensSigmaAlgebra 𝕜] [CompleteSpace A]

private theorem measurable_resolvent_on_support [SigmaAlgebra A] [BorelSpace A]
    {μ : Measure 𝕜} {a : A} (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    Measurable (fun x : μ.support ↦ resolvent a ⟨x.val, mem_resolventSet_of_mem_support ha x.2⟩) :=
  measurable_resolvent.comp (measurable_inclusion fun _ hx ↦ mem_resolventSet_of_mem_support ha hx)

theorem integrable_resolvent [CompleteSpace 𝕜] [HereditarilyLindelofSpace 𝕜]
    [SecondCountableTopology A] [SigmaAlgebra A] [BorelSpace A]
    {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    Integrable (fun x : μ.support ↦ resolvent a ⟨x.val, mem_resolventSet_of_mem_support ha x.2⟩)
      (μ.comap Subtype.val) := by
  by_cases h : μ.support.Nonempty
  · refine ⟨(measurable_resolvent_on_support ha).aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded
      (C := Checked.inv _ (infDist_image_support_pos ha h).ne'.isUnit)
      (Eventually.of_forall fun x ↦ norm_resolvent_le_inv_infDist_support ha x.2)
  · have hzero := support_eq_empty_iff.mp (not_nonempty_iff_eq_empty.mp h)
    simp [hzero]

private theorem resolventTransform_eq_integral_support [NormedAlgebra ℝ A]
    [HereditarilyLindelofSpace 𝕜] {μ : Measure 𝕜} {a : A}
    (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    resolventTransform μ ⟨a, mem_resolventTransformDomain_of_notMem_image_support ha⟩ =
      ∫ x : μ.support, resolvent a ⟨x.val, mem_resolventSet_of_mem_support ha x.2⟩
        ∂μ.comap Subtype.val := by
  let i : μ.support → resolventSet 𝕜 a := inclusion fun _ hx ↦
    mem_resolventSet_of_mem_support ha hx
  have hi : Measurable i := measurable_inclusion _
  have hρ : MeasurableSet (resolventSet 𝕜 a) := (isOpen_resolventSet a).measurableSet
  have hS : MeasurableSet μ.support := isClosed_support.measurableSet
  have eρ := MeasurableEmbedding.subtype_coe hρ
  have ei : MeasurableEmbedding i := by
    refine ⟨inclusion_injective _, hi, fun s hs ↦ eρ.measurableSet_image.mp ?_⟩
    rw [← image_comp]
    exact (MeasurableEmbedding.subtype_coe hS).measurableSet_image' hs
  have hm : (μ.comap (Subtype.val : μ.support → 𝕜)).map i hi.aemeasurable =
      μ.comap (Subtype.val : resolventSet 𝕜 a → 𝕜) := by
    apply eρ.map_injective
    change ((μ.comap (Subtype.val : μ.support → 𝕜)).map i hi.aemeasurable).map
      (Subtype.val : resolventSet 𝕜 a → 𝕜) eρ.measurable.aemeasurable =
      (μ.comap (Subtype.val : resolventSet 𝕜 a → 𝕜)).map Subtype.val
        eρ.measurable.aemeasurable
    rw [Measure.map_map hi.aemeasurable eρ.measurable.aemeasurable]
    change (μ.comap (Subtype.val : μ.support → 𝕜)).map Subtype.val _ =
      (μ.comap (Subtype.val : resolventSet 𝕜 a → 𝕜)).map Subtype.val _
    rw [map_comap_subtype_coe hS μ, map_comap_subtype_coe hρ μ,
      Measure.restrict_eq_self_of_ae_mem (s := μ.support) support_mem_ae,
      Measure.restrict_eq_self_of_ae_mem (s := resolventSet 𝕜 a)
        (mem_resolventTransformDomain_of_notMem_image_support ha)]
  change ∫ x, resolvent a x ∂μ.comap Subtype.val = _
  rw [← hm]
  exact ei.integral_map _

end Resolvent

section Deriv

variable [NontriviallyNormedField 𝕜] [HereditarilyLindelofSpace 𝕜] [CompleteSpace 𝕜]
  [SigmaAlgebra 𝕜] [BorelSpace 𝕜]

theorem hasDerivAt_resolventTransform [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 𝕜}
    [IsFiniteMeasure μ] (a : {a : A // a ∉ algebraMap 𝕜 A '' μ.support}) :
    HasDerivAt
      (fun w : {w : A // w ∉ algebraMap 𝕜 A '' μ.support} ↦ resolventTransform μ
        ⟨w.val, mem_resolventTransformDomain_of_notMem_image_support w.2⟩)
      (∫ x : μ.support, resolvent a.val ⟨x.val, mem_resolventSet_of_mem_support a.2 x.2⟩ ^ 2
        ∂μ.comap Subtype.val) a Subtype.val := by
  let D : Set A := (algebraMap 𝕜 A '' μ.support)ᶜ
  let F (w : D) (x : μ.support) : A :=
    resolvent w.val ⟨x.val, mem_resolventSet_of_mem_support w.2 x.2⟩
  let ν := μ.comap (Subtype.val : μ.support → 𝕜)
  have hF : (fun w : D ↦ resolventTransform μ
      ⟨w.val, mem_resolventTransformDomain_of_notMem_image_support w.2⟩) =
      (fun w : D ↦ ∫ x, F w x ∂ν) :=
    funext fun w ↦ resolventTransform_eq_integral_support w.2
  change HasDerivAt (fun w : D ↦ resolventTransform μ
    ⟨w.val, mem_resolventTransformDomain_of_notMem_image_support w.2⟩)
      (∫ x, (F a x) ^ 2 ∂ν) a Subtype.val
  rw [hF]
  by_cases! hμ : μ.support.Nonempty
  swap
  · have hzero := support_eq_empty_iff.mp hμ
    simp only [ν, hzero, Measure.comap_zero, integral_zero_measure]
    have hc : HasFDerivAt (fun _ : D ↦ (0 : A)) (0 : A →L[A] A) a Subtype.val :=
      (hasFDerivAt_const (𝕜 := A) (0 : A) a.val).comp_tendsto
        (Subtype.val : D → A) (continuous_subtype_val.continuousAt.tendsto.prodMap
          (Filter.tendsto_pure_pure ..))
    simpa only [zero_apply] using hc.hasDerivAt
  have hd := infDist_image_support_pos a.2 hμ
  let R := infDist a.val (algebraMap 𝕜 A '' μ.support) / 2
  have hR : 0 < R := by positivity
  let s : Set D := Subtype.val ⁻¹' ball a.val R
  have hs : s ∈ 𝓝 a := continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hR)
  have hmeas (w : D) : Measurable (F w) := measurable_resolvent_on_support w.2
  have hdist {w : D} (hw : w ∈ s) (x : μ.support) : R ≤ ‖algebraMap 𝕜 A x - w.val‖ := by
    calc
      R ≤ infDist a.val (algebraMap 𝕜 A '' μ.support) - R := by
        dsimp [R]
        linarith
      _ ≤ ‖algebraMap 𝕜 A x - a.val‖ - ‖a.val - w.val‖ := by
        gcongr
        · simpa only [dist_comm a.val, dist_eq_norm] using
            (infDist_le_dist_of_mem (x := a.val) (mem_image_of_mem (algebraMap 𝕜 A) x.2))
        · have hw' : dist w.val a.val < R := hw
          simpa only [dist_eq_norm, norm_sub_rev w.val a.val] using hw'.le
      _ ≤ ‖algebraMap 𝕜 A x - w.val‖ := by
        rw [sub_le_iff_le_add]
        simpa only [dist_eq_norm, norm_sub_rev w.val a.val] using
          dist_triangle (algebraMap 𝕜 A x) w.val a.val
  have hbound : ∀ᵐ x ∂ν, ∀ w ∈ s, ‖F w x ^ 2‖ ≤ Checked.inv R hR.ne'.isUnit ^ 2 := by
    refine Eventually.of_forall fun x w hw ↦ ?_
    rw [norm_pow]
    gcongr
    dsimp only [F]
    rw [norm_resolvent_eq_inv_norm]
    exact (inv_le_inv₀ (hR.trans_le (hdist hw x)) hR).mpr (hdist hw x)
  have hderiv (w : D) (x : μ.support) :
      HasDerivAt (F · x) (F w x ^ 2) w Subtype.val := by
    let i (z : D) : {a : A | x.val ∈ resolventSet 𝕜 a} :=
      ⟨z.val, mem_resolventSet_of_mem_support z.2 x.2⟩
    have hFid : HasFDerivAt (Subtype.val : D → A) (.id A A) w Subtype.val :=
      (hasFDerivAt_id w.val).comp_tendsto (Subtype.val : D → A)
        (continuous_subtype_val.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
    have hid : HasDerivAt ((Subtype.val : {a : A | x.val ∈ resolventSet 𝕜 a} → A) ∘ i)
        1 w (Subtype.val : D → A) := by
      simpa only [ContinuousLinearMap.id_apply, Function.comp_def, i] using hFid.hasDerivAt
    simpa only [Function.comp_def, F, i, mul_one] using
      (hasDerivAt_resolvent_const_right (i w).2).comp w hid
        continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun w ↦ (hmeas w).aestronglyMeasurable) (integrable_resolvent a.2)
    ((hmeas a).pow_const 2).aestronglyMeasurable hbound (integrable_const _)
    (Eventually.of_forall fun x w _ ↦ hderiv w x)
    (isClosed_image_support μ).isOpen_compl.isOpenEmbedding_subtypeVal).2

theorem analyticOn_resolventTransform [NormedAlgebra 𝕜 ℂ] {μ : Measure 𝕜} [IsFiniteMeasure μ] :
    AnalyticOn ℂ (fun a : {a : ℂ // a ∉ algebraMap 𝕜 ℂ '' μ.support} ↦ resolventTransform μ
      ⟨a.val, mem_resolventTransformDomain_of_notMem_image_support a.2⟩) univ Subtype.val := by
  let D : Set ℂ := (algebraMap 𝕜 ℂ '' μ.support)ᶜ
  let f (a : D) := resolventTransform μ
    ⟨a.val, mem_resolventTransformDomain_of_notMem_image_support a.2⟩
  let g := Function.extend (Subtype.val : D → ℂ) f 0
  have heq : (fun a : D ↦ g a.val) = f :=
    funext fun a ↦ Subtype.val_injective.extend_apply _ _ a
  have hopen : IsOpen D := (isClosed_image_support μ).isOpen_compl
  have hdiff : DifferentiableOn ℂ g D := by
    intro z hz
    have hd := (hasDerivAt_resolventTransform (μ := μ) (⟨z, hz⟩ : D)).differentiableAt
    exact (DifferentiableAt.of_restrict (s := D) (x := (⟨z, hz⟩ : D))
      (by rw [heq]; exact hd) (hopen.mem_nhds hz)).differentiableWithinAt
  refine AnalyticOnNhd.analyticOn ?_
  intro a _
  change AnalyticAt ℂ f a Subtype.val
  rw [← heq]
  exact (hdiff.analyticAt (hopen.mem_nhds a.2)).comp_domain (g := Subtype.val) (x := a)

end Deriv

end MeasureTheory

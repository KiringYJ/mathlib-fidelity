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
when `μ` or `κ` is zero or when `μ` is a Dirac measure or counting measure on a space with
measurable singletons (`MeasureTheory.Measure.hasCompProd_count`).
Neither `μ` nor `κ` has to be s-finite: the composition-product of counting measure on `ℝ`, which
is not s-finite, with the constant kernel `dirac 0` is the image of counting measure under
`a ↦ (a, 0)`, and on a space with measurable singletons a Dirac measure has a composition-product
with every kernel, such as the constant kernel of counting measure on `ℝ`.

Tonelli's theorem holds on the whole domain: for a measurable function `f` on `α × β`, the section
integrals `a ↦ ∫⁻ b, f (a, b) ∂κ a` again have a measurable majorant with the same integral, and
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ`. The domain is closed under finite and
countable sums and scalar multiples of the measure and under finite and countable sums of the
kernel, but not under uncountable sums of the measure.

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
* `MeasureTheory.Measure.HasCompProd.exists_measurable_ge_lintegral_lintegral_eq`: the section
  integrals of a measurable function have a measurable majorant with the same integral.
* `MeasureTheory.Measure.lintegral_compProd`: Tonelli's theorem for `μ ⊗ₘ κ`.
* `MeasureTheory.Measure.lintegral_compProd_le`: for a function that need not be measurable, the
  integral against `μ ⊗ₘ κ` is at most the iterated integral.
* `MeasureTheory.Measure.compProd_add_left`, `MeasureTheory.Measure.compProd_sum_left`,
  `MeasureTheory.Measure.compProd_smul_left`, `MeasureTheory.Measure.compProd_add_right`, and
  `MeasureTheory.Measure.compProd_sum_right`: the composition-product is additive in each argument
  and homogeneous in the measure.
* `MeasureTheory.Measure.compProd_const_apply_prod`: against a constant kernel, the measure of a
  rectangle is the product of the measures of its sides, also when they are not measurable.
-/

@[expose] public section

open scoped ENNReal

open Function ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-! ### Functions with a measurable majorant with the same integral -/

section Majorant

/-- `F` has a measurable majorant with the same integral against `μ`, that is, its lower and upper
integrals agree. -/
private def HasLIntegralMajorant (μ : Measure α) (F : α → ℝ≥0∞) : Prop :=
  ∃ g : α → ℝ≥0∞, Measurable g ∧ F ≤ g ∧ ∫⁻ a, F a ∂μ = ∫⁻ a, g a ∂μ

/-- The integral is additive on a function with a measurable majorant with the same integral: the
majorant bounds the integral of a sum from above, and the integral is superadditive. -/
private lemma HasLIntegralMajorant.lintegral_add {F : α → ℝ≥0∞} (hF : HasLIntegralMajorant μ F)
    (G : α → ℝ≥0∞) :
    ∫⁻ a, F a + G a ∂μ = ∫⁻ a, F a ∂μ + ∫⁻ a, G a ∂μ := by
  obtain ⟨g, hg, hFg, hF_eq⟩ := hF
  refine le_antisymm ?_ (le_lintegral_add F G)
  calc ∫⁻ a, F a + G a ∂μ
  _ ≤ ∫⁻ a, g a + G a ∂μ := lintegral_mono fun a ↦ by gcongr; exact hFg a
  _ = ∫⁻ a, F a ∂μ + ∫⁻ a, G a ∂μ := by rw [lintegral_add_left hg, hF_eq]

private lemma HasLIntegralMajorant.add {F G : α → ℝ≥0∞} (hF : HasLIntegralMajorant μ F)
    (hG : HasLIntegralMajorant μ G) :
    HasLIntegralMajorant μ fun a ↦ F a + G a := by
  have h_eq := hF.lintegral_add G
  obtain ⟨f, hf, hFf, hF_eq⟩ := hF
  obtain ⟨g, hg, hGg, hG_eq⟩ := hG
  refine ⟨fun a ↦ f a + g a, hf.add hg, fun a ↦ add_le_add (hFf a) (hGg a), ?_⟩
  rw [h_eq, lintegral_add_left hf, hF_eq, hG_eq]

/-- The integral commutes with multiplication by a constant on a function with a measurable
majorant with the same integral. -/
private lemma HasLIntegralMajorant.lintegral_const_mul {F : α → ℝ≥0∞}
    (hF : HasLIntegralMajorant μ F) (c : ℝ≥0∞) :
    ∫⁻ a, c * F a ∂μ = c * ∫⁻ a, F a ∂μ := by
  obtain ⟨g, hg, hFg, hF_eq⟩ := hF
  refine le_antisymm ?_ (lintegral_const_mul_le c F)
  calc ∫⁻ a, c * F a ∂μ
  _ ≤ ∫⁻ a, c * g a ∂μ := lintegral_mono fun a ↦ mul_le_mul' le_rfl (hFg a)
  _ = c * ∫⁻ a, F a ∂μ := by rw [MeasureTheory.lintegral_const_mul c hg, hF_eq]

private lemma HasLIntegralMajorant.const_mul {F : α → ℝ≥0∞} (hF : HasLIntegralMajorant μ F)
    (c : ℝ≥0∞) :
    HasLIntegralMajorant μ fun a ↦ c * F a := by
  have h_eq := hF.lintegral_const_mul c
  obtain ⟨g, hg, hFg, hF_eq⟩ := hF
  refine ⟨fun a ↦ c * g a, hg.const_mul c, fun a ↦ mul_le_mul' le_rfl (hFg a), ?_⟩
  rw [h_eq, MeasureTheory.lintegral_const_mul c hg, hF_eq]

/-- Monotone convergence for an increasing sequence of functions with measurable majorants with the
same integrals. It fails for the lower integrals of arbitrary functions, but the infima
`⨅ m ≥ n, g m` of the majorants form an increasing sequence of measurable majorants with the same
integrals, to which it applies. -/
private lemma HasLIntegralMajorant.iSup {F : ℕ → α → ℝ≥0∞} (h_mono : Monotone F)
    (hF : ∀ n, HasLIntegralMajorant μ (F n)) :
    HasLIntegralMajorant μ (fun a ↦ ⨆ n, F n a) ∧
      ∫⁻ a, ⨆ n, F n a ∂μ = ⨆ n, ∫⁻ a, F n a ∂μ := by
  choose g hg hFg hF_eq using hF
  let G (n : ℕ) (a : α) : ℝ≥0∞ := ⨅ m ≥ n, g m a
  have hG (n : ℕ) : Measurable (G n) := .iInf fun m ↦ .iInf fun _ ↦ hg m
  have hG_mono : Monotone G := fun n n' hn a ↦ iInf₂_mono' fun m hm ↦ ⟨m, hn.trans hm, le_rfl⟩
  have hFG (n : ℕ) : F n ≤ G n := fun a ↦ le_iInf₂ fun m hm ↦ (h_mono hm a).trans (hFg m a)
  have h_le : ⨆ n, ∫⁻ a, F n a ∂μ ≤ ∫⁻ a, ⨆ n, F n a ∂μ :=
    iSup_le fun n ↦ lintegral_mono fun a ↦ le_iSup (fun n ↦ F n a) n
  have h_ge : ∫⁻ a, ⨆ n, F n a ∂μ ≤ ∫⁻ a, ⨆ n, G n a ∂μ :=
    lintegral_mono fun a ↦ iSup_mono fun n ↦ hFG n a
  have h_eq : ∫⁻ a, ⨆ n, G n a ∂μ = ⨆ n, ∫⁻ a, F n a ∂μ := by
    rw [lintegral_iSup hG hG_mono]
    refine le_antisymm (iSup_mono fun n ↦ ?_) (iSup_mono fun n ↦ lintegral_mono (hFG n))
    exact (lintegral_mono fun a ↦ iInf₂_le n le_rfl).trans_eq (hF_eq n).symm
  exact ⟨⟨fun a ↦ ⨆ n, G n a, .iSup hG, fun a ↦ iSup_mono fun n ↦ hFG n a,
    le_antisymm h_ge (h_eq.trans_le h_le)⟩, le_antisymm (h_ge.trans_eq h_eq) h_le⟩

/-- A countable sum of functions with measurable majorants with the same integrals has one, and its
integral is the sum of their integrals: the majorants bound it from above and measurable minorants
from below. -/
private lemma HasLIntegralMajorant.tsum {ι : Type*} [Countable ι] {F : ι → α → ℝ≥0∞}
    (hF : ∀ i, HasLIntegralMajorant μ (F i)) :
    HasLIntegralMajorant μ (fun a ↦ ∑' i, F i a) ∧
      ∫⁻ a, ∑' i, F i a ∂μ = ∑' i, ∫⁻ a, F i a ∂μ := by
  choose g hg hFg hF_eq using hF
  choose g' hg' hg'F hg'_eq using fun i ↦ exists_measurable_le_lintegral_eq (μ := μ) (F i)
  have h_eq : ∫⁻ a, ∑' i, F i a ∂μ = ∑' i, ∫⁻ a, F i a ∂μ := by
    refine le_antisymm ?_ ?_
    · calc ∫⁻ a, ∑' i, F i a ∂μ
      _ ≤ ∫⁻ a, ∑' i, g i a ∂μ :=
        lintegral_mono fun a ↦ ENNReal.tsum_le_tsum fun i ↦ hFg i a
      _ = ∑' i, ∫⁻ a, F i a ∂μ := by
        rw [lintegral_tsum fun i ↦ (hg i).aemeasurable]
        simp_rw [hF_eq]
    · calc ∑' i, ∫⁻ a, F i a ∂μ
      _ = ∫⁻ a, ∑' i, g' i a ∂μ := by
        rw [lintegral_tsum fun i ↦ (hg' i).aemeasurable]
        simp_rw [hg'_eq]
      _ ≤ ∫⁻ a, ∑' i, F i a ∂μ :=
        lintegral_mono fun a ↦ ENNReal.tsum_le_tsum fun i ↦ hg'F i a
  refine ⟨⟨fun a ↦ ∑' i, g i a, .tsum hg,
    fun a ↦ ENNReal.tsum_le_tsum fun i ↦ hFg i a, ?_⟩, h_eq⟩
  rw [h_eq, lintegral_tsum fun i ↦ (hg i).aemeasurable]
  simp_rw [hF_eq]

end Majorant

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
also supplies it when `μ` or `κ` is zero or when `μ` is a Dirac measure or counting measure on a
space with measurable singletons. Instance search passes it to finite and countable sums and to
multiples of measures, and to finite and countable sums of kernels. -/
class HasCompProd (μ : Measure α) (κ : Kernel α β) : Prop where
  /-- For every measurable set, the measures of its sections have a measurable majorant with the
  same integral. -/
  exists_measurable_ge_lintegral_eq ⦃s : Set (α × β)⦄ (hs : MeasurableSet s) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ (fun a ↦ κ a (Prod.mk a ⁻¹' s)) ≤ g ∧
      ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ = ∫⁻ a, g a ∂μ

/-- The measures of the sections of a measurable set have a measurable majorant with the same
integral. This restates the defining property of `HasCompProd`. -/
private lemma HasCompProd.hasLIntegralMajorant [μ.HasCompProd κ] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    HasLIntegralMajorant μ fun a ↦ κ a (Prod.mk a ⁻¹' s) :=
  HasCompProd.exists_measurable_ge_lintegral_eq hs

/-- The section integrals of the composition-product are countably additive: on a countable
disjoint union, measurable majorants bound them from above and measurable minorants from below. -/
lemma HasCompProd.lintegral_iUnion [μ.HasCompProd κ] ⦃f : ℕ → Set (α × β)⦄
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    ∫⁻ a, κ a (Prod.mk a ⁻¹' ⋃ i, f i) ∂μ = ∑' i, ∫⁻ a, κ a (Prod.mk a ⁻¹' f i) ∂μ := by
  have hsum (a : α) : κ a (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, κ a (Prod.mk a ⁻¹' f i) := by
    rw [preimage_iUnion, measure_iUnion (hd.mono fun _ _ ↦ .preimage _)
      fun i ↦ measurable_prodMk_left (hf i)]
  simp_rw [hsum]
  exact (HasLIntegralMajorant.tsum fun i ↦ HasCompProd.hasLIntegralMajorant (hf i)).2

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

/-- Against counting measure on a space with measurable singletons, the composition-product
with every kernel exists. A section integral is then a sum (`lintegral_count`): if it is infinite,
the constant `∞` is a majorant with the same integral, and otherwise the function
`a ↦ κ a (Prod.mk a ⁻¹' s)` has countable support, so it is measurable. -/
instance hasCompProd_count [MeasurableSingletonClass α] : (count : Measure α).HasCompProd κ where
  exists_measurable_ge_lintegral_eq s hs := by
    set f := fun a ↦ κ a (Prod.mk a ⁻¹' s)
    by_cases hf : ∑' a, f a = ∞
    · have : Nonempty α := by
        by_contra h
        rw [not_nonempty_iff] at h
        simp at hf
      refine ⟨fun _ ↦ ∞, measurable_const, fun _ ↦ le_top, ?_⟩
      rw [lintegral_count, hf, lintegral_const,
        ENNReal.top_mul (measure_univ_ne_zero.mpr count_ne_zero'')]
    · refine ⟨f, measurable_of_measurable_on_compl_countable _
        (Summable.countable_support_ennreal hf) ?_, le_rfl, rfl⟩
      have : (Function.support f)ᶜ.domRestrict f = fun _ ↦ 0 :=
        funext fun x ↦ Function.notMem_support.mp x.2
      rw [this]
      exact measurable_const

/-! ### Tonelli's theorem -/

section LIntegral

/-- Tonelli's theorem for a simple function, together with the majorant property of its section
integrals. -/
private lemma hasLIntegralMajorant_lintegral_simpleFunc [μ.HasCompProd κ]
    (f : SimpleFunc (α × β) ℝ≥0∞) :
    HasLIntegralMajorant μ (fun a ↦ ∫⁻ b, f (a, b) ∂κ a) ∧
      ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ = ∫⁻ x, f x ∂(μ ⊗ₘ κ) := by
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    simp +unfoldPartialApp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
      SimpleFunc.coe_const, SimpleFunc.coe_zero, Set.piecewise_eq_indicator, Function.const,
      lintegral_indicator_const hs]
    have h_sec (a : α) :
        ∫⁻ b, s.indicator (fun _ ↦ c) (a, b) ∂κ a = c * κ a (Prod.mk a ⁻¹' s) :=
      lintegral_indicator_const_comp measurable_prodMk_left hs c
    simp_rw [h_sec]
    have hmaj := HasCompProd.hasLIntegralMajorant (μ := μ) (κ := κ) hs
    exact ⟨hmaj.const_mul c, by rw [hmaj.lintegral_const_mul, compProd_apply hs]⟩
  | @add f g _ hf hg =>
    have h_sec (a : α) :
        ∫⁻ b, (f + g) (a, b) ∂κ a = ∫⁻ b, f (a, b) ∂κ a + ∫⁻ b, g (a, b) ∂κ a :=
      lintegral_add_left (f.measurable.comp measurable_prodMk_left) _
    simp_rw [h_sec]
    refine ⟨hf.1.add hg.1, ?_⟩
    rw [hf.1.lintegral_add, hf.2, hg.2, SimpleFunc.coe_add]
    exact (lintegral_add_left f.measurable _).symm

/-- Tonelli's theorem for a measurable function, together with the majorant property of its
section integrals: approximate it by an increasing sequence of simple functions. -/
private lemma hasLIntegralMajorant_lintegral [μ.HasCompProd κ] {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    HasLIntegralMajorant μ (fun a ↦ ∫⁻ b, f (a, b) ∂κ a) ∧
      ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ = ∫⁻ x, f x ∂(μ ⊗ₘ κ) := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox f
  have hF_mono : Monotone fun n ↦ (F n : α × β → ℝ≥0∞) := SimpleFunc.monotone_eapprox f
  have hF_sup (x : α × β) : ⨆ n, F n x = f x := SimpleFunc.iSup_eapprox_apply hf x
  have h_sec (a : α) : ∫⁻ b, f (a, b) ∂κ a = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    simp_rw [← hF_sup]
    exact lintegral_iSup (fun n ↦ (F n).measurable.comp measurable_prodMk_left)
      fun n m hnm b ↦ hF_mono hnm _
  have h_int : ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ⨆ n, ∫⁻ x, F n x ∂(μ ⊗ₘ κ) := by
    simp_rw [← hF_sup]
    exact lintegral_iSup (fun n ↦ (F n).measurable) hF_mono
  obtain ⟨hmaj, hint⟩ := HasLIntegralMajorant.iSup (μ := μ)
    (F := fun n a ↦ ∫⁻ b, F n (a, b) ∂κ a)
    (fun n m hnm a ↦ lintegral_mono fun b ↦ hF_mono hnm _)
    fun n ↦ (hasLIntegralMajorant_lintegral_simpleFunc (F n)).1
  simp_rw [h_sec]
  refine ⟨hmaj, ?_⟩
  rw [hint, h_int]
  exact iSup_congr fun n ↦ (hasLIntegralMajorant_lintegral_simpleFunc (F n)).2

/-- The section integrals of a measurable function have a measurable majorant with the same
integral, as the measures of the sections of a measurable set do by the definition of
`MeasureTheory.Measure.HasCompProd`. -/
theorem HasCompProd.exists_measurable_ge_lintegral_lintegral_eq [μ.HasCompProd κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ (fun a ↦ ∫⁻ b, f (a, b) ∂κ a) ≤ g ∧
      ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ = ∫⁻ a, g a ∂μ :=
  (hasLIntegralMajorant_lintegral hf).1

/-- **Tonelli's theorem** for the composition-product, on its whole domain `μ.HasCompProd κ`: the
integral of a measurable function against `μ ⊗ₘ κ` is the integral of its section integrals.
Neither `μ` nor `κ` has to be s-finite. -/
theorem lintegral_compProd [μ.HasCompProd κ] {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ :=
  (hasLIntegralMajorant_lintegral hf).2.symm

/-- For a function that need not be measurable, the integral against `μ ⊗ₘ κ` is at most the
iterated integral: Tonelli's theorem applies to a measurable minorant with the same integral. -/
theorem lintegral_compProd_le [μ.HasCompProd κ] (f : α × β → ℝ≥0∞) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) ≤ ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ := by
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ := μ ⊗ₘ κ) f
  rw [hfg, lintegral_compProd hg]
  exact lintegral_mono fun a ↦ lintegral_mono fun b ↦ hgf (a, b)

/-- **Tonelli's theorem** for a function that need not be measurable but has a measurable majorant
with the same integral against `μ ⊗ₘ κ`. -/
theorem lintegral_compProd_of_exists_measurable_ge [μ.HasCompProd κ] {f : α × β → ℝ≥0∞}
    (hf : ∃ g : α × β → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ x, g x ∂(μ ⊗ₘ κ)) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ := by
  obtain ⟨g, hg, hfg, h_eq⟩ := hf
  refine le_antisymm (lintegral_compProd_le f) ?_
  calc ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ
  _ ≤ ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂μ := lintegral_mono fun a ↦ lintegral_mono fun b ↦ hfg (a, b)
  _ = ∫⁻ x, f x ∂(μ ⊗ₘ κ) := by rw [← lintegral_compProd hg, h_eq]

/-- **Tonelli's theorem** for the composition-product on a measurable rectangle. -/
theorem setLIntegral_compProd [μ.HasCompProd κ] {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [← lintegral_indicator (hs.prod ht), lintegral_compProd (hf.indicator (hs.prod ht)),
    ← lintegral_indicator hs]
  congr with a
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    rw [← lintegral_indicator ht]
    congr with b
    by_cases hb : b ∈ t <;> simp [Set.indicator, ha, hb]
  · simp [Set.indicator, ha]

end LIntegral

/-! ### Additivity in each argument -/

section Add

/-- The composition-product of a sum of measures exists when it exists for each of them: the
pointwise minimum of their majorants is a majorant for the sum. -/
instance hasCompProd_add_left [μ.HasCompProd κ] [ν.HasCompProd κ] : (μ + ν).HasCompProd κ where
  exists_measurable_ge_lintegral_eq s hs := by
    obtain ⟨g₁, hg₁, hle₁, heq₁⟩ := HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ)
      (κ := κ) hs
    obtain ⟨g₂, hg₂, hle₂, heq₂⟩ := HasCompProd.exists_measurable_ge_lintegral_eq (μ := ν)
      (κ := κ) hs
    refine ⟨fun a ↦ min (g₁ a) (g₂ a), hg₁.min hg₂, fun a ↦ le_min (hle₁ a) (hle₂ a),
      le_antisymm (lintegral_mono fun a ↦ le_min (hle₁ a) (hle₂ a)) ?_⟩
    rw [lintegral_add_measure, lintegral_add_measure, heq₁, heq₂]
    exact add_le_add (lintegral_mono fun a ↦ min_le_left _ _)
      (lintegral_mono fun a ↦ min_le_right _ _)

/-- The composition-product of a multiple of a measure exists when it exists for the measure. -/
instance hasCompProd_smul_left {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    [μ.HasCompProd κ] : (c • μ).HasCompProd κ where
  exists_measurable_ge_lintegral_eq s hs := by
    obtain ⟨g, hg, hle, heq⟩ := HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ) (κ := κ) hs
    exact ⟨g, hg, hle, by rw [lintegral_smul_measure, lintegral_smul_measure, heq]⟩

/-- The composition-product of a countable sum of measures exists when it exists for each of them:
the pointwise infimum of their majorants is a majorant for the sum.

The domain is not closed under uncountable sums (paper proof). For a set `T ⊆ ℝ` that is not
Borel, every `dirac t` has a composition-product with the constant kernel of `Σ_{u ∉ T} dirac u`
(`hasCompProd_dirac`). Against `Σ_{t ∈ T} dirac t`, the measures of the sections of the diagonal
form the indicator of `Tᶜ`, whose integral is `0`; a measurable majorant with integral `0` would
vanish on `T` and be at least `1` off `T`, which would make `T` Borel. -/
instance hasCompProd_sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α}
    [∀ i, (μ i).HasCompProd κ] : (sum μ).HasCompProd κ where
  exists_measurable_ge_lintegral_eq s hs := by
    choose g hg hle heq using fun i ↦
      HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ i) (κ := κ) hs
    refine ⟨fun a ↦ ⨅ i, g i a, .iInf hg, fun a ↦ le_iInf fun i ↦ hle i a,
      le_antisymm (lintegral_mono fun a ↦ le_iInf fun i ↦ hle i a) ?_⟩
    rw [lintegral_sum_measure, lintegral_sum_measure]
    exact ENNReal.tsum_le_tsum fun i ↦ (lintegral_mono fun a ↦ iInf_le _ i).trans_eq (heq i).symm

/-- The composition-product with a sum of kernels exists when it exists for each of them. -/
instance hasCompProd_add_right [μ.HasCompProd κ] [μ.HasCompProd η] : μ.HasCompProd (κ + η) where
  exists_measurable_ge_lintegral_eq s hs := by
    have h := (HasCompProd.hasLIntegralMajorant (μ := μ) (κ := κ) hs).add
      (HasCompProd.hasLIntegralMajorant (μ := μ) (κ := η) hs)
    simpa only [HasLIntegralMajorant, Measure.add_apply, FunLike.coe_add, Pi.add_apply] using h

/-- The composition-product with a countable sum of kernels exists when it exists for each of
them. -/
instance hasCompProd_sum_right {ι : Type*} [Countable ι] {κ : ι → Kernel α β}
    [∀ i, μ.HasCompProd (κ i)] : μ.HasCompProd (Kernel.sum κ) where
  exists_measurable_ge_lintegral_eq s hs := by
    have h := (HasLIntegralMajorant.tsum fun i ↦
      HasCompProd.hasLIntegralMajorant (μ := μ) (κ := κ i) hs).1
    simpa only [HasLIntegralMajorant, Kernel.sum_apply' _ _ (measurable_prodMk_left hs)] using h

lemma compProd_add_left (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd κ] :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ := by
  ext s hs
  simp [compProd_apply hs]

/-- The composition-product is additive in the measure. Instance search supplies the domain of the
composition-product with the sum for a countable family; for an uncountable one it does not follow
from the domains of the summands (`hasCompProd_sum_left`), so it is an assumption. -/
lemma compProd_sum_left {ι : Type*} {μ : ι → Measure α} [∀ i, (μ i).HasCompProd κ]
    [(sum μ).HasCompProd κ] :
    (sum μ) ⊗ₘ κ = sum (fun i ↦ (μ i) ⊗ₘ κ) := by
  ext s hs
  rw [compProd_apply hs, Measure.sum_apply _ hs, lintegral_sum_measure]
  simp_rw [compProd_apply hs]

lemma compProd_smul_left {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    [μ.HasCompProd κ] :
    (c • μ) ⊗ₘ κ = c • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply]

lemma compProd_add_right (μ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ]
    [μ.HasCompProd η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η := by
  ext s hs
  simp only [compProd_apply hs, Measure.add_apply, FunLike.coe_add, Pi.add_apply]
  exact (HasCompProd.hasLIntegralMajorant (μ := μ) (κ := κ) hs).lintegral_add _

lemma compProd_sum_right {ι : Type*} [Countable ι] {κ : ι → Kernel α β}
    [∀ i, μ.HasCompProd (κ i)] :
    μ ⊗ₘ (Kernel.sum κ) = sum (fun i ↦ μ ⊗ₘ (κ i)) := by
  ext s hs
  rw [compProd_apply hs, Measure.sum_apply _ hs]
  simp_rw [compProd_apply hs, Kernel.sum_apply' _ _ (measurable_prodMk_left hs)]
  exact (HasLIntegralMajorant.tsum fun i ↦
    HasCompProd.hasLIntegralMajorant (μ := μ) (κ := κ i) hs).2

end Add

/-! ### Rectangles -/

/-- Against a constant kernel, the composition-product gives a rectangle the product of the measures
of its sides, also when they are not measurable. A measurable set containing the rectangle has
sections of measure at least `ν t` over `s`, so a majorant of their measures with the same integral
is at least `ν t` on a measurable set containing `s`. -/
lemma compProd_const_apply_prod {ν : Measure β} [μ.HasCompProd (Kernel.const α ν)] (s : Set α)
    (t : Set β) :
    (μ ⊗ₘ Kernel.const α ν) (s ×ˢ t) = μ s * ν t := by
  classical
  refine le_antisymm ?_ ?_
  · have hS := measurableSet_toMeasurable μ s
    have hT := measurableSet_toMeasurable ν t
    calc (μ ⊗ₘ Kernel.const α ν) (s ×ˢ t)
    _ ≤ (μ ⊗ₘ Kernel.const α ν) (toMeasurable μ s ×ˢ toMeasurable ν t) :=
      measure_mono (Set.prod_mono (subset_toMeasurable _ _) (subset_toMeasurable _ _))
    _ = ∫⁻ a, (toMeasurable μ s).indicator (fun _ ↦ ν (toMeasurable ν t)) a ∂μ := by
      rw [compProd_apply (hS.prod hT)]
      congr with a
      by_cases ha : a ∈ toMeasurable μ s <;> simp [ha]
    _ = μ s * ν t := by rw [lintegral_indicator_const hS, measure_toMeasurable,
      measure_toMeasurable, mul_comm]
  · set M := toMeasurable (μ ⊗ₘ Kernel.const α ν) (s ×ˢ t)
    have hM : MeasurableSet M := measurableSet_toMeasurable _ _
    obtain ⟨g, hg, hle, heq⟩ :=
      HasCompProd.exists_measurable_ge_lintegral_eq (μ := μ) (κ := Kernel.const α ν) hM
    have hS : MeasurableSet {a | ν t ≤ g a} := measurableSet_le measurable_const hg
    have hs : s ⊆ {a | ν t ≤ g a} := fun a ha ↦ by
      have h_sub : t ⊆ Prod.mk a ⁻¹' M := fun b hb ↦
        subset_toMeasurable _ _ (Set.mk_mem_prod ha hb)
      exact (measure_mono h_sub : ν t ≤ ν (Prod.mk a ⁻¹' M)).trans (hle a)
    calc μ s * ν t
    _ ≤ μ {a | ν t ≤ g a} * ν t := by gcongr
    _ = ∫⁻ a, {a | ν t ≤ g a}.indicator (fun _ ↦ ν t) a ∂μ := by
      rw [lintegral_indicator_const hS, mul_comm]
    _ ≤ ∫⁻ a, g a ∂μ := lintegral_mono fun a ↦ by
      by_cases ha : ν t ≤ g a <;> simp [Set.indicator, ha]
    _ = (μ ⊗ₘ Kernel.const α ν) (s ×ˢ t) := by
      rw [← heq, ← compProd_apply hM, measure_toMeasurable]

end MeasureTheory.Measure

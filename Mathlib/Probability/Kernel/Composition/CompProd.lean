/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd.Defs

/-!
# Composition-product of kernels

We define the composition-product `κ ⊗ₖ η` of two kernels `κ : Kernel α β` and
`η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`: `(κ ⊗ₖ η) a` integrates the measures
`η (a, b)` of the sections against `κ a`. These section integrals determine at most one kernel.
The class `HasCompProd κ η` says that they define one; it is the domain of `κ ⊗ₖ η`, and instance
search derives it from the s-finiteness of both kernels.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

* `HasCompProd κ η`: the composition-product of `κ` and `η` exists.
* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  kernels. We define a notation `κ ⊗ₖ η = compProd κ η`. On its whole domain, for measurable `f`,
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`

## Main statements

* `lintegral_compProd`: Lebesgue integral of a function against a composition-product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition-product.

## Notation

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`.
-/

variable {s : Set (β × γ)}

/-- The composition-product of `κ` and `η` exists: at every point `a`, the composition-product of
the measure `κ a` with the kernel `sectR η a = fun b ↦ η (a, b)` exists, and its values on
measurable sets depend measurably on `a`. Then the section integrals
`∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a` are the values of a unique kernel.

This is the exact domain of `ProbabilityTheory.Kernel.compProd`. Instance search derives it from
the s-finiteness of both kernels, supplies it when either kernel is zero, and passes it to finite
and countable sums of `κ`. -/
class HasCompProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Prop where
  /-- At every point `a`, the composition-product of `κ a` with `sectR η a` exists. -/
  hasCompProd_apply (a : α) : (κ a).HasCompProd (sectR η a)
  /-- The section integrals of a measurable set depend measurably on the point. -/
  measurable_lintegral ⦃s : Set (β × γ)⦄ (hs : MeasurableSet s) :
    Measurable fun a ↦ ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a

attribute [instance] HasCompProd.hasCompProd_apply

/-- Composition-Product of kernels: `(κ ⊗ₖ η) a` integrates the measures `η (a, b)` of the sections
against `κ a`, that is, `(κ ⊗ₖ η) a = κ a ⊗ₘ sectR η a`. Its domain is `HasCompProd κ η`, on which
it satisfies, for measurable `f`,
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.Kernel.lintegral_compProd`). -/
noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ)
    [κ.HasCompProd η] : Kernel α (β × γ) :=
  { toFun a := κ a ⊗ₘ sectR η a
    measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
      simpa only [Measure.compProd_apply hs, sectR_apply] using
        HasCompProd.measurable_lintegral hs }

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₖ " => ProbabilityTheory.Kernel.compProd

lemma compProd_apply_eq_compProd_sectR (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η]
    (a : α) :
    (κ ⊗ₖ η) a = κ a ⊗ₘ sectR η a := by
  rw [compProd, coe_mk]

theorem compProd_apply (hs : MeasurableSet s) (κ : Kernel α β) (η : Kernel (α × β) γ)
    [κ.HasCompProd η] (a : α) :
    (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a := by
  simp [compProd_apply_eq_compProd_sectR, Measure.compProd_apply hs]

/-- Composition-products of s-finite kernels exist. -/
instance {κ : Kernel α β} {η : Kernel (α × β) γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ.HasCompProd η where
  hasCompProd_apply _ := inferInstance
  measurable_lintegral s hs := by
    have : Measurable fun p : α × β ↦ η p (Prod.mk p.2 ⁻¹' s) :=
      measurable_kernel_prodMk_left (κ := η) (t := {p : (α × β) × γ | (p.1.2, p.2) ∈ s})
        (measurable_fst.snd.prodMk measurable_snd hs)
    exact this.lintegral_kernel_prod_right'

instance (η : Kernel (α × β) γ) : (0 : Kernel α β).HasCompProd η where
  hasCompProd_apply _ := by rw [zero_apply]; infer_instance
  measurable_lintegral _ _ := by simp

instance (κ : Kernel α β) : κ.HasCompProd (0 : Kernel (α × β) γ) where
  hasCompProd_apply _ := by rw [sectR_zero]; infer_instance
  measurable_lintegral _ _ := by simp

theorem le_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α)
    (s : Set (β × γ)) :
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤ (κ ⊗ₖ η) a s :=
  calc
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤
        ∫⁻ b, η (a, b) {c | (b, c) ∈ toMeasurable ((κ ⊗ₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ ⊗ₖ η) a (toMeasurable ((κ ⊗ₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s

@[simp]
lemma compProd_apply_univ {κ : Kernel α β} {η : Kernel (α × β) γ}
    [κ.HasCompProd η] [IsMarkovKernel η] {a : α} :
    (κ ⊗ₖ η) a Set.univ = κ a Set.univ := by
  rw [compProd_apply MeasurableSet.univ]
  simp

lemma compProd_apply_prod {κ : Kernel α β} {η : Kernel (α × β) γ} [κ.HasCompProd η] {a : α}
    {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (κ ⊗ₖ η) a (s ×ˢ t) = ∫⁻ b in s, η (a, b) t ∂(κ a) := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with a
  by_cases ha : a ∈ s <;> simp [ha]

lemma compProd_congr {κ : Kernel α β} {η η' : Kernel (α × β) γ}
    [κ.HasCompProd η] [κ.HasCompProd η'] (h : ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = η' (a, b)) :
    κ ⊗ₖ η = κ ⊗ₖ η' := by
  ext a s hs
  rw [compProd_apply hs, compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]
lemma compProd_zero_left (κ : Kernel (α × β) γ) :
    (0 : Kernel α β) ⊗ₖ κ = 0 := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp

@[simp]
lemma compProd_zero_right (κ : Kernel α β) (γ : Type*) {mγ : SigmaAlgebra γ} :
    κ ⊗ₖ (0 : Kernel (α × β) γ) = 0 := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp

lemma compProd_eq_zero_iff {κ : Kernel α β} {η : Kernel (α × β) γ} [κ.HasCompProd η] :
    κ ⊗ₖ η = 0 ↔ ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a ↦ (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h

lemma compProd_preimage_fst {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β)
    (η : Kernel (α × β) γ) [κ.HasCompProd η] [IsMarkovKernel η] (x : α) :
    (κ ⊗ₖ η) x (Prod.fst ⁻¹' s) = κ x s := by
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

lemma compProd_deterministic_apply [MeasurableSingletonClass γ] {f : α × β → γ} (hf : Measurable f)
    {s : Set (β × γ)} (hs : MeasurableSet s) (κ : Kernel α β) [κ.HasCompProd (deterministic f hf)]
    (x : α) :
    (κ ⊗ₖ deterministic f hf) x s = κ x {b | (b, f (x, b)) ∈ s} := by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) ∈ s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert! add_zero _
  · suffices ∀ b ∈ tᶜ, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this, lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_ofPred_eq] at hb
    simp [hb]
  · suffices ∀ b ∈ t, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this, setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_ofPred_eq] at hb
    simp [hb]

section Ae

/-! ### `ae` filter of the composition-product -/


variable {κ : Kernel α β} {η : Kernel (α × β) γ} [κ.HasCompProd η] {a : α}

theorem ae_kernel_lt_top (a : α) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞ := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  have : ∀ b : β, η (a, b) (Prod.mk b ⁻¹' s) ≤ η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ ⊗ₖ η) a t ≠ ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    obtain ⟨g, hg, hfg, hg_eq⟩ := (HasCompProd.hasCompProd_apply (κ := κ) (η := η) a)
      |>.exists_measurable_ge_lintegral_eq ht
    filter_upwards [ae_lt_top hg (hg_eq.symm.trans_ne h2t)] with b hb using (hfg b).trans_lt hb
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb

theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [Kernel.compProd_apply hs]
  exact Measure.HasCompProd.lintegral_eq_zero_iff (κ := sectR η a) hs

theorem ae_null_of_compProd_null (h : (κ ⊗ₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le⟩

theorem ae_ae_of_ae_compProd {p : β × γ → Prop} (h : ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h

lemma ae_compProd_of_ae_ae {p : β × γ → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c)) :
    ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc := by
  rw [ae_iff, compProd_null a (show MeasurableSet {bc | ¬p bc} from hp.compl)]
  exact h.mono fun _ hb ↦ ae_iff.mp hb

lemma ae_compProd_iff {p : β × γ → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) ↔ ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ⟨fun h ↦ ae_ae_of_ae_compProd h, fun h ↦ ae_compProd_of_ae_ae hp h⟩

end Ae

section Restrict

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

theorem compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Kernel.restrict κ hs ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (hs.prod ht) := by
  ext a u hu
  rw [compProd_apply hu, restrict_apply' _ _ _ hu, compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) ∈ u ∧ b ∈ s ∧ c ∈ t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) ∈ u} ∩ t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_ofPred]
    · simp only [h, false_and, and_false, Set.ofPred_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]

theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    Kernel.restrict κ hs ⊗ₖ η = Kernel.restrict (κ ⊗ₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm

theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

end Restrict

section Lintegral

/-! ### Lebesgue integral -/


/-- **Tonelli's theorem** for the composition-product of two kernels, on its whole domain: this is
`MeasureTheory.Measure.lintegral_compProd` for `κ a ⊗ₘ sectR η a`. -/
theorem lintegral_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α)
    {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  rw [compProd_apply_eq_compProd_sectR]
  exact Measure.lintegral_compProd hf

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd' (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α)
    {f : β → γ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    ∫⁻ bc, f bc.1 bc.2 ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (a, b) ∂κ a :=
  lintegral_compProd κ η a hf

/-- Lebesgue integral against the composition-product of two kernels. -/
theorem lintegral_compProd₀ (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α)
    {f : β × γ → ℝ≥0∞} (hf : AEMeasurable f ((κ ⊗ₖ η) a)) :
    ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  have A : ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ z, hf.mk f z ∂(κ ⊗ₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_compProd]
  exact hf.measurable_mk

theorem setLIntegral_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α)
    {f : β × γ → ℝ≥0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  rw [compProd_apply_eq_compProd_sectR]
  exact Measure.setLIntegral_compProd hf hs ht

theorem setLIntegral_compProd_univ_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    [κ.HasCompProd η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

theorem setLIntegral_compProd_univ_left (κ : Kernel α β) (η : Kernel (α × β) γ)
    [κ.HasCompProd η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

end Lintegral

theorem compProd_eq_sum_compProd_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] :
    κ ⊗ₖ η = Kernel.sum fun n ↦ seq κ n ⊗ₖ η := by
  ext a s hs
  simp_rw [sum_apply' _ _ hs, compProd_apply hs]
  conv_lhs => rw [← kernel_sum_seq κ]
  rw [sum_apply, lintegral_sum_measure]

theorem compProd_eq_sum_compProd_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n => κ ⊗ₖ seq η n := by
  ext a s hs
  simp_rw [sum_apply' _ _ hs, compProd_apply hs]
  conv_lhs => rw [← kernel_sum_seq η]
  simp_rw [sum_apply' _ _ (measurable_prodMk_left hs)]
  exact lintegral_tsum fun n ↦ (measurable_kernel_prodMk_left' hs a).aemeasurable

theorem compProd_eq_sum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n ↦ Kernel.sum fun m ↦ seq κ n ⊗ₖ seq η m := by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]

theorem compProd_eq_tsum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∑' (n : ℕ) (m : ℕ), (seq κ n ⊗ₖ seq η m) a s := by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]

instance IsMarkovKernel.compProd (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η) where
  isProbabilityMeasure a := ⟨by simp [compProd_apply]⟩

instance IsZeroOrMarkovKernel.compProd (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel (α × β) γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ⊗ₖ η) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

theorem compProd_apply_univ_le (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α) :
    (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * η.bound := by
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

instance IsFiniteKernel.compProd (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ⊗ₖ η) := by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a ↦ ?_⟩⟩
  calc (κ ⊗ₖ η) a Set.univ
  _ ≤ κ a Set.univ * η.bound := compProd_apply_univ_le κ η a
  _ ≤ κ.bound * η.bound := by
    gcongr
    exact measure_le_bound κ a Set.univ

instance IsSFiniteKernel.compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : IsSFiniteKernel (κ ⊗ₖ η) := by
  rw [compProd_eq_sum_compProd]
  infer_instance

/-- `Kernel.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc` in two places
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
lemma compProd_assoc {δ : Type*} {mδ : SigmaAlgebra δ}
    {κ : Kernel α β} {η : Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ξ] :
    (κ ⊗ₖ (η ⊗ₖ (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map
        MeasurableEquiv.prodAssoc.symm
      = κ ⊗ₖ η ⊗ₖ ξ := by
  ext a s hs
  rw [compProd_apply hs, map_apply' _ _ hs (by fun_prop),
    compProd_apply (hs.preimage (by fun_prop)), lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

/-- The composition-product of a sum of kernels with `η` exists when it exists for each of them. -/
instance hasCompProd_add_left {κ κ' : Kernel α β} {η : Kernel (α × β) γ} [κ.HasCompProd η]
    [κ'.HasCompProd η] : (κ + κ').HasCompProd η where
  hasCompProd_apply a := by rw [add_apply]; infer_instance
  measurable_lintegral s hs := by
    simp_rw [add_apply, lintegral_add_measure]
    exact (HasCompProd.measurable_lintegral (κ := κ) hs).add
      (HasCompProd.measurable_lintegral (κ := κ') hs)

/-- The composition-product of a countable sum of kernels with `η` exists when it exists for each of
them. -/
instance hasCompProd_sum_left {ι : Type*} [Countable ι] {κ : ι → Kernel α β}
    {η : Kernel (α × β) γ} [∀ i, (κ i).HasCompProd η] : (Kernel.sum κ).HasCompProd η where
  hasCompProd_apply a := by rw [sum_apply]; infer_instance
  measurable_lintegral s hs := by
    simp_rw [sum_apply, lintegral_sum_measure]
    exact .tsum fun i ↦ HasCompProd.measurable_lintegral (κ := κ i) hs

lemma compProd_add_left (μ κ : Kernel α β) (η : Kernel (α × β) γ)
    [μ.HasCompProd η] [κ.HasCompProd η] :
    (μ + κ) ⊗ₖ η = μ ⊗ₖ η + κ ⊗ₖ η := by
  ext _ _ hs
  simp [compProd_apply hs]

lemma compProd_add_right (μ : Kernel α β) (κ η : Kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₖ (κ + η) = μ ⊗ₖ κ + μ ⊗ₖ η := by
  ext a s hs
  simp only [compProd_apply hs, FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a

lemma compProd_sum_left {ι : Type*} [Countable ι]
    {κ : ι → Kernel α β} {η : Kernel (α × β) γ} [∀ i, (κ i).HasCompProd η] :
    Kernel.sum κ ⊗ₖ η = Kernel.sum (fun i ↦ (κ i) ⊗ₖ η) := by
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]

lemma compProd_sum_right {ι : Type*} [Countable ι]
    {κ : Kernel α β} {η : ι → Kernel (α × β) γ} [IsSFiniteKernel κ] [∀ i, IsSFiniteKernel (η i)] :
    κ ⊗ₖ Kernel.sum η = Kernel.sum (fun i ↦ κ ⊗ₖ (η i)) := by
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ ↦ (measurable_kernel_prodMk_left' hs a).aemeasurable

lemma comapRight_compProd_id_prod {δ : Type*} {mδ : SigmaAlgebra δ}
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η]
    {f : δ → γ} (hf : MeasurableEmbedding f) :
    comapRight (κ ⊗ₖ η) (MeasurableEmbedding.id.prodMap hf) = κ ⊗ₖ (comapRight η hf) := by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht, compProd_apply, compProd_apply ht]
  · refine lintegral_congr fun b ↦ ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

end CompositionProduct

open scoped ProbabilityTheory

section FstSnd

/-- If `η` is a Markov kernel, use instead `fst_compProd` to get `(κ ⊗ₖ η).fst = κ`. -/
lemma fst_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (x : α)
    {s : Set β} (hs : MeasurableSet s) :
    (κ ⊗ₖ η).fst x s = ∫⁻ b, s.indicator (fun b ↦ η (x, b) Set.univ) b ∂(κ x) := by
  rw [Kernel.fst_apply' _ _ hs, Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b ∈ s} = s.indicator (fun b ↦ η (x, b) Set.univ) b := by
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_ofPred_eq, h_eq]

@[simp]
lemma fst_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs; simp [fst_compProd_apply, hs]

end FstSnd

end Kernel
end ProbabilityTheory

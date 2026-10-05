/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Product and composition of kernels

We define the product `κ ×ₖ η` of kernels `κ : Kernel α β` and `η : Kernel α γ`, which is a kernel
from `α` to `β × γ`: the composition-product of `κ` with `η` regarded as a kernel from `α × β` that
ignores its second coordinate. Instance search supplies its domain for s-finite kernels.

## Main definitions

* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 kernels. On its whole
  domain, for measurable `f`, `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_prod`: Lebesgue integral of a function against a product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by product.

## Notation

* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}

variable {γ δ : Type*} {mγ : SigmaAlgebra γ} {mδ : SigmaAlgebra δ}

/-- The product of `κ` and the zero kernel exists. -/
instance (κ : Kernel α β) : κ.HasCompProd (prodMkRight β (0 : Kernel α γ)) := by
  rw [prodMkRight_zero]
  infer_instance

/-- Product of two kernels: the composition-product of `κ` with `η` regarded as a kernel from
`α × β` that ignores its second coordinate, so that `(κ ×ₖ η) a` integrates the `η a`-measures of
the sections against `κ a`. Its domain is `κ.HasCompProd (prodMkRight β η)`, which instance search
derives from the s-finiteness of both kernels. -/
noncomputable def prod (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (prodMkRight β η)] :
    Kernel α (β × γ) :=
  κ ⊗ₖ prodMkRight β η

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod

@[simp]
lemma zero_prod (η : Kernel α γ) : (0 : Kernel α β) ×ₖ η = 0 := by simp [prod]

@[simp]
lemma prod_zero (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0 := by simp [prod]

theorem prod_apply' (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (prodMkRight β η)]
    (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) (Prod.mk b ⁻¹' s) ∂κ a := by
  rw [prod, compProd_apply hs]
  rfl

/-- Equal factors give equal products, whichever evidence for their domains is used. -/
lemma prod_congr {κ κ' : Kernel α β} {η η' : Kernel α γ} [κ.HasCompProd (prodMkRight β η)]
    [κ'.HasCompProd (prodMkRight β η')] (hκ : κ = κ') (hη : η = η') : κ ×ₖ η = κ' ×ₖ η' := by
  subst hκ hη
  rfl

lemma parallelComp_comp_copy (κ : Kernel α β) (η : Kernel α γ) [κ.HasParallelComp η]
    [κ.HasCompProd (prodMkRight β η)] :
    (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, copy_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs),
    parallelComp_apply' hs, prod_apply' _ _ _ hs]

lemma prod_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).productBySections (η a) (hasAEMeasurableSectionMeasures_of_sfinite _ _) := by
  ext s hs
  rw [prod_apply' _ _ _ hs,
    Measure.productBySections_apply (ν := η a) hs]

/-- The product of kernels gives a rectangle the product of the measures of its sides, also when
they are not measurable. -/
lemma prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [κ.HasCompProd (prodMkRight β η)] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  have : (κ a).HasCompProd (const β (η a)) :=
    HasCompProd.hasCompProd_apply (κ := κ) (η := prodMkRight β η) a
  rw [prod, compProd_apply_eq_compProd_sectR]
  exact Measure.compProd_const_apply_prod (μ := κ a) (ν := η a) s t

lemma prod_const (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν] :
    const α μ ×ₖ const α ν = const α (μ.productBySections ν) := by
  ext x s hs
  rw [prod_apply' _ _ _ hs, const_apply, const_apply, const_apply,
    Measure.productBySections_apply hs]

/-- **Tonelli's theorem** for the product of kernels, on its whole domain. -/
theorem lintegral_prod (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (prodMkRight β η)]
    (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  rw [prod]
  exact lintegral_compProd κ (prodMkRight β η) a hg

theorem lintegral_prod_symm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ c, ∫⁻ b, g (b, c) ∂κ a ∂η a := by
  rw [prod_apply, MeasureTheory.lintegral_productBySections_symm _ hg.aemeasurable]

theorem lintegral_deterministic_prod {f : α → β} (hf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂((deterministic f hf) ×ₖ κ) a = ∫⁻ c, g (f a, c) ∂κ a := by
  rw [lintegral_prod _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_right']

theorem lintegral_prod_deterministic {f : α → γ} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂(κ ×ₖ (deterministic f hf)) a = ∫⁻ b, g (b, f a) ∂κ a := by
  rw [lintegral_prod_symm _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_left']

theorem lintegral_id_prod {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) :
    ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a = ∫⁻ b, f (a, b) ∂κ a :=
  lintegral_deterministic_prod measurable_id κ a hf

theorem lintegral_prod_id {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel β α)
    [IsSFiniteKernel κ] (b : β) :
    ∫⁻ p, f p ∂(κ ×ₖ Kernel.id) b = ∫⁻ a, f (a, b) ∂κ b :=
  lintegral_prod_deterministic measurable_id κ b hf

theorem deterministic_prod_apply' {f : α → β} (mf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ κ) a s = κ a (Prod.mk (f a) ⁻¹' s) := by
  rw [prod_apply' _ _ _ hs, lintegral_deterministic']
  exact measurable_measure_prodMk_left hs

theorem id_prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × β)}
    (hs : MeasurableSet s) : (Kernel.id ×ₖ κ) a s = κ a (Prod.mk a ⁻¹' s) :=
  deterministic_prod_apply' measurable_id κ a hs

instance IsMarkovKernel.prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod]; infer_instance
  rcases eq_zero_or_isMarkovKernel η with rfl | h'
  · simp only [prod]; infer_instance
  infer_instance

instance IsFiniteKernel.prod (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

instance IsSFiniteKernel.prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] : IsSFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

@[simp] lemma fst_prod (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (prodMkRight β η)]
    [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, show {p : β × γ | p.1 ∈ s} = s ×ˢ Set.univ by ext; simp, prod_apply_prod,
    measure_univ, mul_one]

@[simp] lemma snd_prod (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (prodMkRight β η)]
    [IsMarkovKernel κ] :
    snd (κ ×ₖ η) = η := by
  ext a t ht
  rw [snd_apply' _ _ ht, ← Set.univ_prod, prod_apply_prod, measure_univ, one_mul]

lemma comap_prod (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (κ ×ₖ η).comap f hf = (κ.comap f hf) ×ₖ (η.comap f hf) := by
  ext x s hs
  rw [comap_apply' _ hf _ s, prod_apply' _ _ _ hs, prod_apply' _ _ _ hs]
  rfl

lemma map_prod_map {ε} {mε : SigmaAlgebra ε} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α δ) [IsSFiniteKernel η] {f : β → γ} (hf : Measurable f) {g : δ → ε}
    (hg : Measurable g) : (κ.map f) ×ₖ (η.map g) = (κ ×ₖ η).map (Prod.map f g) := by
  ext1 x
  simpa only [map_apply, prod_apply] using Measure.map_productBySections_map (κ x) (η x) hf hg

lemma map_prod_eq (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    {f : β → δ} (hf : Measurable f) : (κ.map f) ×ₖ η = (κ ×ₖ η).map (Prod.map f id) := by
  simpa only [map_id] using map_prod_map κ η hf measurable_id

lemma comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap, lintegral_map _ measurable_swap _ hf, lintegral_prod _ _ _ hf,
    lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

lemma map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf, lintegral_prod, lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

lemma prodComm_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (κ ×ₖ η).map MeasurableEquiv.prodComm = η ×ₖ κ :=
  map_prod_swap κ η

@[simp]
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  rw [swap_comp_eq_map, map_prod_swap]

lemma deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prodMk hg) := by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_productBySections_dirac]

lemma id_prod_eq : @Kernel.id (α × β) inferInstance =
    (deterministic Prod.fst measurable_fst) ×ₖ (deterministic Prod.snd measurable_snd) := by
  rw [deterministic_prod_deterministic]
  rfl

lemma prodAssoc_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    ((κ ×ₖ ξ) ×ₖ η).map MeasurableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η) := by
  ext1 a
  simpa only [map_apply, prod_apply] using
    (Measure.prodAssoc_productBySections (μ := κ a) (ν := ξ a) (τ := η a))

lemma prodAssoc_symm_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    (κ ×ₖ (ξ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm = (κ ×ₖ ξ) ×ₖ η := by
  rw [← prodAssoc_prod, ← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  simp

lemma prod_const_comp {δ} {mδ : SigmaAlgebra δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] (μ : Measure δ) [SFinite μ] :
    (η ×ₖ (const β μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const α μ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]

lemma const_prod_comp {δ} {mδ : SigmaAlgebra δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (μ : Measure γ) [SFinite μ] (η : Kernel β δ) [IsSFiniteKernel η] :
    ((const β μ) ×ₖ η) ∘ₖ κ = (const α μ) ×ₖ (η ∘ₖ κ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.productBySections_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

end Kernel
end ProbabilityTheory

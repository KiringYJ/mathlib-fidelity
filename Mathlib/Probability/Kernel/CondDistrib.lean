/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.Unique

import Mathlib.Probability.Kernel.Integral

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space: the `μ.map X`-almost-everywhere class of the Markov kernels
`η : Kernel β Ω` with `μ.map X ⊗ₘ η = μ.map (fun a ↦ (X a, Y a))`. For every such kernel and almost
all `a`, `η (X a) s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at
`a`, for every measurable set `s`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The conditional distribution is determined only up to `μ.map X`-null sets, so it is a class of
kernels rather than a chosen kernel: a kernel `η` represents it, written
`η ∈ condDistrib Y X μ`, when it agrees `μ.map X`-almost everywhere with a Markov kernel that has
the defining property. Statements about the class hold for every representative; statements about
the values of a representative are stated for every Markov representative.

The case `Y = X = id` is developed in more detail in `Mathlib/Probability/Kernel/Condexp.lean`:
there `X` is the identity from `Ω` with its default σ-algebra to `Ω` with a sub-σ-algebra `m`, and
the finite representatives of this conditional distribution are those of `condExpKernel μ hm`, the
class of kernels associated with the conditional expectation with respect to `m`.

## Main definitions

* `condDistrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space, as a class of kernels.

## Main statements

* `mem_condDistrib_iff`: a finite kernel `η` represents `condDistrib Y X μ` if and only if
  `μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η`.
* `condDistrib_ae_eq_condExp`: for every Markov representative `η` and almost all `a`, `η (X a) s`
  is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condExp_prod_ae_eq_integral_condDistrib`: the conditional expectation
  `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(η (X a))` for every Markov representative `η`.
-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [SigmaAlgebra Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : SigmaAlgebra α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution** of `Y` given `X`: the `μ.map X`-almost
everywhere class of the Markov kernels `η` with `μ.map X ⊗ₘ η = μ.map (fun a => (X a, Y a))`, which
is the conditional kernel of the joint law of `(X, Y)` (`MeasureTheory.Measure.condKernel`).

For every Markov representative `η` and almost all `a`, `η (X a)` evaluated at a measurable set
`s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the
equality `μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a))` for all
integrable functions `f`. The joint map `fun a => (X a, Y a)` must be almost everywhere
measurable; this proof is normally discharged by `fun_prop`. -/
noncomputable def condDistrib {_ : SigmaAlgebra α} [SigmaAlgebra β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ]
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop) :
    Kernel.AEClass (ae (μ.map X hXY.fst)) Ω :=
  ((μ.map (fun a => (X a, Y a)) hXY).condKernel).copy
    (congrArg ae (Measure.fst_map_prodMk₀ hXY.fst hXY.snd)).symm

variable {mβ : SigmaAlgebra β} {s : Set Ω} {t : Set β} {f : β × Ω → F} {η : Kernel β Ω}

/-- The representatives of `condDistrib Y X μ` are those of the conditional kernel of the joint law
of `(X, Y)`. -/
lemma mem_condDistrib_iff_mem_condKernel (hXY : AEMeasurable (fun a => (X a, Y a)) μ) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ (μ.map (fun a => (X a, Y a)) hXY).condKernel :=
  Kernel.AEClass.mem_copy _

/-- `condDistrib Y X μ` is represented by a Markov kernel. -/
lemma exists_isMarkovKernel_mem_condDistrib
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop) :
    ∃ η : Kernel β Ω, IsMarkovKernel η ∧ η ∈ condDistrib Y X μ hXY :=
  let ⟨η, hη, _, hη_mem⟩ := (μ.map (fun a => (X a, Y a)) hXY).exists_isMarkovKernel_mem_condKernel
  ⟨η, hη, (mem_condDistrib_iff_mem_condKernel hXY).2 hη_mem⟩

/-- An s-finite representative of `condDistrib Y X μ` disintegrates the joint law of `(X, Y)`. -/
lemma isCondKernel_of_mem_condDistrib [IsSFiniteKernel η]
    {hXY : AEMeasurable (fun a => (X a, Y a)) μ} (hη : η ∈ condDistrib Y X μ hXY) :
    (μ.map (fun a => (X a, Y a)) hXY).IsCondKernel η :=
  Measure.isCondKernel_of_mem_condKernel ((mem_condDistrib_iff_mem_condKernel hXY).1 hη)

lemma compProd_map_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) :
    (μ.map X) ⊗ₘ η = μ.map fun a ↦ (X a, Y a) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ hX hY, Measure.disintegrate]

/-- A finite kernel `η` with `μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η` represents
`condDistrib Y X μ`. -/
lemma mem_condDistrib_of_measure_eq_compProd (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [IsFiniteKernel η] (hη : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η) :
    η ∈ condDistrib Y X μ := by
  have : (μ.map (fun x => (X x, Y x)) (hX.prodMk hY)).IsCondKernel η :=
    ⟨inferInstance, by rw [Measure.fst_map_prodMk₀ hX hY, ← hη]⟩
  exact (mem_condDistrib_iff_mem_condKernel _).2 Measure.IsCondKernel.mem_condKernel

/-- A finite kernel `η` represents `condDistrib Y X μ` if and only if
`μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η`. -/
lemma mem_condDistrib_iff (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) [IsFiniteKernel η] :
    η ∈ condDistrib Y X μ ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η :=
  ⟨fun h ↦ (compProd_map_condDistrib hX hY h).symm, mem_condDistrib_of_measure_eq_compProd hX hY⟩

/-- If the singleton `{x}` has non-zero mass for `μ.map X`, then for every s-finite representative
`η` of `condDistrib Y X μ` and all `s : Set Ω`,
`η x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)` . -/
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hX : Measurable X)
    (hY : Measurable Y) [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ) (x : β)
    (hX' : μ.map X hX.aemeasurable {x} ≠ 0) (s : Set Ω) :
    η x s =
      (μ.map X hX.aemeasurable {x})⁻¹ *
        μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY.aemeasurable) ({x} ×ˢ s) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [Measure.IsCondKernel.apply_of_ne_zero
    (μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY.aemeasurable)) η _ s]
  · rw [Measure.fst_map_prodMk hX hY]
  · rwa [Measure.fst_map_prodMk hX hY]

lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) :
    η ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hX hY hη, Measure.snd_map_prodMk₀ hX hY]

lemma condDistrib_congr {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y' X' μ (hXY.congr (hX.prodMk hY)) := by
  rw [mem_condDistrib_iff_mem_condKernel, mem_condDistrib_iff_mem_condKernel]
  exact Measure.mem_condKernel_congr (Measure.map_congr (hX.prodMk hY) hXY)

lemma condDistrib_congr_right {X' : α → β} (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X' μ (hXY.congr (hX.prodMk (by rfl))) :=
  condDistrib_congr (by rfl) hX hXY

lemma condDistrib_congr_left {Y' : α → Ω} (hY : Y =ᵐ[μ] Y')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y' X μ (hXY.congr (EventuallyEq.rfl.prodMk hY)) :=
  condDistrib_congr hY (by rfl) hXY

section Measurability

theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (η a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂(η a)) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← hf.ae_integrable_condKernel_iff (η := η), Measure.fst_map_prodMk₀ hX hY]

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂(η x)) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ hX hY]
  exact hf.integral_condKernel

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  AEStronglyMeasurable.comp_aemeasurable hX (hf.integral_condDistrib_map hX hY hη)

theorem aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  (hf.integral_condDistrib_map hX hY hη).comp_ae_measurable' hX

end Measurability

lemma map_mem_condDistrib_comp {Ω' : Type*} {mΩ' : SigmaAlgebra Ω'} [StandardBorelSpace Ω']
    [Nonempty Ω'] (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) {f : Ω → Ω'} (hf : Measurable f) :
    η.map f ∈ condDistrib (f ∘ Y) X μ := by
  refine mem_condDistrib_of_measure_eq_compProd hX (by fun_prop) ?_
  calc μ.map (fun x ↦ (X x, (f ∘ Y) x))
  _ = (μ.map (fun x ↦ (X x, Y x))).map (Prod.map id f) := by
    rw [Measure.map_map]
    simp [Function.comp_def]
  _ = (μ.map X ⊗ₘ η).map (Prod.map id f) := by rw [compProd_map_condDistrib hX hY hη]
  _ = μ.map X ⊗ₘ η.map f := by rw [Measure.compProd_map hf]

lemma deterministic_mem_condDistrib_comp_self (hX : AEMeasurable X μ) {f : β → Ω}
    (hf : Measurable f) :
    Kernel.deterministic f hf ∈ condDistrib (f ∘ X) X μ := by
  refine mem_condDistrib_of_measure_eq_compProd hX (by fun_prop) ?_
  rw [Measure.compProd_deterministic, Measure.map_map]
  simp [Function.comp_def]

lemma id_mem_condDistrib_self (hY : AEMeasurable Y μ) : Kernel.id ∈ condDistrib Y Y μ := by
  simpa using! deterministic_mem_condDistrib_comp_self hY measurable_id

lemma deterministic_mem_condDistrib_const (hX : AEMeasurable X μ) (c : Ω) :
    Kernel.deterministic (mα := mβ) (fun _ ↦ c) (by fun_prop) ∈
      condDistrib (fun _ ↦ c) X μ := by
  exact deterministic_mem_condDistrib_comp_self hX (measurable_const (a := c))

/-- Equal measures have the same representatives of the conditional distribution. Since the type of
`condDistrib Y X μ` depends on `μ`, this transports membership along an equation `μ = μ'`. -/
lemma condDistrib_congr_measure {μ' : Measure α} [IsFiniteMeasure μ'] (h : μ = μ')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X μ' (h ▸ hXY) := by
  subst h
  rfl

lemma condDistrib_map {γ : Type*} {mγ : SigmaAlgebra γ}
    {ν : Measure γ} [IsFiniteMeasure ν] {f : γ → α}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X (ν.map f))
    (hY : AEMeasurable Y (ν.map f)) :
    η ∈ condDistrib Y X (ν.map f) ↔ η ∈ condDistrib (Y ∘ f) (X ∘ f) ν := by
  rw [mem_condDistrib_iff_mem_condKernel, mem_condDistrib_iff_mem_condKernel]
  refine Measure.mem_condKernel_congr ?_
  rw [Measure.map_map hf (hX.prodMk hY)]
  rfl

lemma condDistrib_fst_prod {γ : Type*} {mγ : SigmaAlgebra γ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    η ∈ condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) ↔ η ∈ condDistrib Y X μ := by
  have h_eq : (μ.productBySections ν (hasAEMeasurableSectionMeasures_of_sfinite _ _)).map
      Prod.fst measurable_fst.aemeasurable = μ := by
    simp [Measure.map_fst_productBySections]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ)) (η := η)
      (ν := μ.productBySections ν (hasAEMeasurableSectionMeasures_of_sfinite _ _))
      (mα := inferInstance) (mβ := inferInstance)
      (by fun_prop) (by rw [h_eq]; exact hX) (by rw [h_eq]; exact hY)
  exact ((condDistrib_congr_measure (Measure.prod_eq_productBySections μ ν
    (hasAEMeasurableSectionMeasures_of_sfinite _ _) (hasUniqueProduct_of_sigmaFinite _ _)) _).trans
    h_map.symm).trans (condDistrib_congr_measure h_eq _)

lemma condDistrib_snd_prod {γ : Type*} {mγ : SigmaAlgebra γ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    η ∈ condDistrib (fun ω ↦ Y ω.2) (fun ω ↦ X ω.2) (ν.prod μ) ↔ η ∈ condDistrib Y X μ := by
  have h_eq : (ν.productBySections μ (hasAEMeasurableSectionMeasures_of_sfinite _ _)).map
      Prod.snd measurable_snd.aemeasurable = μ := by
    simp [Measure.map_snd_productBySections]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ)) (η := η)
      (ν := ν.productBySections μ (hasAEMeasurableSectionMeasures_of_sfinite _ _))
      (mα := inferInstance) (mβ := inferInstance)
      (by fun_prop) (by rw [h_eq]; exact hX) (by rw [h_eq]; exact hY)
  exact ((condDistrib_congr_measure (Measure.prod_eq_productBySections ν μ
    (hasAEMeasurableSectionMeasures_of_sfinite _ _) (hasUniqueProduct_of_sigmaFinite _ _)) _).trans
    h_map.symm).trans (condDistrib_congr_measure h_eq _)

section Integrability

theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (η b) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.condKernel_ae

theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (η (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(η x)) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.integral_norm_condKernel

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂(η (X a))) μ :=
  Integrable.comp_aemeasurable hX (hf_int.integral_norm_condDistrib_map hX hY hη)

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂(η x)‖) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.norm_integral_condKernel

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂(η (X a))‖) μ :=
  Integrable.comp_aemeasurable (f := X) (g := fun x => ‖∫ y, f (x, y) ∂(η x)‖)
    hX (hf_int.norm_integral_condDistrib_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂(η x)) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hX hY hη)).mp
    (hf_int.norm_integral_condDistrib_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  Integrable.comp_aemeasurable hX (hf_int.integral_condDistrib_map hX hY hη)

end Integrability

theorem setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, η (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX, ← Measure.restrict_map hX ht,
    ← Measure.fst_map_prodMk₀ hX.aemeasurable hY,
    Measure.setLIntegral_condKernel_eq_measure_prod ht hs,
    Measure.map_apply (ht.prod hs) (hX.aemeasurable.prodMk hY), mk_preimage_prod]

theorem setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s) {t : Set α}
    (ht : t ∈ mβ.comap X) :
    ∫⁻ a in t, η (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hη hs ht']

/-- For every Markov representative `η` of `condDistrib Y X μ` and almost every `a : α`, `η (X a)`
evaluated at a measurable set `s` is equal to the conditional expectation of the indicator of
`Y ⁻¹' s`. -/
theorem condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s) :
    (fun a => (η (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧ := by
  have h_meas : Measurable[mβ.comap X] fun a => η (X a) s :=
    (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (Integrable.comp_aemeasurable hX.aemeasurable
      (Kernel.IsMarkovKernel.integrable _ η hs)).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal (h_meas.mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (η (X ω)) _),
      integral_indicator_const _ (hY hs), measureReal_restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hη hs ht,
      measureReal_def]
  · exact h_meas.ennreal_toReal.aestronglyMeasurable

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against every Markov representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) := by
  have := isCondKernel_of_mem_condDistrib hη
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure (hX.aemeasurable.prodMk hY) hf_int.1).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY hη).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(η x')) ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y, f (x', y) ∂(η x'))]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hX.aemeasurable hY hη).restrict
    rw [← Measure.restrict_map hX ht, ← Measure.fst_map_prodMk₀ hX.aemeasurable hY,
      Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn,
      setIntegral_map (MeasurableSet.prod ht MeasurableSet.univ)
        (hX.aemeasurable.prodMk hY) hf_int.1,
      mk_preimage_prod, preimage_univ, inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hη hf_int.1

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against every Markov representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure (hX.aemeasurable.prodMk hY) hf]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hη hf_int'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against every Markov representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure (hX.aemeasurable.prodMk hY) hf.aestronglyMeasurable]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hη hf_int'

theorem condExp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) [IsMarkovKernel η] (hη : η ∈ condDistrib Y X μ) {f : Ω → F}
    (hf : StronglyMeasurable f) (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂(η (X a)) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY hη (hf.comp_measurable measurable_snd) hf_int

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(η (X a))` for every Markov representative `η` of `condDistrib Y X μ`. -/
theorem condExp_ae_eq_integral_condDistrib' {Ω : Type*} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [SigmaAlgebra Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    {η : Kernel β Ω} [IsMarkovKernel η] (hX : Measurable X) (hY_int : Integrable Y μ)
    (hη : η ∈ condDistrib Y X μ) :
    μ[Y | mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂(η (X a)) :=
  condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable hη stronglyMeasurable_id hY_int

open MeasureTheory

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk {Ω F} {mΩ : SigmaAlgebra Ω}
    {X : Ω → β} {μ : Measure Ω} (hX : AEMeasurable X μ) [TopologicalSpace F] {f : Ω → F}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω ↦ (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq_comp h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply hs measurable_snd.aemeasurable, Measure.map_apply]
  · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
    exact hμs
  · exact measurable_snd hs

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prodMk
    {Ω} {mΩ : SigmaAlgebra Ω} {X : Ω → β} {μ : Measure Ω} (hX : AEMeasurable X μ)
    {f : Ω → F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  have hf := hf_int.1.comp_snd_map_prodMk hX (mΩ := mΩ) (mβ := mβ)
  refine ⟨hf, ?_⟩
  have hpair : AEMeasurable (fun ω => (X ω, ω)) μ := by
    simpa only [id_eq] using hX.prodMk aemeasurable_id
  rw [hasFiniteIntegral_iff_enorm, lintegral_map' hpair hf.enorm]
  exact hf_int.2

theorem aestronglyMeasurable_comp_snd_map_prodMk_iff {Ω F} {_ : SigmaAlgebra Ω}
    [TopologicalSpace F] {X : Ω → β} {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
      AEStronglyMeasurable f μ :=
  ⟨fun h => AEStronglyMeasurable.comp_measurable
      (f := fun ω => (X ω, ω)) (g := fun x : β × Ω => f x.2)
      (hX.prodMk measurable_id) h,
    fun h => h.comp_snd_map_prodMk hX.aemeasurable⟩

theorem integrable_comp_snd_map_prodMk_iff {Ω} {_ : SigmaAlgebra Ω} {X : Ω → β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω → F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => Integrable.comp_measurable
      (f := fun ω => (X ω, ω)) (g := fun x : β × Ω => f x.2)
      (hX.prodMk measurable_id) h,
    fun h => h.comp_snd_map_prodMk hX.aemeasurable⟩

theorem condExp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ)
    {η : Kernel β Ω} [IsMarkovKernel η] (hη : η ∈ condDistrib id X μ) :
    μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂(η (X a)) :=
  condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id hη
    (hf_int.comp_snd_map_prodMk hX.aemeasurable)

end ProbabilityTheory

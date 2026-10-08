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

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`: the
`μ.map X`-almost-everywhere class of the Markov kernels `η : Kernel β Ω` with
`μ.map X ⊗ₘ η = μ.map (fun a ↦ (X a, Y a))`. If the law of `X` is σ-finite, then for every such
kernel, every measurable set `s` with `μ (Y ⁻¹' s) ≠ ∞`, and almost all `a`, `η (X a) s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

When the law of `X` is σ-finite, `μ⟦Y ⁻¹' s | mβ.comap X⟧` is, for a measurable set `s` with
`μ (Y ⁻¹' s) ≠ ∞`, a function `α → ℝ` determined up to a `μ`-null set. For all `a`, the map from
sets to `ℝ` that we obtain that way verifies some of the properties of a measure, but in general
the fact that the `μ`-null set depends on `s` can prevent us from finding versions of the
conditional expectation that combine into a true measure. A standard Borel space `Ω` allows us to
do so.

The conditional distribution exists when the joint law of `(X, Y)` has a unique conditional kernel,
which the statements take as an instance argument. Instance search supplies it when `Ω` is a
nonempty standard Borel space and the law `μ.map X` of `X`, the first marginal of the joint law, is
σ-finite (`MeasureTheory.Measure.sigmaFinite_fst_map_prodMk`), for example when `μ` is finite.

The conditional distribution is determined only up to `μ.map X`-null sets, so it is a class of
kernels rather than a chosen kernel: a kernel `η` represents it, written
`η ∈ condDistrib Y X μ`, when it agrees `μ.map X`-almost everywhere with a Markov kernel that has
the defining property. Statements about the class, the defining property, and the measures and
Lebesgue integrals of a representative hold for every representative; those about Bochner integrals
are stated for every s-finite representative, and the identification of the values of a
representative with conditional expectations for every Markov one.

The case `Y = X = id` is developed in more detail in `Mathlib/Probability/Kernel/Condexp.lean`:
there `X` is the identity from `Ω` with its default σ-algebra to `Ω` with a sub-σ-algebra `m`, and
the finite representatives of this conditional distribution are those of `condExpKernel μ hm`, the
class of kernels associated with the conditional expectation with respect to `m`.

## Main definitions

* `condDistrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, as a class of kernels.

## Main statements

* `mem_condDistrib_iff`: if the law of `X` is σ-finite, a kernel `η` for which `μ.map X ⊗ₘ η`
  exists represents `condDistrib Y X μ` if and only if `μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η`.
* `condDistrib_ae_eq_condExp`: if the law of `X` is σ-finite, then for every Markov representative
  `η`, every measurable set `s` with `μ (Y ⁻¹' s) ≠ ∞`, and almost all `a`, `η (X a) s` is equal to
  the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condExp_prod_ae_eq_integral_condDistrib`: if the law of `X` is σ-finite, the conditional
  expectation `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(η (X a))` for every s-finite representative `η`.
-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [SigmaAlgebra Ω] [NormedAddCommGroup F] {mα : SigmaAlgebra α}
  {μ : Measure α} {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution** of `Y` given `X`: the `μ.map X`-almost
everywhere class of the Markov kernels `η` with `μ.map X ⊗ₘ η = μ.map (fun a => (X a, Y a))`, which
is the conditional kernel of the joint law of `(X, Y)` (`MeasureTheory.Measure.condKernel`).

If the law of `X` is σ-finite, then for every Markov representative `η`, every measurable set `s`
with `μ (Y ⁻¹' s) ≠ ∞`, and almost all `a`, `η (X a) s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧ a`, and for every s-finite representative `η` and every integrable function
`f`, `μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a))`. The joint
map `fun a => (X a, Y a)` must be almost everywhere measurable; this proof is normally discharged
by `fun_prop` through the default tactic `fun_prop_default`, and an instance of the class of the
joint law found in the local context determines it before default arguments are synthesized. -/
noncomputable def condDistrib {_ : SigmaAlgebra α} [SigmaAlgebra β] (Y : α → Ω)
    (X : α → β) (μ : Measure α)
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop_default)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel] :
    Kernel.AEClass (ae (μ.map X hXY.fst)) Ω :=
  ((μ.map (fun a => (X a, Y a)) hXY).condKernel).copy
    (congrArg ae (Measure.fst_map_prodMk₀ hXY.fst hXY.snd)).symm

variable {mβ : SigmaAlgebra β} {s : Set Ω} {t : Set β} {f : β × Ω → F} {η : Kernel β Ω}

/-- The representatives of `condDistrib Y X μ` are those of the conditional kernel of the joint law
of `(X, Y)`. -/
lemma mem_condDistrib_iff_mem_condKernel (hXY : AEMeasurable (fun a => (X a, Y a)) μ)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel] :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ (μ.map (fun a => (X a, Y a)) hXY).condKernel :=
  Kernel.AEClass.mem_copy _

/-- `condDistrib Y X μ` is represented by a Markov kernel. -/
lemma exists_isMarkovKernel_mem_condDistrib
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop_default)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel] :
    ∃ η : Kernel β Ω, IsMarkovKernel η ∧ η ∈ condDistrib Y X μ hXY :=
  let ⟨η, hη, _, hη_mem⟩ := (μ.map (fun a => (X a, Y a)) hXY).exists_isMarkovKernel_mem_condKernel
  ⟨η, hη, (mem_condDistrib_iff_mem_condKernel hXY).2 hη_mem⟩

/-- A representative of `condDistrib Y X μ` disintegrates the joint law of `(X, Y)`. -/
lemma isCondKernel_of_mem_condDistrib {hXY : AEMeasurable (fun a => (X a, Y a)) μ}
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel] (hη : η ∈ condDistrib Y X μ hXY) :
    (μ.map (fun a => (X a, Y a)) hXY).IsCondKernel η :=
  Measure.isCondKernel_of_mem_condKernel ((mem_condDistrib_iff_mem_condKernel hXY).1 hη)

/-- The composition-product of the law of `X` with a representative of `condDistrib Y X μ` exists,
since the representative disintegrates the joint law of `(X, Y)`, whose first marginal is the law
of `X`. -/
lemma hasCompProd_map_of_mem_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    (hη : η ∈ condDistrib Y X μ) : (μ.map X hX).HasCompProd η := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ hX hY]
  infer_instance

/-- The law of `X` and a representative of `condDistrib Y X μ` have the joint law of `(X, Y)` as
composition-product. -/
lemma compProd_map_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [(μ.map X hX).HasCompProd η] (hη : η ∈ condDistrib Y X μ) :
    (μ.map X) ⊗ₘ η = μ.map fun a ↦ (X a, Y a) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [Measure.compProd_congr_measure (Measure.fst_map_prodMk₀ hX hY).symm, Measure.disintegrate]

/-- A kernel `η` with `μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η` represents `condDistrib Y X μ`
if the law of `X` is σ-finite. -/
lemma mem_condDistrib_of_measure_eq_compProd (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [SigmaFinite (μ.map X hX)]
    [(μ.map X hX).HasCompProd η] (hη : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η) :
    η ∈ condDistrib Y X μ := by
  have : (μ.map (fun x => (X x, Y x)) (hX.prodMk hY)).IsCondKernel η :=
    .of_compProd_eq (Measure.fst_map_prodMk₀ hX hY) hη.symm
  exact (mem_condDistrib_iff_mem_condKernel _).2 Measure.IsCondKernel.mem_condKernel

/-- A kernel `η` for which `μ.map X ⊗ₘ η` exists represents `condDistrib Y X μ` if and only if
`μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η`, if the law of `X` is σ-finite. -/
lemma mem_condDistrib_iff (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [SigmaFinite (μ.map X hX)]
    [(μ.map X hX).HasCompProd η] :
    η ∈ condDistrib Y X μ ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η :=
  ⟨fun h ↦ (compProd_map_condDistrib hX hY h).symm, mem_condDistrib_of_measure_eq_compProd hX hY⟩

/-- A Markov kernel `η` with `μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η` represents
`condDistrib Y X μ`. Unlike for a kernel that is not Markov, the class of the joint law suffices. -/
lemma mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [IsMarkovKernel η] (hη : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ η) :
    η ∈ condDistrib Y X μ :=
  (mem_condDistrib_iff_mem_condKernel _).2 (Measure.mem_condKernel_iff_of_isMarkovKernel.2
    (.of_compProd_eq (Measure.fst_map_prodMk₀ hX hY) hη.symm))

/-- If the singleton `{x}` has non-zero finite mass for `μ.map X`, then for every representative
`η` of `condDistrib Y X μ` and all `s : Set Ω`,
`η x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)`. The finiteness is supplied by
default for a finite or σ-finite law of `X`. -/
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    (hη : η ∈ condDistrib Y X μ) (x : β) (hX' : μ.map X hX {x} ≠ 0) (s : Set Ω)
    (hX'_top : μ.map X hX {x} ≠ ∞ := by measure_singleton_ne_top) :
    η x s = (μ.map X hX {x})⁻¹ * μ.map (fun a => (X a, Y a)) (hX.prodMk hY) ({x} ×ˢ s) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [Measure.IsCondKernel.apply_of_ne_zero (μ.map (fun a => (X a, Y a)) (hX.prodMk hY)) η ?_ s ?_]
  · rw [Measure.fst_map_prodMk₀ hX hY]
  · rwa [Measure.fst_map_prodMk₀ hX hY]
  · rwa [Measure.fst_map_prodMk₀ hX hY]

lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    (hη : η ∈ condDistrib Y X μ) :
    η ∘ₘ (μ.map X) = μ.map Y := by
  have := hasCompProd_map_of_mem_condDistrib hX hY hη
  rw [← Measure.snd_compProd, compProd_map_condDistrib hX hY hη, Measure.snd_map_prodMk₀ hX hY]

/-- Almost everywhere equal maps have the same conditional distribution, when both joint laws have
unique conditional kernels; the laws are equal. -/
lemma mem_condDistrib_congr {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop_default)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ.map (fun a => (X' a, Y' a)) (hXY.congr (hX.prodMk hY))).HasUniqueCondKernel] :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y' X' μ (hXY.congr (hX.prodMk hY)) := by
  rw [mem_condDistrib_iff_mem_condKernel, mem_condDistrib_iff_mem_condKernel]
  exact Measure.mem_condKernel_congr (Measure.map_congr (hX.prodMk hY) hXY)

lemma mem_condDistrib_congr_right {X' : α → β} (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop_default)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ.map (fun a => (X' a, Y a)) (hXY.congr (hX.prodMk (by rfl)))).HasUniqueCondKernel] :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X' μ (hXY.congr (hX.prodMk (by rfl))) :=
  mem_condDistrib_congr (by rfl) hX hXY

lemma mem_condDistrib_congr_left {Y' : α → Ω} (hY : Y =ᵐ[μ] Y')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ := by fun_prop_default)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ.map (fun a => (X a, Y' a)) (hXY.congr (EventuallyEq.rfl.prodMk hY))).HasUniqueCondKernel] :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y' X μ (hXY.congr (EventuallyEq.rfl.prodMk hY)) :=
  mem_condDistrib_congr hY (by rfl) hXY

section Measurability

theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [SFinite (μ.map X hX)]
    [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (η a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂(η a)) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← hf.ae_integrable_condKernel_iff (η := η), Measure.fst_map_prodMk₀ hX hY]

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂(η x)) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ hX hY]
  exact hf.integral_condKernel

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  AEStronglyMeasurable.comp_aemeasurable hX (hf.integral_condDistrib_map hX hY hη)

theorem aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  (hf.integral_condDistrib_map hX hY hη).comp_ae_measurable' hX

end Measurability

lemma map_mem_condDistrib_comp {Ω' : Type*} {mΩ' : SigmaAlgebra Ω'}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) {f : Ω → Ω'} (hf : Measurable f)
    [(μ.map (fun a => (X a, (f ∘ Y) a))
      (hX.prodMk (hf.comp_aemeasurable hY))).HasUniqueCondKernel] :
    η.map f ∈ condDistrib (f ∘ Y) X μ := by
  have := Kernel.IsMarkovKernel.map η hf
  refine mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel hX (by fun_prop) ?_
  calc μ.map (fun x ↦ (X x, (f ∘ Y) x))
  _ = (μ.map (fun x ↦ (X x, Y x))).map (Prod.map id f) := by
    rw [Measure.map_map]
    simp [Function.comp_def]
  _ = (μ.map X ⊗ₘ η).map (Prod.map id f) := by rw [compProd_map_condDistrib hX hY hη]
  _ = μ.map X ⊗ₘ η.map f := by rw [Measure.compProd_map hf]

lemma deterministic_mem_condDistrib_comp_self (hX : AEMeasurable X μ) {f : β → Ω}
    (hf : Measurable f)
    [(μ.map (fun a => (X a, (f ∘ X) a))
      (hX.prodMk (hf.comp_aemeasurable hX))).HasUniqueCondKernel] :
    Kernel.deterministic f hf ∈ condDistrib (f ∘ X) X μ := by
  refine mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel hX (by fun_prop) ?_
  rw [Measure.compProd_deterministic, Measure.map_map]
  simp [Function.comp_def]

lemma id_mem_condDistrib_self (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (Y a, Y a)) (hY.prodMk hY)).HasUniqueCondKernel] :
    Kernel.id ∈ condDistrib Y Y μ := by
  refine mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel hY hY ?_
  rw [Measure.compProd_id, Measure.map_map hY]
  rfl

lemma deterministic_mem_condDistrib_const (hX : AEMeasurable X μ) (c : Ω)
    [(μ.map (fun a => (X a, c)) (hX.prodMk aemeasurable_const)).HasUniqueCondKernel] :
    Kernel.deterministic (mα := mβ) (fun _ ↦ c) (by fun_prop) ∈
      condDistrib (fun _ ↦ c) X μ := by
  refine mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel hX aemeasurable_const ?_
  rw [Measure.compProd_deterministic, Measure.map_map]
  simp [Function.comp_def]

/-- Equal measures have the same representatives of the conditional distribution. Since the type of
`condDistrib Y X μ` depends on `μ`, this transports membership along an equation `μ = μ'`. -/
lemma mem_condDistrib_congr_measure {μ' : Measure α} (h : μ = μ')
    (hXY : AEMeasurable (fun a => (X a, Y a)) μ)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ'.map (fun a => (X a, Y a)) (h ▸ hXY)).HasUniqueCondKernel] :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X μ' (h ▸ hXY) := by
  subst h
  rfl

lemma mem_condDistrib_map_iff {γ : Type*} {mγ : SigmaAlgebra γ}
    {ν : Measure γ} {f : γ → α}
    (hf : AEMeasurable f ν) (hX : AEMeasurable X (ν.map f))
    (hY : AEMeasurable Y (ν.map f))
    [((ν.map f).map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [(ν.map (fun a => ((X ∘ f) a, (Y ∘ f) a))).HasUniqueCondKernel] :
    η ∈ condDistrib Y X (ν.map f) ↔ η ∈ condDistrib (Y ∘ f) (X ∘ f) ν := by
  rw [mem_condDistrib_iff_mem_condKernel, mem_condDistrib_iff_mem_condKernel]
  refine Measure.mem_condKernel_congr ?_
  rw [Measure.map_map hf (hX.prodMk hY)]
  rfl

/-- A nonzero factor does not change the conditional distribution: it scales the joint law, which
keeps the conditional kernel (`MeasureTheory.Measure.mem_condKernel_smul_iff`). For a finite factor,
the class of the scaled joint law follows from that of the joint law
(`MeasureTheory.Measure.HasUniqueCondKernel.smul`); for the factor `∞` it does not. -/
lemma mem_condDistrib_smul_iff {c : ℝ≥0∞} (hc : c ≠ 0) (hXY : AEMeasurable (fun a => (X a, Y a)) μ)
    [(μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel]
    [((c • μ).map (fun a => (X a, Y a)) (hXY.smul_measure c)).HasUniqueCondKernel] :
    η ∈ condDistrib Y X (c • μ) (hXY.smul_measure c) ↔ η ∈ condDistrib Y X μ hXY := by
  have h_law : (c • μ).map (fun a => (X a, Y a)) (hXY.smul_measure c) =
      c • μ.map (fun a => (X a, Y a)) hXY :=
    Measure.map_smul _ hXY
  have : (c • μ.map (fun a => (X a, Y a)) hXY).HasUniqueCondKernel := h_law ▸ inferInstance
  rw [mem_condDistrib_iff_mem_condKernel, mem_condDistrib_iff_mem_condKernel,
    Measure.mem_condKernel_congr h_law, Measure.mem_condKernel_smul_iff hc]

/-- A nonzero factor does not change the conditional distribution: the law of the first coordinate
is the measure scaled by the total mass of the factor
(`ProbabilityTheory.mem_condDistrib_smul_iff`). -/
lemma mem_condDistrib_fst_prod_iff {γ : Type*} {mγ : SigmaAlgebra γ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (ν : Measure γ) [NeZero ν]
    (h : HasUniqueProduct μ ν := by has_unique_product)
    [((μ.prod ν h).map (fun ω ↦ (X ω.1, Y ω.1))).HasUniqueCondKernel]
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] :
    η ∈ condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν h) ↔ η ∈ condDistrib Y X μ := by
  have h_eq : (μ.prod ν h).map Prod.fst measurable_fst.aemeasurable = ν Set.univ • μ :=
    Measure.map_fst_prod
  have hXY : AEMeasurable (fun a ↦ (X a, Y a))
      ((μ.prod ν h).map Prod.fst measurable_fst.aemeasurable) := by
    rw [h_eq]
    exact (hX.prodMk hY).smul_measure _
  have h_law : (μ.prod ν h).map (fun ω ↦ (X ω.1, Y ω.1)) =
      (ν Set.univ • μ).map (fun a => (X a, Y a)) ((hX.prodMk hY).smul_measure _) := by
    rw [← Measure.map_congr_measure h_eq hXY, Measure.map_map measurable_fst.aemeasurable hXY]
    rfl
  have : ((ν Set.univ • μ).map (fun a => (X a, Y a))
      ((hX.prodMk hY).smul_measure _)).HasUniqueCondKernel := h_law ▸ inferInstance
  rw [mem_condDistrib_iff_mem_condKernel, Measure.mem_condKernel_congr h_law,
    ← mem_condDistrib_smul_iff (NeZero.ne (ν Set.univ)) (hX.prodMk hY),
    mem_condDistrib_iff_mem_condKernel]

/-- A nonzero factor does not change the conditional distribution: the law of the second coordinate
is the measure scaled by the total mass of the factor
(`ProbabilityTheory.mem_condDistrib_smul_iff`). -/
lemma mem_condDistrib_snd_prod_iff {γ : Type*} {mγ : SigmaAlgebra γ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (ν : Measure γ) [NeZero ν]
    (h : HasUniqueProduct ν μ := by has_unique_product)
    [((ν.prod μ h).map (fun ω ↦ (X ω.2, Y ω.2))).HasUniqueCondKernel]
    [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] :
    η ∈ condDistrib (fun ω ↦ Y ω.2) (fun ω ↦ X ω.2) (ν.prod μ h) ↔ η ∈ condDistrib Y X μ := by
  have h_eq : (ν.prod μ h).map Prod.snd measurable_snd.aemeasurable = ν Set.univ • μ :=
    Measure.map_snd_prod
  have hXY : AEMeasurable (fun a ↦ (X a, Y a))
      ((ν.prod μ h).map Prod.snd measurable_snd.aemeasurable) := by
    rw [h_eq]
    exact (hX.prodMk hY).smul_measure _
  have h_law : (ν.prod μ h).map (fun ω ↦ (X ω.2, Y ω.2)) =
      (ν Set.univ • μ).map (fun a => (X a, Y a)) ((hX.prodMk hY).smul_measure _) := by
    rw [← Measure.map_congr_measure h_eq hXY, Measure.map_map measurable_snd.aemeasurable hXY]
    rfl
  have : ((ν Set.univ • μ).map (fun a => (X a, Y a))
      ((hX.prodMk hY).smul_measure _)).HasUniqueCondKernel := h_law ▸ inferInstance
  rw [mem_condDistrib_iff_mem_condKernel, Measure.mem_condKernel_congr h_law,
    ← mem_condDistrib_smul_iff (NeZero.ne (ν Set.univ)) (hX.prodMk hY),
    mem_condDistrib_iff_mem_condKernel]

section Integrability

theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (η b) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.condKernel_ae

theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (η (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(η x)) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.integral_norm_condKernel

theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂(η (X a))) μ :=
  Integrable.comp_aemeasurable hX (hf_int.integral_norm_condDistrib_map hX hY hη)

variable [NormedSpace ℝ F]

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂(η x)‖) (μ.map X) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← Measure.fst_map_prodMk₀ (X := X) hX hY]; exact hf_int.norm_integral_condKernel

theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂(η (X a))‖) μ :=
  Integrable.comp_aemeasurable (f := X) (g := fun x => ‖∫ y, f (x, y) ∂(η x)‖)
    hX (hf_int.norm_integral_condDistrib_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂(η x)) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hX hY hη)).mp
    (hf_int.norm_integral_condDistrib_map hX hY hη)

theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) [(μ.map (fun a => (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [SFinite (μ.map X hX)] [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂(η (X a))) μ :=
  Integrable.comp_aemeasurable hX (hf_int.integral_condDistrib_map hX hY hη)

end Integrability

theorem setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, η (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  have := isCondKernel_of_mem_condDistrib hη
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX, ← Measure.restrict_map hX ht,
    ← Measure.fst_map_prodMk₀ hX.aemeasurable hY,
    Measure.setLIntegral_condKernel_eq_measure_prod ht hs,
    Measure.map_apply (ht.prod hs) (hX.aemeasurable.prodMk hY), mk_preimage_prod]

theorem setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s) {t : Set α}
    (ht : t ∈ mβ.comap X) :
    ∫⁻ a in t, η (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hη hs ht']

/-- For every Markov representative `η` of `condDistrib Y X μ` and almost every `a : α`, `η (X a)`
evaluated at a measurable set `s` is equal to the conditional expectation of the indicator of
`Y ⁻¹' s`. -/
theorem condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY.aemeasurable)).HasUniqueCondKernel]
    [SigmaFinite (μ.map X hX.aemeasurable)] [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) (hs : MeasurableSet s)
    (hμs : μ (Y ⁻¹' s) ≠ ∞ := by finiteness) :
    (fun a => (η (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧ := by
  have := sigmaFinite_trim_comap (μ := μ) hX
  have h_meas : Measurable[mβ.comap X] fun a => η (X a) s :=
    (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrableOn_const hμs).integrable_indicator (hY hs)
  · refine fun t _ ht ↦ Measure.integrableOn_of_bounded ht.ne
      (h_meas.mono hX.comap_le le_rfl).ennreal_toReal.aestronglyMeasurable (M := 1) ?_
    refine ae_of_all _ fun a ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal (h_meas.mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (η (X ω)) _),
      integral_indicator_const _ (hY hs), measureReal_restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hη hs ht,
      measureReal_def]
  · exact h_meas.ennreal_toReal.aestronglyMeasurable

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against every s-finite representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    [SigmaFinite (μ.map X hX.aemeasurable)]
    [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) := by
  have := sigmaFinite_trim_comap (μ := μ) hX
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
to the integral of `y ↦ f(X, y)` against every s-finite representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    [SigmaFinite (μ.map X hX.aemeasurable)]
    [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure (hX.aemeasurable.prodMk hY) hf]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hη hf_int'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against every s-finite representative of `condDistrib Y X μ`. -/
theorem condExp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    [SigmaFinite (μ.map X hX.aemeasurable)]
    [IsSFiniteKernel η]
    (hη : η ∈ condDistrib Y X μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(η (X a)) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure (hX.aemeasurable.prodMk hY) hf.aestronglyMeasurable]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hη hf_int'

theorem condExp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ)
    [(μ.map (fun a => (X a, Y a)) (hX.aemeasurable.prodMk hY)).HasUniqueCondKernel]
    [SigmaFinite (μ.map X hX.aemeasurable)]
    [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ) {f : Ω → F}
    (hf : StronglyMeasurable f) (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂(η (X a)) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY hη (hf.comp_measurable measurable_snd) hf_int

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(η (X a))` for every s-finite representative `η` of `condDistrib Y X μ`. -/
theorem condExp_ae_eq_integral_condDistrib' {Ω : Type*} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [SigmaAlgebra Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    {η : Kernel β Ω} [IsSFiniteKernel η] (hX : Measurable X) [SigmaFinite (μ.map X hX.aemeasurable)]
    (hY_int : Integrable Y μ)
    [(μ.map (fun a => (X a, Y a))
      (hX.aemeasurable.prodMk hY_int.1.aemeasurable)).HasUniqueCondKernel]
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
    {μ : Measure Ω} (hX : Measurable X) [SigmaFinite (μ.map X hX.aemeasurable)] {f : Ω → F}
    (hf_int : Integrable f μ)
    [(μ.map (fun a => (X a, id a)) (hX.aemeasurable.prodMk aemeasurable_id)).HasUniqueCondKernel]
    {η : Kernel β Ω} [IsSFiniteKernel η] (hη : η ∈ condDistrib id X μ) :
    μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂(η (X a)) :=
  condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id hη
    (hf_int.comp_snd_map_prodMk hX.aemeasurable)

end ProbabilityTheory

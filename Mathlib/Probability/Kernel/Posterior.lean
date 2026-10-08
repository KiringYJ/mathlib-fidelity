/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.Unique
public import Mathlib.Probability.Kernel.Deterministic

/-!

# Posterior kernel

For `μ : Measure Ω` (called prior measure), seen as a measure on a parameter, and a kernel
`κ : Kernel Ω 𝓧` that gives the conditional distribution of "data" in `𝓧` given the prior parameter,
we can get the distribution of the data with `κ ∘ₘ μ`, and the joint distribution of parameter and
data with `μ ⊗ₘ κ : Measure (Ω × 𝓧)`.

A posterior distribution of the parameter given the data is a Markov kernel `η : Kernel 𝓧 Ω` such
that `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`. That is, the joint distribution of parameter and data
can be recovered from the distribution of the data and the posterior. Such a kernel is determined
only up to `κ ∘ₘ μ`-null sets, so the posterior `κ†μ` is the `κ ∘ₘ μ`-almost-everywhere class of
these kernels, and the statements below hold for every Markov representative `η ∈ κ†μ`.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`, as a class of kernels.

## Main statements

* `mem_posterior_iff`: if `κ ∘ₘ μ` is σ-finite, a finite kernel `η` represents `κ†μ` if and only if
  `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`.
* `posterior_comp_self`: `η ∘ₘ κ ∘ₘ μ = μ` for every Markov representative `η` of `κ†μ`.
* `mem_posterior_posterior`: `κ` represents the posterior of every Markov representative of `κ†μ`
  for the prior `κ ∘ₘ μ`.
* `comp_mem_posterior_comp`: the composition of Markov representatives of `κ†μ` and `η†(κ ∘ₘ μ)`
  represents `(η ∘ₖ κ)†μ`.

* `posterior_eq_withDensity`: If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, then for every Markov
  representative `η` of `κ†μ` and `κ ∘ₘ μ`-almost every `x`,
  `η x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
  The condition is true for countable `Ω`: see `absolutelyContinuous_comp_of_countable`.

## Notation

`κ†μ` denotes the posterior of `κ` with respect to `μ`, `posterior κ μ`.
`†` can be typed as `\dag` or `\dagger`.

This notation emphasizes that the posterior is a kind of inverse of `κ`, which we would want to
denote `κ†`, but we have to also specify the measure `μ`.

-/

@[expose] public section

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 : Type*}
  {mΩ : SigmaAlgebra Ω} {m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨}
  {κ : Kernel Ω 𝓧} {μ : Measure Ω}

/-- The first marginal of the joint law with swapped coordinates is the law `κ ∘ₘ μ` of the
data. -/
lemma fst_map_swap_compProd (κ : Kernel Ω 𝓧) (μ : Measure Ω) [μ.HasCompProd κ] :
    ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).fst = κ ∘ₘ μ := by
  rw [Measure.fst_map_swap, Measure.snd_compProd]

/-- The first marginal of the joint law with swapped coordinates is σ-finite if the law `κ ∘ₘ μ`
of the data is, since it is that law. For a nonempty standard Borel space `Ω`, the joint law then
has a unique conditional kernel, so that the posterior exists; this admits an infinite prior `μ`. -/
instance sigmaFinite_fst_map_swap_compProd [μ.HasCompProd κ] [SigmaFinite (κ ∘ₘ μ)] :
    SigmaFinite ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).fst := by
  rwa [fst_map_swap_compProd]

/-- Posterior of the kernel `κ` with respect to the measure `μ`: the `κ ∘ₘ μ`-almost-everywhere
class of the Markov kernels `η : Kernel 𝓧 Ω` with `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`, which is
the conditional kernel of the joint law with swapped coordinates
(`MeasureTheory.Measure.condKernel`).

It exists when this joint law has a unique conditional kernel, in particular when `κ ∘ₘ μ` is
σ-finite (`ProbabilityTheory.sigmaFinite_fst_map_swap_compProd`). A finite kernel represents it
if and only if it has this property, when `κ ∘ₘ μ` is σ-finite (`mem_posterior_iff`), and a Markov
representative exists (`exists_isMarkovKernel_mem_posterior`). -/
noncomputable
def posterior (κ : Kernel Ω 𝓧) (μ : Measure Ω) [μ.HasCompProd κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] :
    Kernel.AEClass (ae (κ ∘ₘ μ)) Ω :=
  (((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).condKernel).copy
    (congrArg ae (fst_map_swap_compProd κ μ)).symm

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
scoped[ProbabilityTheory] infix:arg "†" => ProbabilityTheory.posterior

section HasUniqueCondKernel

variable [μ.HasCompProd κ]
  [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] {η : Kernel 𝓧 Ω}

/-- The representatives of `κ†μ` are those of the conditional kernel of the joint law with swapped
coordinates. -/
lemma mem_posterior_iff_mem_condKernel :
    η ∈ κ†μ ↔ η ∈ ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).condKernel :=
  Kernel.AEClass.mem_copy _

/-- The posterior is represented by a Markov kernel. -/
lemma exists_isMarkovKernel_mem_posterior : ∃ η : Kernel 𝓧 Ω, IsMarkovKernel η ∧ η ∈ κ†μ :=
  let ⟨η, hη, _, hη_mem⟩ :=
    ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).exists_isMarkovKernel_mem_condKernel
  ⟨η, hη, mem_posterior_iff_mem_condKernel.2 hη_mem⟩

/-- The main property of the posterior, for every s-finite representative. -/
lemma compProd_posterior_eq_map_swap [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
    (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
  have := Measure.isCondKernel_of_mem_condKernel (mem_posterior_iff_mem_condKernel.1 hη)
  rw [← fst_map_swap_compProd κ μ]
  exact Measure.disintegrate _ η

lemma compProd_posterior_eq_swap_comp [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
    (κ ∘ₘ μ) ⊗ₘ η = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_map_swap hη, Measure.swap_comp]

lemma posterior_comp_self [IsMarkovKernel κ] [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
    η ∘ₘ κ ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap hη, Measure.snd_map_swap,
    Measure.fst_compProd]

end HasUniqueCondKernel

variable [StandardBorelSpace Ω] [Nonempty Ω]

section SigmaFinite

variable [μ.HasCompProd κ] [SigmaFinite (κ ∘ₘ μ)] {η : Kernel 𝓧 Ω}

/-- A finite kernel with the main property of the posterior represents it. -/
lemma mem_posterior_of_compProd_eq [IsFiniteKernel η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η ∈ κ†μ := by
  have : ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).IsCondKernel η :=
    ⟨inferInstance, by rw [fst_map_swap_compProd, h]⟩
  exact mem_posterior_iff_mem_condKernel.2 Measure.IsCondKernel.mem_condKernel

/-- A finite kernel represents the posterior if and only if it has its main property. -/
lemma mem_posterior_iff [IsFiniteKernel η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  ⟨compProd_posterior_eq_map_swap, mem_posterior_of_compProd_eq⟩

/-- A finite kernel `η` with `(κ ∘ₘ μ) ⊗ₘ η = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ` represents the
posterior. -/
lemma mem_posterior_of_compProd_eq_swap_comp [IsFiniteKernel η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ) :
    η ∈ κ†μ :=
  mem_posterior_of_compProd_eq <| by rw [h, Measure.swap_comp]

end SigmaFinite

variable [IsFiniteMeasure μ] [IsFiniteKernel κ] {η : Kernel 𝓧 Ω}

lemma swap_compProd_posterior [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
    Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) ⊗ₘ η = μ ⊗ₘ κ := by
  simp only [compProd_posterior_eq_swap_comp hη, Measure.comp_assoc, Kernel.swap_swap,
    Measure.id_comp]

/-- The main property of the posterior, as equality of the following diagrams:
```
         -- id          -- κ
μ -- κ -|        =  μ -|
         -- η           -- id
```
for every Markov representative `η` of `κ†μ`. -/
lemma parallelProd_posterior_comp_copy_comp [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    (Kernel.id ∥ₖ η) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
      = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
  calc (Kernel.id ∥ₖ η) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) ⊗ₘ η := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_posterior_eq_swap_comp hη]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    have hkernel :
        (Kernel.swap Ω 𝓧 ∘ₖ (Kernel.id ∥ₖ κ)) ∘ₖ Kernel.copy Ω =
          (κ ∥ₖ Kernel.id) ∘ₖ Kernel.copy Ω := by
      rw [Kernel.swap_parallelComp, Kernel.comp_assoc, Kernel.swap_copy]
    calc
      Kernel.swap Ω 𝓧 ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ =
          ((Kernel.swap Ω 𝓧 ∘ₖ (Kernel.id ∥ₖ κ)) ∘ₖ Kernel.copy Ω) ∘ₘ μ :=
        Measure.comp_assoc.trans Measure.comp_assoc
      _ = ((κ ∥ₖ Kernel.id) ∘ₖ Kernel.copy Ω) ∘ₘ μ :=
        Measure.comp_congr <| ae_of_all _ fun a ↦ DFunLike.congr_fun hkernel a
      _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := Measure.comp_assoc.symm

lemma posterior_prod_id_comp [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    (η ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ ⊗ₘ κ := by
  calc
    (η ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ =
        Kernel.swap 𝓧 Ω ∘ₘ (Kernel.id ×ₖ η) ∘ₘ κ ∘ₘ μ := by
      simp only [Measure.comp_assoc]
      apply Measure.comp_congr
      filter_upwards [] with a
      rw [← Kernel.comp_assoc, Kernel.swap_prod]
    _ = Kernel.swap 𝓧 Ω ∘ₘ ((κ ∘ₘ μ) ⊗ₘ η) := by
      simp only [Measure.compProd_eq_comp_prod]
    _ = Kernel.swap 𝓧 Ω ∘ₘ Kernel.swap Ω 𝓧 ∘ₘ (μ ⊗ₘ κ) := by
      simp only [compProd_posterior_eq_swap_comp hη]
    _ = μ ⊗ₘ κ := by
      simp only [Measure.comp_assoc, Kernel.swap_swap, Measure.id_comp]

/-- The identity kernel represents the posterior of the identity kernel. -/
lemma id_mem_posterior_id (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.id ∈ (Kernel.id : Kernel Ω Ω)†μ := by
  refine mem_posterior_of_compProd_eq_swap_comp ?_
  simp only [Measure.id_comp, Measure.compProd_id_eq_copy_comp, Measure.comp_assoc,
    Kernel.swap_copy]

/-- For a deterministic kernel `κ` and a Markov representative `η` of `κ†μ`, `κ ∘ₖ η` is
`μ.map f`-a.e. equal to the identity kernel. -/
lemma deterministic_comp_posterior [SigmaAlgebra.CountablyGenerated 𝓧]
    {f : Ω → 𝓧} (hf : Measurable f) [IsMarkovKernel η]
    (hη : η ∈ (Kernel.deterministic f hf)†μ) :
    Kernel.deterministic f hf ∘ₖ η =ᵐ[μ.map f] Kernel.id := by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f ⊗ₘ (Kernel.deterministic f hf ∘ₖ η)
  _ = (Kernel.deterministic f hf ∘ₘ μ) ⊗ₘ (Kernel.deterministic f hf ∘ₖ η) := by
    rw [Measure.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ
      Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    simp only [Measure.compProd_eq_parallelComp_comp_copy_comp,
      ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy Ω ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp hη]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    have hkernel :
        (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₖ
            (Kernel.deterministic f hf ∥ₖ Kernel.id) =
          Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf := by
      rw [Kernel.parallelComp_comp_parallelComp]
      simp only [Kernel.id_comp, Kernel.comp_id]
    calc
      (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ
          (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ =
          (((Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₖ
            (Kernel.deterministic f hf ∥ₖ Kernel.id)) ∘ₖ Kernel.copy Ω) ∘ₘ μ :=
        Measure.comp_assoc.trans Measure.comp_assoc
      _ = ((Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₖ
          Kernel.copy Ω) ∘ₘ μ :=
        Measure.comp_congr <| ae_of_all _ fun a ↦ DFunLike.congr_fun
          (congrArg (fun k ↦ k ∘ₖ Kernel.copy Ω) hkernel) a
      _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ
          Kernel.copy Ω ∘ₘ μ := Measure.comp_assoc.symm
  _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    calc
      (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ =
          ((Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₖ
            Kernel.copy Ω) ∘ₘ μ := Measure.comp_assoc
      _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ :=
        Measure.comp_congr <| ae_of_all _ fun a ↦ DFunLike.congr_fun
          Kernel.parallelComp_self_comp_copy a
  _ = μ.map f ⊗ₘ Kernel.id := by
    calc
      (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ =
          Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := Measure.comp_assoc.symm
      _ = Kernel.copy 𝓧 ∘ₘ μ.map f := by
        simp only [Measure.deterministic_comp_eq_map]
      _ = μ.map f ⊗ₘ Kernel.id := Measure.compProd_id_eq_copy_comp.symm

lemma absolutelyContinuous_posterior {ν : Measure 𝓧} [SFinite ν] (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν)
    [IsFiniteKernel η] (hη : η ∈ κ†μ) :
    ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ := by
  suffices (κ ∘ₘ μ) ⊗ₘ η ≪ ν.productBySections μ by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices μ ⊗ₘ κ ≪ μ.productBySections ν by
    rw [compProd_posterior_eq_map_swap hη, ← Measure.productBySections_swap]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

section StandardBorelSpace

variable [StandardBorelSpace 𝓧] [Nonempty 𝓧]

/-- The posterior is involutive: `κ` represents the posterior, for the prior `κ ∘ₘ μ`, of every
Markov representative of `κ†μ`. -/
lemma mem_posterior_posterior [IsMarkovKernel κ] [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    κ ∈ η†(Measure.bind μ κ κ.aemeasurable) := by
  refine mem_posterior_of_compProd_eq_swap_comp ?_
  rw [posterior_comp_self hη]
  simp only [compProd_posterior_eq_swap_comp hη, Measure.comp_assoc, Kernel.swap_swap,
    Measure.id_comp]

/-- The posterior is contravariant: for Markov representatives `ξ` of `κ†μ` and `ζ` of
`η†(κ ∘ₘ μ)`, the kernel `ξ ∘ₖ ζ` represents `(η ∘ₖ κ)†μ`. -/
lemma comp_mem_posterior_comp {η : Kernel 𝓧 𝓨} [IsFiniteKernel η] {ξ : Kernel 𝓧 Ω}
    [IsMarkovKernel ξ] (hξ : ξ ∈ κ†μ) {ζ : Kernel 𝓨 𝓧} [IsMarkovKernel ζ]
    (hζ : ζ ∈ η†(Measure.bind μ κ κ.aemeasurable)) :
    ξ ∘ₖ ζ ∈ (η ∘ₖ κ)†μ := by
  refine mem_posterior_of_compProd_eq_swap_comp ?_
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ ξ) ∘ₘ (Kernel.id ∥ₖ ζ) ∘ₘ (Kernel.copy 𝓨) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ ξ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp hζ]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ ξ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    calc
      (Kernel.id ∥ₖ ξ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ =
          ((Kernel.id ∥ₖ ξ) ∘ₖ (η ∥ₖ Kernel.id)) ∘ₘ
            Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := Measure.comp_assoc
      _ = ((η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ ξ)) ∘ₘ
          Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ :=
        Measure.comp_congr <| ae_of_all _ fun a ↦ DFunLike.congr_fun
          Kernel.parallelComp_comm a
      _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ ξ) ∘ₘ
          Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := Measure.comp_assoc.symm
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp hξ]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    have hleft :
        (η ∥ₖ (Kernel.id : Kernel Ω Ω)) ∘ₖ
            (κ ∥ₖ (Kernel.id : Kernel Ω Ω)) =
          (η ∘ₖ κ) ∥ₖ (Kernel.id : Kernel Ω Ω) := by
      rw [Kernel.parallelComp_comp_parallelComp]
      simp only [Kernel.id_comp]
    have hright :
        ((Kernel.id : Kernel Ω Ω) ∥ₖ η) ∘ₖ
            ((Kernel.id : Kernel Ω Ω) ∥ₖ κ) =
          (Kernel.id : Kernel Ω Ω) ∥ₖ (η ∘ₖ κ) := by
      rw [Kernel.parallelComp_comp_parallelComp]
      simp only [Kernel.id_comp]
    have hkernel :
        (η ∥ₖ Kernel.id) ∘ₖ ((κ ∥ₖ Kernel.id) ∘ₖ Kernel.copy Ω) =
          Kernel.swap Ω 𝓨 ∘ₖ ((Kernel.id ∥ₖ η) ∘ₖ
            ((Kernel.id ∥ₖ κ) ∘ₖ Kernel.copy Ω)) := by
      calc
        (η ∥ₖ Kernel.id) ∘ₖ ((κ ∥ₖ Kernel.id) ∘ₖ Kernel.copy Ω) =
            ((η ∥ₖ Kernel.id) ∘ₖ (κ ∥ₖ Kernel.id)) ∘ₖ Kernel.copy Ω :=
          (Kernel.comp_assoc _ _ _).symm
        _ = ((η ∘ₖ κ) ∥ₖ Kernel.id) ∘ₖ Kernel.copy Ω :=
          congrArg (fun q ↦ q ∘ₖ Kernel.copy Ω) hleft
        _ = ((η ∘ₖ κ) ∥ₖ Kernel.id) ∘ₖ
            (Kernel.swap Ω Ω ∘ₖ Kernel.copy Ω) :=
          congrArg (((η ∘ₖ κ) ∥ₖ Kernel.id) ∘ₖ ·) Kernel.swap_copy.symm
        _ = (((η ∘ₖ κ) ∥ₖ Kernel.id) ∘ₖ Kernel.swap Ω Ω) ∘ₖ
            Kernel.copy Ω := (Kernel.comp_assoc _ _ _).symm
        _ = (Kernel.swap Ω 𝓨 ∘ₖ (Kernel.id ∥ₖ (η ∘ₖ κ))) ∘ₖ
            Kernel.copy Ω :=
          congrArg (fun q ↦ q ∘ₖ Kernel.copy Ω) Kernel.swap_parallelComp.symm
        _ = Kernel.swap Ω 𝓨 ∘ₖ ((Kernel.id ∥ₖ (η ∘ₖ κ)) ∘ₖ
            Kernel.copy Ω) := Kernel.comp_assoc _ _ _
        _ = Kernel.swap Ω 𝓨 ∘ₖ (((Kernel.id ∥ₖ η) ∘ₖ
            (Kernel.id ∥ₖ κ)) ∘ₖ Kernel.copy Ω) :=
          congrArg (fun q ↦ Kernel.swap Ω 𝓨 ∘ₖ (q ∘ₖ Kernel.copy Ω)) hright.symm
        _ = Kernel.swap Ω 𝓨 ∘ₖ ((Kernel.id ∥ₖ η) ∘ₖ
            ((Kernel.id ∥ₖ κ) ∘ₖ Kernel.copy Ω)) :=
          congrArg (Kernel.swap Ω 𝓨 ∘ₖ ·) (Kernel.comp_assoc _ _ _)
    simp only [Measure.comp_assoc]
    exact Measure.comp_congr <| ae_of_all _ fun a ↦ DFunLike.congr_fun hkernel a

end StandardBorelSpace


section CountableOrCountablyGenerated

variable [SigmaAlgebra.CountableOrCountablyGenerated Ω 𝓧]

lemma absolutelyContinuous_of_posterior [IsSFiniteKernel η] (hη : η ∈ κ†μ)
    (h_ac : ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  suffices μ ⊗ₘ κ ≪ μ.productBySections (Measure.bind μ κ κ.aemeasurable) by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices (κ ∘ₘ μ) ⊗ₘ η ≪ (κ ∘ₘ μ).productBySections μ by
    rw [← swap_compProd_posterior hη, ← Measure.productBySections_swap, Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

lemma absolutelyContinuous_posterior_iff [IsFiniteKernel η] (hη : η ∈ κ†μ) :
    (∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) ↔ ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  ⟨absolutelyContinuous_of_posterior hη, fun h ↦ absolutelyContinuous_posterior h hη⟩

lemma Kernel.absolutelyContinuous_comp_of_absolutelyContinuous {ν : Measure 𝓧} [SFinite ν]
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  obtain ⟨η, _, hη⟩ := exists_isMarkovKernel_mem_posterior (κ := κ) (μ := μ)
  rw [← absolutelyContinuous_posterior_iff hη]
  exact absolutelyContinuous_posterior h_ac hη

lemma rnDeriv_posterior_ae_prod [IsMarkovKernel η] (hη : η ∈ κ†μ)
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ p ∂(μ.prod (Measure.bind μ κ κ.aemeasurable)),
      η.rnDeriv (Kernel.const _ μ) p.2 p.1 = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) p.1 p.2 := by
  rw [Measure.prod_eq_productBySections μ (Measure.bind μ κ κ.aemeasurable)]
  -- We prove the a.e. equality by showing that integrals on the π-system of rectangles are equal.
  -- First, the integral of the left-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`, which we prove
  -- by showing that it's equal to `((κ ∘ₘ μ) ⊗ η) (t ×ˢ s)` and using the main property of the
  -- posterior.
  have h1 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫⁻ x in s ×ˢ t, η.rnDeriv (Kernel.const _ μ) x.2 x.1
        ∂μ.productBySections (Measure.bind μ κ κ.aemeasurable)
        = (μ ⊗ₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_productBySections_symm _ (by fun_prop), ← swap_compProd_posterior hη,
      Measure.swap_comp, Measure.map_apply (hs.prod ht) measurable_swap.aemeasurable,
      Set.preimage_swap_prod, Measure.compProd_apply_prod ht hs]
    refine lintegral_congr_ae <| ae_restrict_of_ae ?_
    filter_upwards [absolutelyContinuous_posterior h_ac hη] with x h_ac'
    change ∫⁻ ω in s, η.rnDeriv (Kernel.const 𝓧 μ) x ω ∂(Kernel.const 𝓧 μ x) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac' hs]
  have h2 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
  -- Second, the integral of the right-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`.
      ∫⁻ x in s ×ˢ t, κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) x.1 x.2
        ∂μ.productBySections (Measure.bind μ κ κ.aemeasurable)
        = (μ ⊗ₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_productBySections _ (by fun_prop), Measure.compProd_apply_prod hs ht]
    refine lintegral_congr_ae <| ae_restrict_of_ae ?_
    filter_upwards [h_ac] with ω h_ac
    change ∫⁻ x in t, κ.rnDeriv (Kernel.const Ω (κ ∘ₘ μ)) ω x ∂(Kernel.const Ω (κ ∘ₘ μ) ω) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac ht]
  -- We extend from the π-system to the σ-algebra.
  refine ae_eq_of_setLIntegral_prod_eq (by fun_prop) (by fun_prop) ?_ ?_
  · refine ne_of_lt ?_
    calc ∫⁻ x, η.rnDeriv (Kernel.const _ μ) x.2 x.1
        ∂μ.productBySections (Measure.bind μ κ κ.aemeasurable)
    _ = (μ ⊗ₘ κ) Set.univ := by rw [← setLIntegral_univ, ← Set.univ_prod_univ, h1 .univ .univ]
    _ < ⊤ := measure_lt_top _ _
  · intro s hs t ht
    rw [h1 hs ht, h2 hs ht]

lemma rnDeriv_posterior [IsMarkovKernel η] (hη : η ∈ κ†μ) (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ ω ∂μ, ∀ᵐ x ∂(κ ∘ₘ μ),
      η.rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  have h := rnDeriv_posterior_ae_prod hη h_ac
  rw [Measure.prod_eq_productBySections μ (Measure.bind μ κ κ.aemeasurable)] at h
  convert! Measure.ae_ae_of_ae_prod h -- much faster than `exact`

lemma rnDeriv_posterior_symm [IsMarkovKernel η] (hη : η ∈ κ†μ)
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), ∀ᵐ ω ∂μ,
      η.rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  rw [Measure.ae_ae_comm]
  · exact rnDeriv_posterior hη h_ac
  · measurability

/-- If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, then for every Markov representative `η` of `κ†μ`
and `κ ∘ₘ μ`-almost every `x`,
`η x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
This is a form of **Bayes' theorem**.
The condition is true for example for countable `Ω`. -/
lemma posterior_eq_withDensity [IsMarkovKernel η] (hη : η ∈ κ†μ)
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), η x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x) := by
  filter_upwards [rnDeriv_posterior_symm hη h_ac, absolutelyContinuous_posterior h_ac hη]
    with x h h_ac'
  ext s hs
  rw [← Measure.setLIntegral_rnDeriv h_ac', withDensity_apply _ hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [h, Kernel.rnDeriv_eq_rnDeriv_measure (κ := η) (η := Kernel.const 𝓧 μ) (a := x)]
    with ω h h_eq hωs
  rw [← h, h_eq, Kernel.const_apply]

lemma posterior_eq_withDensity_of_countable {Ω : Type*} [Countable Ω] [SigmaAlgebra Ω]
    [Nonempty Ω] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {η : Kernel 𝓧 Ω} [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), η x = μ.withDensity (fun ω ↦ (κ ω).rnDeriv (κ ∘ₘ μ) x) := by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity hη Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

end CountableOrCountablyGenerated

section Bool

lemma posterior_boolKernel_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] {η : Kernel 𝓧 Bool} [IsMarkovKernel η]
    (hη : η ∈ (Kernel.boolKernel μ ν)†π) :
    ∀ᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, η x {false}
      = π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π hη] with x hx
  rw [hx]
  simp

lemma posterior_boolKernel_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] {η : Kernel 𝓧 Bool} [IsMarkovKernel η]
    (hη : η ∈ (Kernel.boolKernel μ ν)†π) :
    ∀ᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, η x {true}
      = π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π hη] with x hx
  rw [hx]
  simp

end Bool

end ProbabilityTheory

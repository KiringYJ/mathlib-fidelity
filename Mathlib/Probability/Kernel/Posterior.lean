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

import Mathlib.MeasureTheory.Measure.WithDensityFinite

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
these kernels. The statements below hold for every representative `η ∈ κ†μ` where the proof
allows, and otherwise for every finite, s-finite, or Markov one; the composition-product
`(κ ∘ₘ μ) ⊗ₘ η` exists for every representative (`hasCompProd_of_mem_posterior`). The posterior
exists when the joint law with swapped coordinates has a unique conditional kernel, which the
statements take as an instance argument; instance search supplies it when `Ω` is a nonempty
standard Borel space and `κ ∘ₘ μ` is σ-finite, which admits an infinite prior, and for the identity
kernel and every prior in a countably generated space.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`, as a class of kernels.

## Main statements

* `mem_posterior_iff_of_isMarkovKernel`: a Markov kernel `η` represents `κ†μ` if and only if
  `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`.
* `mem_posterior_iff`: if `κ ∘ₘ μ` is σ-finite, a kernel `η` for which `(κ ∘ₘ μ) ⊗ₘ η` exists
  represents `κ†μ` if and only if `(κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap`.
* `posterior_comp_self`: `η ∘ₘ κ ∘ₘ μ = μ` for a Markov kernel `κ` and every representative `η` of
  `κ†μ`.
* `mem_posterior_posterior`: `κ` represents the posterior of every Markov representative of `κ†μ`
  for the prior `κ ∘ₘ μ`.
* `comp_mem_posterior_comp`: the composition of Markov representatives of `κ†μ` and `η†(κ ∘ₘ μ)`
  represents `(η ∘ₖ κ)†μ`.

* `posterior_eq_withDensity`: If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, then for every Markov
  representative `η` of `κ†μ` and `κ ∘ₘ μ`-almost every `x`,
  `η x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
  The condition is true for countable `Ω`, and whenever `κ ω ≪ ν` for an s-finite `ν` and
  `μ`-almost every `ω`: see `Measure.absolutelyContinuous_comp_of_countable` and
  `Measure.absolutelyContinuous_comp_of_absolutelyContinuous`.

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

It exists when this joint law has a unique conditional kernel, in particular when `Ω` is a
nonempty standard Borel space and `κ ∘ₘ μ` is σ-finite
(`ProbabilityTheory.sigmaFinite_fst_map_swap_compProd`). A kernel for which
`(κ ∘ₘ μ) ⊗ₘ η` exists represents it if and only if it has this property, when `κ ∘ₘ μ` is σ-finite
(`mem_posterior_iff`), and a Markov representative exists
(`exists_isMarkovKernel_mem_posterior`). -/
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

/-- The composition-product of `κ ∘ₘ μ` with a representative of `κ†μ` exists, since the
representative disintegrates the joint law with swapped coordinates, whose first marginal is
`κ ∘ₘ μ`. -/
lemma hasCompProd_of_mem_posterior (hη : η ∈ κ†μ) : (κ ∘ₘ μ).HasCompProd η := by
  have := Measure.isCondKernel_of_mem_condKernel (mem_posterior_iff_mem_condKernel.1 hη)
  rw [← fst_map_swap_compProd κ μ]
  infer_instance

/-- The main property of the posterior, for every representative; the composition-product exists
by `hasCompProd_of_mem_posterior`. -/
lemma compProd_posterior_eq_map_swap [(κ ∘ₘ μ).HasCompProd η] (hη : η ∈ κ†μ) :
    (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
  have := Measure.isCondKernel_of_mem_condKernel (mem_posterior_iff_mem_condKernel.1 hη)
  rw [Measure.compProd_congr_measure (fst_map_swap_compProd κ μ).symm]
  exact Measure.disintegrate _ η

lemma compProd_posterior_eq_swap_comp [(κ ∘ₘ μ).HasCompProd η] (hη : η ∈ κ†μ) :
    (κ ∘ₘ μ) ⊗ₘ η = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ := by
  rw [compProd_posterior_eq_map_swap hη, Measure.swap_comp]

lemma posterior_comp_self [IsMarkovKernel κ] (hη : η ∈ κ†μ) :
    η ∘ₘ κ ∘ₘ μ = μ := by
  have := hasCompProd_of_mem_posterior hη
  rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap hη, Measure.snd_map_swap,
    Measure.fst_compProd]

/-- A Markov kernel with the main property of the posterior represents it. Unlike for a kernel that
is not Markov (`mem_posterior_of_compProd_eq`), the class of the joint law with swapped coordinates
suffices. -/
lemma mem_posterior_of_compProd_eq_of_isMarkovKernel [IsMarkovKernel η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η ∈ κ†μ :=
  mem_posterior_iff_mem_condKernel.2 <| Measure.mem_condKernel_iff_of_isMarkovKernel.2
    (.of_compProd_eq (fst_map_swap_compProd κ μ) h)

/-- A Markov kernel represents the posterior if and only if it has its main property. -/
lemma mem_posterior_iff_of_isMarkovKernel [IsMarkovKernel η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  ⟨compProd_posterior_eq_map_swap, mem_posterior_of_compProd_eq_of_isMarkovKernel⟩

/-- A Markov kernel `η` with `(κ ∘ₘ μ) ⊗ₘ η = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ` represents the
posterior. -/
lemma mem_posterior_of_compProd_eq_swap_comp_of_isMarkovKernel [IsMarkovKernel η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ) :
    η ∈ κ†μ :=
  mem_posterior_of_compProd_eq_of_isMarkovKernel <| by rw [h, Measure.swap_comp]

lemma swap_compProd_posterior [(κ ∘ₘ μ).HasCompProd η] (hη : η ∈ κ†μ) :
    Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) ⊗ₘ η = μ ⊗ₘ κ := by
  simp only [compProd_posterior_eq_swap_comp hη, Measure.comp_assoc, Kernel.swap_swap,
    Measure.id_comp]

lemma posterior_prod_id_comp [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
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

end HasUniqueCondKernel

section SFiniteKernel

variable [IsSFiniteKernel κ]
  [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] {η : Kernel 𝓧 Ω}

/-- The main property of the posterior, as equality of the following diagrams:
```
         -- id          -- κ
μ -- κ -|        =  μ -|
         -- η           -- id
```
for every s-finite representative `η` of `κ†μ`. -/
lemma parallelProd_posterior_comp_copy_comp [IsSFiniteKernel η] (hη : η ∈ κ†μ) :
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

end SFiniteKernel

/-- The joint law with swapped coordinates of a measure and the identity kernel, the law of
`(ω, ω)`, has a unique conditional kernel, for every measure, in a countably generated space
(`MeasureTheory.Measure.hasUniqueCondKernel_map_prodMk_comp`). -/
instance hasUniqueCondKernel_map_swap_compProd_id [SigmaAlgebra.CountablyGenerated Ω]
    (μ : Measure Ω) :
    ((μ ⊗ₘ (Kernel.id : Kernel Ω Ω)).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel := by
  have h : (μ ⊗ₘ (Kernel.id : Kernel Ω Ω)).map Prod.swap measurable_swap.aemeasurable =
      μ.map (fun ω ↦ (id ω, (id ∘ id) ω)) (aemeasurable_id.prodMk
        (measurable_id.comp_aemeasurable aemeasurable_id)) := by
    rw [Measure.compProd_id, Measure.map_map measurable_diag.aemeasurable
      measurable_swap.aemeasurable]
    rfl
  rw [h]
  exact Measure.hasUniqueCondKernel_map_prodMk_comp aemeasurable_id measurable_id

/-- The identity kernel represents the posterior of the identity kernel. -/
lemma id_mem_posterior_id (μ : Measure Ω)
    [((μ ⊗ₘ (Kernel.id : Kernel Ω Ω)).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel] :
    Kernel.id ∈ (Kernel.id : Kernel Ω Ω)†μ := by
  refine mem_posterior_of_compProd_eq_swap_comp_of_isMarkovKernel ?_
  simp only [Measure.id_comp, Measure.compProd_id_eq_copy_comp, Measure.comp_assoc,
    Kernel.swap_copy]

/-- For a deterministic kernel `κ` and a Markov representative `η` of `κ†μ`, `κ ∘ₖ η` is
`μ.map f`-a.e. equal to the identity kernel. The class of the joint law suffices, with no
finiteness of `μ.map f`: by the main property of the posterior, `η x (f ⁻¹' s) = 0` for almost
every `x ∉ s` (`ProbabilityTheory.Kernel.ae_eq_deterministic_iff`). -/
lemma deterministic_comp_posterior [SigmaAlgebra.CountablyGenerated 𝓧]
    {f : Ω → 𝓧} (hf : Measurable f)
    [((μ ⊗ₘ Kernel.deterministic f hf).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    {η : Kernel 𝓧 Ω} [IsMarkovKernel η] (hη : η ∈ (Kernel.deterministic f hf)†μ) :
    Kernel.deterministic f hf ∘ₖ η =ᵐ[μ.map f] Kernel.id := by
  have := Kernel.IsMarkovKernel.map η hf
  rw [Kernel.deterministic_comp_eq_map]
  refine (Kernel.ae_eq_deterministic_iff (g := id) measurable_id).2 fun s hs ↦ ?_
  have hfs : MeasurableSet (f ⁻¹' s) := hf hs
  have h0 : ((Kernel.deterministic f hf ∘ₘ μ) ⊗ₘ η) (sᶜ ×ˢ (f ⁻¹' s)) = 0 := by
    rw [compProd_posterior_eq_map_swap hη,
      Measure.map_apply (hs.compl.prod hfs) measurable_swap.aemeasurable,
      Set.preimage_swap_prod, Measure.compProd_deterministic,
      Measure.map_apply (hfs.prod hs.compl) (measurable_id'.prodMk hf).aemeasurable]
    convert measure_empty (μ := μ)
    ext a
    simp
  rw [Measure.compProd_apply_prod hs.compl hfs, Measure.deterministic_comp_eq_map,
    setLIntegral_eq_zero_iff hs.compl (η.measurable_coe hfs)] at h0
  filter_upwards [h0] with x hx hxs
  rw [Kernel.map_apply' η x hs hf]
  exact hx hxs

/-- The posterior is involutive: `κ` represents the posterior, for the prior `κ ∘ₘ μ`, of every
Markov representative of `κ†μ`. -/
lemma mem_posterior_posterior [IsMarkovKernel κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    {η : Kernel 𝓧 Ω} [IsMarkovKernel η]
    [((Measure.bind μ κ κ.aemeasurable ⊗ₘ η).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    (hη : η ∈ κ†μ) :
    κ ∈ η†(Measure.bind μ κ κ.aemeasurable) := by
  refine mem_posterior_of_compProd_eq_swap_comp_of_isMarkovKernel ?_
  rw [posterior_comp_self hη]
  simp only [compProd_posterior_eq_swap_comp hη, Measure.comp_assoc, Kernel.swap_swap,
    Measure.id_comp]

/-- The posterior is contravariant: for Markov representatives `ξ` of `κ†μ` and `ζ` of
`η†(κ ∘ₘ μ)`, the kernel `ξ ∘ₖ ζ` represents `(η ∘ₖ κ)†μ`. -/
lemma comp_mem_posterior_comp [IsSFiniteKernel κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    {η : Kernel 𝓧 𝓨} [IsSFiniteKernel η]
    [((Measure.bind μ κ κ.aemeasurable ⊗ₘ η).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    [((μ ⊗ₘ (η ∘ₖ κ)).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    {ξ : Kernel 𝓧 Ω} [IsMarkovKernel ξ] (hξ : ξ ∈ κ†μ) {ζ : Kernel 𝓨 𝓧} [IsMarkovKernel ζ]
    (hζ : ζ ∈ η†(Measure.bind μ κ κ.aemeasurable)) :
    ξ ∘ₖ ζ ∈ (η ∘ₖ κ)†μ := by
  refine mem_posterior_of_compProd_eq_swap_comp_of_isMarkovKernel ?_
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

section AbsolutelyContinuous

variable [μ.HasCompProd κ]
  [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] {η : Kernel 𝓧 Ω}

/-- The case of a finite representative of `absolutelyContinuous_posterior`. -/
private lemma absolutelyContinuous_posterior_of_isFiniteKernel
    [SigmaAlgebra.CountableOrCountablyGenerated 𝓧 Ω] {ν : Measure 𝓧} [SFinite ν]
    (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν) [IsFiniteKernel η] (hη : η ∈ κ†μ) :
    ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ := by
  have : SFinite (κ ∘ₘ μ) := sFinite_of_absolutelyContinuous (ν := ν) <|
    Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ by
      rw [Measure.bind_apply hs κ.aemeasurable, lintegral_eq_zero_iff (κ.measurable_coe hs)]
      filter_upwards [h_ac] with ω hω using hω hs0
  have h_fst : η ∘ₘ (κ ∘ₘ μ) = μ.withDensity fun ω ↦ κ ω Set.univ := by
    rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap hη, Measure.snd_map_swap]
    ext s hs
    rw [Measure.fst_apply hs, ← Set.prod_univ, Measure.compProd_apply_prod hs .univ,
      withDensity_apply _ hs]
  have h_marginal : η ∘ₘ (κ ∘ₘ μ) ≪ μ := by
    rw [h_fst]
    exact withDensity_absolutelyContinuous _ _
  have h_joint : μ ⊗ₘ κ ≪ (η ∘ₘ (κ ∘ₘ μ)) ⊗ₘ Kernel.const Ω ν := by
    refine Measure.AbsolutelyContinuous.mk fun E hE hE0 ↦ ?_
    rw [Measure.compProd_apply hE, h_fst] at hE0
    simp only [Kernel.const_apply] at hE0
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hE), Filter.EventuallyEq,
      ae_withDensity_iff (κ.measurable_coe .univ)] at hE0
    rw [Measure.compProd_apply hE]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hE0, h_ac] with ω h₁ h₂
    by_cases hω : κ ω Set.univ = 0
    · exact measure_mono_null (Set.subset_univ _) hω
    · exact h₂ (h₁ hω)
  have h_swap : (κ ∘ₘ μ) ⊗ₘ η ≪ ν ⊗ₘ Kernel.const 𝓧
      (Measure.bind (Measure.bind μ κ κ.aemeasurable) η η.aemeasurable).toFinite := by
    have h := (h_joint.trans
      ((absolutelyContinuous_toFinite _).compProd_left (Kernel.const Ω ν))).map measurable_swap
    rwa [Measure.compProd_const, Measure.productBySections_swap, ← Measure.compProd_const,
      ← compProd_posterior_eq_map_swap hη] at h
  filter_upwards [h_swap.kernel_of_compProd] with b hb
  exact (hb.trans (toFinite_absolutelyContinuous _)).trans h_marginal

/-- If `κ ω ≪ ν` for `μ`-almost every `ω`, then `η x ≪ μ` for `κ ∘ₘ μ`-almost every `x` and every
representative `η` of `κ†μ`, for every prior `μ`. Then `κ ∘ₘ μ`, being `≪ ν`, is s-finite, and
so is the first marginal `η ∘ₘ κ ∘ₘ μ` of the joint law for a Markov representative `η`, which is
`μ` weighted by `κ · univ`. The joint law is absolutely continuous with respect to the product of
that marginal with `ν`, and the finite measure with the null sets of the marginal reduces the
statement to finite kernels. The statement does not depend on the representative. -/
lemma absolutelyContinuous_posterior [SigmaAlgebra.CountableOrCountablyGenerated 𝓧 Ω]
    {ν : Measure 𝓧} [SFinite ν] (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ν) (hη : η ∈ κ†μ) :
    ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ := by
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_posterior (κ := κ) (μ := μ)
  filter_upwards [absolutelyContinuous_posterior_of_isFiniteKernel h_ac hη₀,
    Kernel.AEClass.eventuallyEq_of_mem hη₀ hη] with b hb hb_eq
  rwa [← hb_eq]

/-- The case of an s-finite prior of `absolutelyContinuous_of_posterior`: the joint law is
absolutely continuous with respect to the product of the prior with `(κ ∘ₘ μ).toFinite`. -/
private lemma absolutelyContinuous_of_posterior_of_sFinite
    [SigmaAlgebra.CountableOrCountablyGenerated Ω 𝓧] [SFinite μ] [IsFiniteKernel κ]
    (hη : η ∈ κ†μ) (h_ac : ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  have := hasCompProd_of_mem_posterior hη
  have h_toFinite : μ ⊗ₘ Kernel.const Ω (Measure.bind μ κ κ.aemeasurable) ≪
      μ ⊗ₘ Kernel.const Ω (Measure.bind μ κ κ.aemeasurable).toFinite :=
    Measure.AbsolutelyContinuous.compProd_right
      (ae_of_all _ fun _ ↦ absolutelyContinuous_toFinite _)
  suffices μ ⊗ₘ κ ≪ μ ⊗ₘ Kernel.const Ω (κ ∘ₘ μ) by
    filter_upwards [(this.trans h_toFinite).kernel_of_compProd] with ω hω
    exact hω.trans (toFinite_absolutelyContinuous _)
  rw [Measure.compProd_const]
  suffices (κ ∘ₘ μ) ⊗ₘ η ≪ (κ ∘ₘ μ).productBySections μ by
    rw [← swap_compProd_posterior hη, ← Measure.productBySections_swap, Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

/-- If `η x ≪ μ` for `κ ∘ₘ μ`-almost every `x`, for a representative `η` of `κ†μ`, then
`κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`, if `κ ∘ₘ μ` is s-finite. Off the set `A` of the points
`ω` with `κ ω ≠ 0` this holds trivially. The prior restricted to `A` has the same joint law and
posterior, its posterior gives no mass to the complement of `A`, and it is s-finite, being
absolutely continuous with respect to the first marginal of the joint law, which is `η₀ ∘ₘ κ ∘ₘ μ`
for a Markov representative `η₀`; an s-finite prior reduces to the comparison of the joint law with
the product of the prior with `(κ ∘ₘ μ).toFinite`. -/
lemma absolutelyContinuous_of_posterior [SigmaAlgebra.CountableOrCountablyGenerated Ω 𝓧]
    [SFinite (κ ∘ₘ μ)] [IsFiniteKernel κ] (hη : η ∈ κ†μ)
    (h_ac : ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  set A : Set Ω := {ω | κ ω Set.univ ≠ 0}
  have hA : MeasurableSet A := (κ.measurable_coe .univ) (measurableSet_singleton 0).compl
  have h_zero (ω : Ω) (hω : ω ∉ A) : κ ω = 0 := Measure.measure_univ_eq_zero.1 (not_not.1 hω)
  have h_joint : μ.restrict A ⊗ₘ κ = μ ⊗ₘ κ := by
    ext s hs
    rw [Measure.compProd_apply hs, Measure.compProd_apply hs, ← lintegral_indicator hA]
    congr 1 with ω
    by_cases hω : ω ∈ A
    · simp [hω]
    · simp [hω, h_zero ω hω]
  have h_comp : κ ∘ₘ μ.restrict A = κ ∘ₘ μ := by
    rw [← Measure.snd_compProd, h_joint, Measure.snd_compProd]
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_posterior (κ := κ) (μ := μ)
  have h_fst : η₀ ∘ₘ (κ ∘ₘ μ) = μ.withDensity fun ω ↦ κ ω Set.univ := by
    rw [← Measure.snd_compProd, compProd_posterior_eq_map_swap hη₀, Measure.snd_map_swap]
    ext s hs
    rw [Measure.fst_apply hs, ← Set.prod_univ, Measure.compProd_apply_prod hs .univ,
      withDensity_apply _ hs]
  have : SFinite (μ.restrict A) := by
    refine sFinite_of_absolutelyContinuous (ν := η₀ ∘ₘ (κ ∘ₘ μ))
      (Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_)
    rw [h_fst, withDensity_apply _ hs, lintegral_eq_zero_iff (κ.measurable_coe .univ)] at hs0
    have h0 : ∀ᵐ ω ∂μ.restrict s, ω ∉ A := hs0.mono fun ω hω hωA ↦ hωA hω
    have h1 : μ (A ∩ s) = 0 := by
      rw [ae_iff, Measure.restrict_apply' hs] at h0
      simpa using h0
    rwa [Measure.restrict_apply hs, Set.inter_comm]
  have : ((μ.restrict A ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel :=
    h_joint ▸ inferInstance
  have hη' : η ∈ κ†(μ.restrict A) := by
    rw [mem_posterior_iff_mem_condKernel,
      Measure.mem_condKernel_congr (ρ' := (μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable)
        (by rw [h_joint])]
    exact mem_posterior_iff_mem_condKernel.1 hη
  have h_null : ∀ᵐ b ∂(κ ∘ₘ μ), η b Aᶜ = 0 := by
    have := hasCompProd_of_mem_posterior hη
    have h0 : ((κ ∘ₘ μ) ⊗ₘ η) (Set.univ ×ˢ Aᶜ) = 0 := by
      rw [compProd_posterior_eq_map_swap hη,
        Measure.map_apply (MeasurableSet.univ.prod hA.compl) measurable_swap.aemeasurable,
        Set.preimage_swap_prod, Measure.compProd_apply_prod hA.compl .univ]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [ae_restrict_mem hA.compl] with ω hω
      simp [h_zero ω hω]
    rw [Measure.compProd_apply_prod .univ hA.compl, Measure.restrict_univ,
      lintegral_eq_zero_iff (η.measurable_coe hA.compl)] at h0
    exact h0
  have h_ac' : ∀ᵐ b ∂(κ ∘ₘ μ.restrict A), η b ≪ μ.restrict A := by
    rw [h_comp]
    filter_upwards [h_ac, h_null] with b hb hb0
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ le_antisymm ?_ zero_le
    rw [Measure.restrict_apply hs] at hs0
    calc η b s ≤ η b (s ∩ A) + η b (s \ A) := measure_le_inter_add_sdiff _ _ _
      _ = 0 := by rw [hb hs0, measure_mono_null (fun x hx ↦ hx.2) hb0, add_zero]
  have h := absolutelyContinuous_of_posterior_of_sFinite (μ := μ.restrict A) hη' h_ac'
  rw [h_comp, ae_restrict_iff' hA] at h
  filter_upwards [h] with ω hω
  by_cases hωA : ω ∈ A
  · exact hω hωA
  · rw [h_zero ω hωA]
    exact Measure.AbsolutelyContinuous.zero _

lemma absolutelyContinuous_posterior_iff [SigmaAlgebra.CountableOrCountablyGenerated Ω 𝓧]
    [SigmaAlgebra.CountableOrCountablyGenerated 𝓧 Ω] [SFinite (κ ∘ₘ μ)] [IsFiniteKernel κ]
    (hη : η ∈ κ†μ) :
    (∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) ↔ ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  ⟨absolutelyContinuous_of_posterior hη, fun h ↦ absolutelyContinuous_posterior h hη⟩

section RadonNikodym

variable [SigmaAlgebra.CountableOrCountablyGenerated Ω 𝓧]
  [SigmaAlgebra.CountableOrCountablyGenerated 𝓧 Ω] [IsFiniteMeasure μ] [IsFiniteKernel κ]

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

end RadonNikodym

end AbsolutelyContinuous

section SigmaFinite

variable [μ.HasCompProd κ]
  [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
  [SigmaFinite (κ ∘ₘ μ)] {η : Kernel 𝓧 Ω}

/-- A kernel with the main property of the posterior represents it, if `κ ∘ₘ μ` is σ-finite. -/
lemma mem_posterior_of_compProd_eq [(κ ∘ₘ μ).HasCompProd η]
    (h : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap) :
    η ∈ κ†μ := by
  have : ((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).IsCondKernel η :=
    .of_compProd_eq (fst_map_swap_compProd κ μ) h
  exact mem_posterior_iff_mem_condKernel.2 Measure.IsCondKernel.mem_condKernel

/-- A kernel for which `(κ ∘ₘ μ) ⊗ₘ η` exists represents the posterior if and only if it has its
main property, if `κ ∘ₘ μ` is σ-finite. -/
lemma mem_posterior_iff [(κ ∘ₘ μ).HasCompProd η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  ⟨compProd_posterior_eq_map_swap, mem_posterior_of_compProd_eq⟩

/-- A kernel `η` with `(κ ∘ₘ μ) ⊗ₘ η = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ` represents the posterior, if
`κ ∘ₘ μ` is σ-finite. -/
lemma mem_posterior_of_compProd_eq_swap_comp [(κ ∘ₘ μ).HasCompProd η]
    (h : ((κ ∘ₘ μ) ⊗ₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ ⊗ₘ κ) :
    η ∈ κ†μ :=
  mem_posterior_of_compProd_eq <| by rw [h, Measure.swap_comp]

end SigmaFinite

/-- **Bayes' theorem** for a countable parameter space: for every Markov representative `η` of
`κ†μ` and `κ ∘ₘ μ`-almost every `x`, `η x` is `μ` weighted by the densities of the measures `κ ω`
with respect to `κ ∘ₘ μ`, which dominates `κ ω` for `μ`-almost every `ω`
(`Measure.absolutelyContinuous_comp_of_countable`). -/
lemma posterior_eq_withDensity_of_countable {Ω : Type*} [Countable Ω] [SigmaAlgebra Ω]
    (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    {η : Kernel 𝓧 Ω} [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), η x = μ.withDensity (fun ω ↦ (κ ω).rnDeriv (κ ∘ₘ μ) x) := by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity hη Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

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

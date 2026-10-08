/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.AEClass
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.FiberwiseAE
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.Density
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Existence of disintegration of measures and kernels for standard Borel spaces

Let `κ : Kernel α (β × Ω)` be a finite kernel, where `Ω` is a nonempty standard Borel space. Then
if `α` is countable or `β` has a countably generated σ-algebra (for example if it is standard
Borel), then there exists a Markov kernel `η : Kernel (α × β) Ω` such that `κ = fst κ ⊗ₖ η`. The
conditional kernel `condKernel κ` is the class of these kernels up to `fst κ a`-null sets for every
`a`.
We also define the conditional kernel of a measure `ρ : Measure (β × Ω)` with a unique conditional
kernel (`MeasureTheory.Measure.HasUniqueCondKernel`): the `ρ.fst`-almost-everywhere class
`ρ.condKernel` of the Markov kernels `η : Kernel β Ω` with `ρ = ρ.fst ⊗ₘ η`. A measure whose first
marginal is σ-finite, for a nonempty standard Borel space `Ω`, has a unique conditional kernel (see
the file `Unique.lean`): such a measure becomes finite when it is reweighted by a positive function
of the first coordinate with a finite integral, and a disintegration of the reweighted measure
disintegrates the measure.
A conditional kernel is determined almost everywhere (see the file `Unique.lean`), and only almost
everywhere: every Markov kernel that agrees with a conditional kernel almost everywhere is one too
(`MeasureTheory.Measure.compProd_congr`, `ProbabilityTheory.Kernel.compProd_congr`). So `κ` and `ρ`
determine these classes, but not the values of a conditional kernel on null sets.

In order to obtain a disintegration for any standard Borel space `Ω`, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. The private
construction `borelMarkovFromReal` pulls a Markov kernel to `ℝ` back along the embedding and uses a
Dirac mass at an arbitrary point of `Ω` wherever the measure on `ℝ` gives positive mass to the
complement of the range of the embedding. For the conditional kernels of the image of `κ` in
`β × ℝ` built below, this happens only on `fst κ a`-null sets, and the construction serves only to
build the witnesses of the existence statements.

For `κ : Kernel α (β × ℝ)`, the construction of a conditional kernel proceeds as follows:
* Build a measurable function `f : (α × β) → ℚ → ℝ` such that for all measurable sets
  `s` and all `q : ℚ`, `∫ x in s, f (a, x) q ∂(Kernel.fst κ a) = (κ a).real (s ×ˢ Iic (q : ℝ))`.
  We restrict to `ℚ` here to be able to prove the measurability.
* Choose a measurable function `(α × β) → StieltjesFunction ℝ` with the property `IsCondKernelCDF`
  that agrees with it almost everywhere at every rational. Its existence is proved in the file
  `CDFToKernel.lean`, with the tools of the file `MeasurableStieltjes.lean`.
* Finally obtain from the measurable Stieltjes function a measure on `ℝ` for each element of `α × β`
  in a measurable way: we have obtained a `Kernel (α × β) ℝ`.
  See the file `CDFToKernel.lean` for that step.

The first step (building the measurable function on `ℚ`) is done differently depending on whether
`α` is countable or not.
* If `α` is countable, we can proceed separately for each `a : α`: the finite measure `κ a` is
  disintegrated by a Markov kernel `Kernel β Ω`
  (`MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`). Since `α` is countable,
  measurability is not an issue and we can put chosen such kernels together into a
  `Kernel (α × β) Ω`, which serves as the witness of the existence statement. For a measure on
  `β × ℝ`, a conditional kernel is built from the kernel of a conditional cdf in the sense of
  `ProbabilityTheory.IsCondCDF`, whose existence is proved in the `CondCDF.lean` file; for a general
  standard Borel space `Ω`, we go through the measurable embedding of `Ω` into `ℝ`.
* If `α` is not countable, we can't proceed separately for each `a : α` and have to build a function
  `f : α × β → ℚ → ℝ` which is measurable on the product. We are able to do so if `β` has a
  countably generated σ-algebra (this is the case in particular for standard Borel spaces).
  See the file `Density.lean`.

The conditional kernel is defined under the typeclass assumption
`CountableOrCountablyGenerated α β`, which encodes the property
`Countable α ∨ CountablyGenerated β`.

Properties of integrals against conditional kernels are collated in the file `Integral.lean`.
Conditional kernels are unique almost everywhere, so that the finite representatives of the classes
are exactly the finite conditional kernels: this is proved in the file `Unique.lean`.

## Main definitions

* `ProbabilityTheory.Kernel.condKernel κ : Kernel.AEClass (fst κ).fiberwiseAE Ω`: the conditional
  kernel described above.
* `MeasureTheory.Measure.condKernel ρ : Kernel.AEClass (ae ρ.fst) Ω`: the conditional kernel of a
  measure.

## Main statements

* `ProbabilityTheory.Kernel.exists_isMarkovKernel_isCondKernel`: a Markov kernel `η` with
  `fst κ ⊗ₖ η = κ` exists.
* `MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`: a Markov kernel `η` with
  `ρ.fst ⊗ₘ η = ρ` exists if `ρ.fst` is σ-finite.
* `ProbabilityTheory.Kernel.exists_isMarkovKernel_mem_condKernel` and
  `MeasureTheory.Measure.exists_isMarkovKernel_mem_condKernel`: the conditional kernels are
  represented by Markov kernels that disintegrate `κ`, respectively `ρ`. The file `Unique.lean`
  shows that the Markov representatives are exactly these Markov kernels.
-/

@[expose] public section

open MeasureTheory Set Filter SigmaAlgebra

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ Ω : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {mγ : SigmaAlgebra γ} [SigmaAlgebra.CountablyGenerated γ]
  {mΩ : SigmaAlgebra Ω} [StandardBorelSpace Ω] [Nonempty Ω]

section Real

/-! ### Disintegration of kernels from `α` to `γ × ℝ` for countably generated `γ` -/

lemma isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) where
  measurable := measurable_pi_iff.mpr fun _ ↦ measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ ↦ density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    · ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    rw [fst_real_apply _ _ MeasurableSet.univ]
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ ≤ fst κ)
      a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · exact fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a _ := integrable_density le_rfl a measurableSet_Iic
  setIntegral a _ hA _ := setIntegral_density le_rfl a measurableSet_Iic hA

/-- Taking the kernel density of intervals `Iic q` for `q : ℚ` gives a function with the property
`isRatCondKernelCDF`. -/
lemma isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

/-- Some germ along `(fst κ).fiberwiseAE` is represented by a conditional kernel CDF of `κ` with
respect to `fst κ`. Since two conditional kernel CDFs agree `fst κ a`-almost everywhere for every
`a` (`ProbabilityTheory.IsCondKernelCDF.ae_eq`), such a germ is unique, and every conditional
kernel CDF represents it (`ProbabilityTheory.IsCondKernelCDF.mem_condKernelCDF`). -/
lemma exists_germ_isCondKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    ∃ φ : (fst κ).fiberwiseAE.Germ (StieltjesFunction ℝ), ∃ f,
      IsCondKernelCDF f κ (fst κ) ∧ f ∈ φ :=
  let ⟨f, hf, _⟩ := (isRatCondKernelCDF_density_Iic κ).exists_isCondKernelCDF
  ⟨f, f, hf, Filter.Germ.coe_mem f⟩

/-- The conditional kernel CDF of a finite kernel `κ : Kernel α (γ × ℝ)` with respect to `fst κ`,
where `γ` is countably generated: the class of the conditional kernel CDFs of `κ` along
`(fst κ).fiberwiseAE`, that is, up to `fst κ a`-null sets for every `a`.

A family `f` represents it, written `f ∈ condKernelCDF κ`, when for every `a` it agrees
`fst κ a`-almost everywhere with a conditional kernel CDF of `κ`. Every conditional kernel CDF
represents it (`ProbabilityTheory.IsCondKernelCDF.mem_condKernelCDF`); one exists by
`isRatCondKernelCDF_density_Iic`. The values of a conditional kernel CDF on `fst κ a`-null sets are
not determined by `κ` (`ProbabilityTheory.IsCondKernelCDF.congr`). -/
noncomputable
def condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    (fst κ).fiberwiseAE.Germ (StieltjesFunction ℝ) :=
  (exists_germ_isCondKernelCDF κ).choose

/-- Every conditional kernel CDF of `κ` with respect to `fst κ` represents `condKernelCDF κ`. -/
lemma _root_.ProbabilityTheory.IsCondKernelCDF.mem_condKernelCDF {κ : Kernel α (γ × ℝ)}
    [IsFiniteKernel κ] {f : α × γ → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ (fst κ)) :
    f ∈ condKernelCDF κ := by
  obtain ⟨g, hg, hg_mem⟩ := (exists_germ_isCondKernelCDF κ).choose_spec
  exact Filter.Germ.mem_of_eventuallyEq hg_mem (eventuallyEq_fiberwiseAE_iff.2 (hg.ae_eq hf))

/-- `condKernelCDF κ` is represented by a conditional kernel CDF of `κ`. -/
lemma exists_isCondKernelCDF_mem_condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    ∃ f, IsCondKernelCDF f κ (fst κ) ∧ f ∈ condKernelCDF κ :=
  let ⟨f, hf, _⟩ := (isRatCondKernelCDF_density_Iic κ).exists_isCondKernelCDF
  ⟨f, hf, hf.mem_condKernelCDF⟩

/-- Given a conditional kernel CDF `f` of `κ`, the representatives of `condKernelCDF κ` are the
families that agree with `f` `fst κ a`-almost everywhere for every `a`. -/
lemma _root_.ProbabilityTheory.IsCondKernelCDF.mem_condKernelCDF_iff {κ : Kernel α (γ × ℝ)}
    [IsFiniteKernel κ] {f g : α × γ → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ (fst κ)) :
    g ∈ condKernelCDF κ ↔ ∀ a, ∀ᵐ b ∂(fst κ a), g (a, b) = f (a, b) :=
  (Filter.Germ.mem_iff_eventuallyEq hf.mem_condKernelCDF).trans eventuallyEq_fiberwiseAE_iff

/-- A representative of `condKernelCDF κ` that is measurable and consists of probability cdfs is a
conditional kernel CDF of `κ`. -/
lemma isCondKernelCDF_of_mem_condKernelCDF {κ : Kernel α (γ × ℝ)} [IsFiniteKernel κ]
    {g : α × γ → StieltjesFunction ℝ} (hg : g ∈ condKernelCDF κ)
    (hg_meas : ∀ x, Measurable fun p ↦ g p x) (hg_atBot : ∀ p, Tendsto (g p) atBot (𝓝 0))
    (hg_atTop : ∀ p, Tendsto (g p) atTop (𝓝 1)) :
    IsCondKernelCDF g κ (fst κ) := by
  obtain ⟨f, hf, hf_mem⟩ := exists_isCondKernelCDF_mem_condKernelCDF κ
  exact hf.congr hg_meas hg_atBot hg_atTop
    (eventuallyEq_fiberwiseAE_iff.1 (Filter.Germ.eventuallyEq_of_mem hf_mem hg))

/-- A conditional kernel for `κ : Kernel α (γ × ℝ)`, where `γ` is countably generated, built from a
conditional kernel CDF. It serves only to build the witness of
`ProbabilityTheory.Kernel.exists_isMarkovKernel_isCondKernel` when `α` is uncountable. -/
private noncomputable def condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    Kernel (α × γ) ℝ :=
  (isRatCondKernelCDF_density_Iic κ).exists_isCondKernelCDF.choose_spec.1.toKernel

private lemma isMarkovKernel_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelReal κ) := by
  rw [condKernelReal]
  infer_instance

attribute [local instance] isMarkovKernel_condKernelReal

private lemma compProd_fst_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelReal κ = κ :=
  compProd_toKernel (isRatCondKernelCDF_density_Iic κ).exists_isCondKernelCDF.choose_spec.1

/-- A conditional kernel for `κ : Kernel Unit (α × ℝ)`, built from a conditional cdf of `κ ()`. It
serves only to build the witness of `MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`. -/
private noncomputable def condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    Kernel (Unit × α) ℝ :=
  (HasUniqueCondCDF.exists_isCondCDF (ρ := κ ())).choose_spec.isCondKernelCDF.toKernel

private lemma isMarkovKernel_condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitReal κ) := by
  rw [condKernelUnitReal]
  infer_instance

attribute [local instance] isMarkovKernel_condKernelUnitReal

private lemma isCondKernel_condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    κ.IsCondKernel (condKernelUnitReal κ) where
  hasCompProd_fst := inferInstance
  disintegrate :=
    compProd_toKernel (HasUniqueCondCDF.exists_isCondCDF (ρ := κ ())).choose_spec.isCondKernelCDF

end Real

attribute [local instance] isMarkovKernel_condKernelReal isMarkovKernel_condKernelUnitReal
  isCondKernel_condKernelUnitReal

section BorelSnd

/-! ### Disintegration of kernels on standard Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize a disintegration
property on `ℝ` to all these spaces. The private kernel `borelMarkovFromReal` serves only to build
the witnesses of the existence statements of this file, where its arbitrary point acts only on
`fst κ a`-null sets. -/

open scoped Classical in
/-- The measurable selector used in `borelMarkovFromReal`, stated in the legacy
`MeasurableSet` facade expected by `Kernel.piecewise`. -/
private lemma measurableSet_borelMarkovFromRealSelector
    (Ω : Type*) [SigmaAlgebra Ω] [StandardBorelSpace Ω] (η : Kernel α ℝ) :
    MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0} :=
  measurableSet_iff_mem.mpr <|
    (Kernel.measurable_coe η (measurableEmbedding_embeddingReal Ω).measurableSet_range.compl)
      (measurableSet_singleton 0)

open scoped Classical in
/-- The pullback of `η : Kernel α ℝ` along the measurable embedding `e := embeddingReal Ω`, modified
to be a Markov kernel when `η` is one: the comap by `e` of `η a` when `η a` gives the complement of
`range e` measure zero, and of the Dirac mass at `e x₀` for an arbitrary `x₀ : Ω` otherwise.

The arbitrary point is not part of any public statement. The existence statements below apply the
construction to a conditional kernel of the image of a kernel `κ` under `Prod.map id e`, where the
second branch acts only on `fst κ a`-null sets
(`compProd_fst_borelMarkovFromReal_eq_comapRight_compProd`). -/
private noncomputable def borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [SigmaAlgebra Ω]
    [StandardBorelSpace Ω] (η : Kernel α ℝ) :
    Kernel α Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := embeddingReal Ω (Classical.ofNonempty : Ω)
  comapRight
    (piecewise (measurableSet_borelMarkovFromRealSelector Ω η)
      η (deterministic (fun _ ↦ x₀) measurable_const)) he

private lemma isSFiniteKernel_borelMarkovFromReal (η : Kernel α ℝ) [IsSFiniteKernel η] :
    IsSFiniteKernel (borelMarkovFromReal Ω η) :=
  IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

attribute [local instance] isSFiniteKernel_borelMarkovFromReal

/-- When `η` is a Markov kernel, `borelMarkovFromReal Ω η` is a Markov kernel; where `η a` gives
positive mass to the complement of the range of `embeddingReal Ω`, only through the arbitrary
point. -/
private lemma isMarkovKernel_borelMarkovFromReal (η : Kernel α ℝ) [IsMarkovKernel η] :
    IsMarkovKernel (borelMarkovFromReal Ω η) := by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a ↦ ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp

/-- For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η = κ'`.
The conclusion of the lemma is `fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) _`. -/
private lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η
      = comapRight (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))) ⊗ₖ η)
        (MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal Ω)) := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) h_prod_embed
  rw [comapRight_compProd_id_prod _ _ he]
  have h_fst : fst κ' = fst κ := by
    calc
      fst κ' = map κ Prod.fst := by
        unfold κ'
        change fst (map κ (fun x ↦ (x.1, e x.2))) = map κ Prod.fst
        exact fst_map_prod κ (he.measurable.comp measurable_snd)
      _ = fst κ := (fst_eq κ).symm
  ext a t ht : 2
  simp_rw [compProd_apply ht]
  rw [h_fst]
  refine lintegral_congr_ae ?_
  have h_ae : ∀ᵐ t ∂(fst κ a), (a, t) ∈ {p : α × β | η p (range e)ᶜ = 0} := by
    rw [← h_fst]
    have h_compProd : κ' a (univ ×ˢ range e)ᶜ = 0 := by
      unfold κ'
      rw [map_apply' _ _ ((MeasurableSet.univ.prod he.measurableSet_range).compl) (by fun_prop)]
      suffices Prod.map id e ⁻¹' (univ ×ˢ range e)ᶜ = ∅ by rw [this]; simp
      ext x
      simp
    rw [← hη', compProd_null] at h_compProd
    swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
    simp only [preimage_compl, mem_univ, mk_preimage_prod_right] at h_compProd
    exact h_compProd
  filter_upwards [h_ae] with a ha
  rw [borelMarkovFromReal, comapRight_apply', comapRight_apply']
  rotate_left
  · exact measurable_prodMk_left ht
  · exact measurable_prodMk_left ht
  classical
  rw [piecewise_apply, ite_eq_left]
  exact ha

/-- For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η = κ'`.
With that hypothesis, `fst κ ⊗ₖ borelMarkovFromReal Ω η = κ`. -/
private lemma compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
    (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ' h_prod_embed := by
    ext c t : 2
    unfold κ'
    rw [comapRight_apply, map_apply _ _ (by fun_prop), h_prod_embed.comap_map]
  conv_rhs => rw [this, ← hη']
  exact compProd_fst_borelMarkovFromReal_eq_comapRight_compProd κ η hη

/-- A finite kernel `κ : Kernel α (γ × Ω)`, where `γ` is countably generated, is disintegrated by a
Markov kernel: the pullback along `embeddingReal Ω` of the conditional kernel `condKernelReal` of
the image of `κ` in `γ × ℝ`, modified by `borelMarkovFromReal` on `fst κ a`-null sets. -/
private lemma exists_isMarkovKernel_isCondKernel_of_countablyGenerated (κ : Kernel α (γ × Ω))
    [IsFiniteKernel κ] : ∃ η : Kernel (α × γ) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η :=
  ⟨borelMarkovFromReal Ω (condKernelReal (map κ (Prod.map (id : γ → γ) (embeddingReal Ω))
      (measurable_id.prodMap (measurable_embeddingReal Ω)))),
    isMarkovKernel_borelMarkovFromReal _,
    ⟨inferInstance, compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)⟩⟩

/-- A finite kernel `κ : Kernel Unit (α × Ω)` is disintegrated by a Markov kernel: the pullback
along `embeddingReal Ω` of the conditional kernel `condKernelUnitReal` of the image of `κ` in
`α × ℝ`, which needs no assumption on `α`, modified by `borelMarkovFromReal` on
`fst κ ()`-null sets. -/
private lemma exists_isMarkovKernel_isCondKernel_unit (κ : Kernel Unit (α × Ω))
    [IsFiniteKernel κ] : ∃ η : Kernel (Unit × α) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η :=
  ⟨borelMarkovFromReal Ω (condKernelUnitReal (map κ (Prod.map (id : α → α) (embeddingReal Ω))
      (measurable_id.prodMap (measurable_embeddingReal Ω)))),
    isMarkovKernel_borelMarkovFromReal _,
    ⟨inferInstance, compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)⟩⟩

end BorelSnd

section Measure

/-- The case of `MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel` for a finite
measure. -/
private theorem exists_isMarkovKernel_isCondKernel_of_isFiniteMeasure (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] : ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η := by
  obtain ⟨η, _, _⟩ := exists_isMarkovKernel_isCondKernel_unit (const Unit ρ)
  refine ⟨comap η (fun a ↦ ((), a)) measurable_prodMk_left, inferInstance, ⟨inferInstance, ?_⟩⟩
  have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
    ext
    simp only [fst_apply, Measure.fst, const_apply]
  have h2 : prodMkLeft Unit (comap η (fun a ↦ ((), a)) measurable_prodMk_left) = η := by
    ext
    simp only [prodMkLeft_apply, comap_apply]
  rw [Measure.compProd_eq_compProd_const_apply]
  simp only [h1, h2]
  rw [disintegrate]
  simp

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- An s-finite kernel that disintegrates `ρ` reweighted by a positive finite function `w` of the
first coordinate disintegrates `ρ`: the weight can be divided out. -/
private lemma isCondKernel_of_withDensity_fst {ρ : Measure (α × Ω)} {η : Kernel α Ω}
    [IsSFiniteKernel η] {w : α → ℝ≥0∞} (hw : Measurable w) (hw₀ : ∀ a, w a ≠ 0)
    (hw_top : ∀ a, w a ≠ ∞) (h : (ρ.withDensity fun p ↦ w p.1).IsCondKernel η) :
    ρ.IsCondKernel η := by
  have h_eq : (ρ.fst ⊗ₘ η).withDensity (fun p ↦ w p.1) = ρ.withDensity fun p ↦ w p.1 := by
    rw [← Measure.withDensity_compProd hw]
    ext s hs
    rw [Measure.compProd_apply hs, ← Measure.fst_withDensity_fst hw, ← Measure.compProd_apply hs,
      h.disintegrate]
  exact ⟨inferInstance, Measure.eq_of_withDensity_eq (hw.comp measurable_fst) (fun p ↦ hw₀ p.1)
    (fun p ↦ hw_top p.1) h_eq⟩

/-- A measure `ρ` on `α × Ω` whose first marginal is σ-finite, where `Ω` is a nonempty standard
Borel space, is disintegrated by a Markov kernel: there is a Markov kernel `η : Kernel α Ω` with
`ρ.fst ⊗ₘ η = ρ`. For a positive weight `w` with a finite integral against `ρ.fst`, a Markov kernel
that disintegrates the finite measure `ρ.withDensity fun p ↦ w p.1` disintegrates `ρ`. -/
theorem _root_.MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel (ρ : Measure (α × Ω))
    [SigmaFinite ρ.fst] : ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η := by
  obtain ⟨w, hw_pos, hw, hw_int⟩ := exists_pos_lintegral_lt_of_sigmaFinite ρ.fst one_ne_zero
  have hw' : Measurable fun a ↦ (w a : ℝ≥0∞) := hw.coe_nnreal_ennreal
  have : IsFiniteMeasure (ρ.withDensity fun p ↦ (w p.1 : ℝ≥0∞)) :=
    Measure.isFiniteMeasure_withDensity_fst (f := fun a ↦ (w a : ℝ≥0∞)) hw'
      (hw_int.trans ENNReal.one_lt_top).ne
  obtain ⟨η, hη, h⟩ :=
    exists_isMarkovKernel_isCondKernel_of_isFiniteMeasure (ρ.withDensity fun p ↦ (w p.1 : ℝ≥0∞))
  exact ⟨η, hη, isCondKernel_of_withDensity_fst hw'
    (fun a ↦ ENNReal.coe_ne_zero.2 (hw_pos a).ne') (fun _ ↦ ENNReal.coe_ne_top) h⟩

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- Some class of kernels along `ae ρ.fst` contains a Markov kernel that disintegrates `ρ`. Since
`ρ` has a unique conditional kernel, such a class is unique. -/
lemma _root_.MeasureTheory.Measure.exists_aeClass_isCondKernel (ρ : Measure (α × Ω))
    [ρ.HasUniqueCondKernel] :
    ∃ c : AEClass (ae ρ.fst) Ω, ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η ∧ η ∈ c :=
  let ⟨η, h₁, h₂⟩ := Measure.HasUniqueCondKernel.exists_isMarkovKernel_isCondKernel (ρ := ρ)
  ⟨AEClass.mk _ η, η, h₁, h₂, AEClass.mem_mk _ η⟩

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- The conditional kernel of a measure `ρ` on a product space `α × Ω` with a unique conditional
kernel: the `ρ.fst`-almost-everywhere class of the Markov kernels `η` with `ρ.fst ⊗ₘ η = ρ`. A
measure whose first marginal is σ-finite has one when `Ω` is a nonempty standard Borel space
(`MeasureTheory.Measure.hasUniqueCondKernel_of_sigmaFinite_fst`).

A kernel represents it, written `η ∈ ρ.condKernel`, when it agrees `ρ.fst`-almost everywhere with
such a kernel. A Markov kernel represents it if and only if it disintegrates `ρ`
(`MeasureTheory.Measure.mem_condKernel_iff_of_isMarkovKernel`), and a Markov representative exists
(`MeasureTheory.Measure.exists_isMarkovKernel_mem_condKernel`). The class is determined by `ρ`,
while the values of a conditional kernel on a `ρ.fst`-null set are not. -/
noncomputable
def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [ρ.HasUniqueCondKernel] :
    AEClass (ae ρ.fst) Ω :=
  ρ.exists_aeClass_isCondKernel.choose

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- `ρ.condKernel` is represented by a Markov kernel that disintegrates `ρ`. -/
lemma _root_.MeasureTheory.Measure.exists_isMarkovKernel_mem_condKernel (ρ : Measure (α × Ω))
    [ρ.HasUniqueCondKernel] :
    ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η ∧ η ∈ ρ.condKernel :=
  ρ.exists_aeClass_isCondKernel.choose_spec

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- Equal measures have the same representatives of their conditional kernels. Since the type of
`ρ.condKernel` depends on `ρ`, this transports membership along an equation `ρ = ρ'`. -/
lemma _root_.MeasureTheory.Measure.mem_condKernel_congr {ρ ρ' : Measure (α × Ω)}
    [ρ.HasUniqueCondKernel] [ρ'.HasUniqueCondKernel] (h : ρ = ρ') {η : Kernel α Ω} :
    η ∈ ρ.condKernel ↔ η ∈ ρ'.condKernel := by
  subst h
  rfl

end Measure

section CountableOrCountablyGenerated
variable [h : CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ]

/-- A finite kernel `κ : Kernel α (β × Ω)`, where `Ω` is a nonempty standard Borel space and either
`α` is countable or `β` is countably generated, is disintegrated by a Markov kernel: there is a
Markov kernel `η : Kernel (α × β) Ω` with `fst κ ⊗ₖ η = κ`. -/
theorem exists_isMarkovKernel_isCondKernel :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η := by
  by_cases hα : Countable α
  · let κCond a := (κ a).exists_isMarkovKernel_isCondKernel.choose
    have h_markov a : IsMarkovKernel (κCond a) :=
      (κ a).exists_isMarkovKernel_isCondKernel.choose_spec.1
    have h_cond a : (κ a).IsCondKernel (κCond a) :=
      (κ a).exists_isMarkovKernel_isCondKernel.choose_spec.2
    exact ⟨condKernelCountable κCond
      (fun x y h ↦ by simp [κCond, apply_congr_of_indistinguishable _ h]), inferInstance,
      inferInstance⟩
  · have := h.countableOrCountablyGenerated.resolve_left hα
    exact exists_isMarkovKernel_isCondKernel_of_countablyGenerated κ

/-- Some class of kernels along `(fst κ).fiberwiseAE` contains a Markov kernel that disintegrates
`κ`. Since two finite conditional kernels of `κ` agree `fst κ a`-almost everywhere for every `a`
(`ProbabilityTheory.Kernel.IsCondKernel.ae_eq`), such a class is unique. -/
lemma exists_aeClass_isCondKernel :
    ∃ c : AEClass (fst κ).fiberwiseAE Ω, ∃ η : Kernel (α × β) Ω,
      IsMarkovKernel η ∧ κ.IsCondKernel η ∧ η ∈ c :=
  let ⟨η, h₁, h₂⟩ := exists_isMarkovKernel_isCondKernel κ
  ⟨AEClass.mk _ η, η, h₁, h₂, AEClass.mem_mk _ η⟩

/-- The conditional kernel of a finite kernel `κ : Kernel α (β × Ω)`, where `Ω` is a nonempty
standard Borel space and either `α` is countable or `β` is countably generated: the class along
`(fst κ).fiberwiseAE` of the Markov kernels `η` with `fst κ ⊗ₖ η = κ`, that is, of these kernels up
to `fst κ a`-null sets for every `a`.

A finite kernel represents it if and only if it disintegrates `κ`
(`ProbabilityTheory.Kernel.mem_condKernel_iff`), and a Markov representative exists
(`ProbabilityTheory.Kernel.exists_isMarkovKernel_mem_condKernel`). The class is determined by `κ`,
while the values of a conditional kernel on such null sets are not. -/
noncomputable
def condKernel : AEClass (fst κ).fiberwiseAE Ω :=
  (exists_aeClass_isCondKernel κ).choose

/-- `condKernel κ` is represented by a Markov kernel that disintegrates `κ`. -/
lemma exists_isMarkovKernel_mem_condKernel :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η ∧ η ∈ condKernel κ :=
  (exists_aeClass_isCondKernel κ).choose_spec

end CountableOrCountablyGenerated

end ProbabilityTheory.Kernel

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.FiberwiseAE
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.Density
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Existence of disintegration of measures and kernels for standard Borel spaces

Let `κ : Kernel α (β × Ω)` be a finite kernel, where `Ω` is a nonempty standard Borel space. Then
if `α` is countable or `β` has a countably generated σ-algebra (for example if it is standard
Borel), then there exists a Markov kernel `η : Kernel (α × β) Ω` such that `κ = fst κ ⊗ₖ η`. The
conditional kernel `condKernel κ` is chosen among these kernels.
We also define a conditional kernel for a finite measure `ρ : Measure (β × Ω)`, where `Ω` is a
nonempty standard Borel space. This is a Markov kernel `ρ.condKernel : Kernel β Ω`, chosen among
the Markov kernels `η` with `ρ = ρ.fst ⊗ₘ η`.
A conditional kernel is determined almost everywhere (see the file `Unique.lean`), and only almost
everywhere: every Markov kernel that agrees with a conditional kernel almost everywhere is one too
(`MeasureTheory.Measure.compProd_congr`, `ProbabilityTheory.Kernel.compProd_congr`). So `κ` and `ρ`
do not determine the values of these choices on null sets.

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
* If `α` is countable, we can proceed separately for each `a : α`: the finite measure `κ a` has a
  conditional kernel `(κ a).condKernel : Kernel β Ω`. Since `α` is countable, measurability is not
  an issue and we can put those together into a `Kernel (α × β) Ω`. For a measure on `β × ℝ`, a
  conditional kernel is built from the kernel of a conditional cdf in the sense of
  `ProbabilityTheory.IsCondCDF`, whose existence is proved in the `CondCDF.lean` file; for a general
  standard Borel space `Ω`, we go through the measurable embedding of `Ω` into `ℝ`.
* If `α` is not countable, we can't proceed separately for each `a : α` and have to build a function
  `f : α × β → ℚ → ℝ` which is measurable on the product. We are able to do so if `β` has a
  countably generated σ-algebra (this is the case in particular for standard Borel spaces).
  See the file `Density.lean`.

The conditional kernel is defined under the typeclass assumption
`CountableOrCountablyGenerated α β`, which encodes the property
`Countable α ∨ CountablyGenerated β`.

Properties of integrals involving `condKernel` are collated in the file `Integral.lean`.
The conditional kernel is unique (almost everywhere w.r.t. `fst κ`): this is proved in the file
`Unique.lean`.

## Main definitions

* `ProbabilityTheory.Kernel.condKernel κ : Kernel (α × β) Ω`: conditional kernel described above.
* `MeasureTheory.Measure.condKernel ρ : Kernel β Ω`: conditional kernel of a measure.

## Main statements

* `ProbabilityTheory.Kernel.exists_isMarkovKernel_isCondKernel`: a Markov kernel `η` with
  `fst κ ⊗ₖ η = κ` exists.
* `MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`: a Markov kernel `η` with
  `ρ.fst ⊗ₘ η = ρ` exists.
* `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`: `fst κ ⊗ₖ condKernel κ = κ`, available
  through `ProbabilityTheory.Kernel.disintegrate`.
* `MeasureTheory.Measure.condKernel.instIsCondKernel`: `ρ.fst ⊗ₘ ρ.condKernel = ρ`, available
  through `MeasureTheory.Measure.disintegrate`.
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

private lemma compProd_fst_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelReal κ = κ := by
  rw [condKernelReal, compProd_toKernel]

/-- A conditional kernel for `κ : Kernel Unit (α × ℝ)`, built from a conditional cdf of `κ ()`. It
serves only to build the witness of `MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`. -/
private noncomputable def condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    Kernel (Unit × α) ℝ :=
  (HasUniqueCondCDF.exists_isCondCDF (ρ := κ ())).choose_spec.isCondKernelCDF.toKernel

private lemma isMarkovKernel_condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitReal κ) := by
  rw [condKernelUnitReal]
  infer_instance

private lemma isCondKernel_condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    κ.IsCondKernel (condKernelUnitReal κ) where
  disintegrate := by
    rw [condKernelUnitReal]
    exact compProd_toKernel
      (HasUniqueCondCDF.exists_isCondCDF (ρ := κ ())).choose_spec.isCondKernelCDF

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
  rw [h_fst]
  ext a t ht : 2
  simp_rw [compProd_apply ht]
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
    ⟨compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)⟩⟩

/-- A finite kernel `κ : Kernel Unit (α × Ω)` is disintegrated by a Markov kernel: the pullback
along `embeddingReal Ω` of the conditional kernel `condKernelUnitReal` of the image of `κ` in
`α × ℝ`, which needs no assumption on `α`, modified by `borelMarkovFromReal` on
`fst κ ()`-null sets. -/
private lemma exists_isMarkovKernel_isCondKernel_unit (κ : Kernel Unit (α × Ω))
    [IsFiniteKernel κ] : ∃ η : Kernel (Unit × α) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η :=
  ⟨borelMarkovFromReal Ω (condKernelUnitReal (map κ (Prod.map (id : α → α) (embeddingReal Ω))
      (measurable_id.prodMap (measurable_embeddingReal Ω)))),
    isMarkovKernel_borelMarkovFromReal _,
    ⟨compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)⟩⟩

end BorelSnd

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-- A finite measure `ρ` on `α × Ω`, where `Ω` is a nonempty standard Borel space, is disintegrated
by a Markov kernel: there is a Markov kernel `η : Kernel α Ω` with `ρ.fst ⊗ₘ η = ρ`. -/
theorem _root_.MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] : ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η := by
  obtain ⟨η, _, _⟩ := exists_isMarkovKernel_isCondKernel_unit (const Unit ρ)
  refine ⟨comap η (fun a ↦ ((), a)) measurable_prodMk_left, inferInstance, ⟨?_⟩⟩
  have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
    ext
    simp only [fst_apply, Measure.fst, const_apply]
  have h2 : prodMkLeft Unit (comap η (fun a ↦ ((), a)) measurable_prodMk_left) = η := by
    ext
    simp only [prodMkLeft_apply, comap_apply]
  rw [Measure.compProd, h1, h2, disintegrate]
  simp

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ.fst ⊗ₘ ρ.condKernel = ρ` (`MeasureTheory.Measure.disintegrate`).

It is chosen among the Markov kernels with this property, which exist by
`MeasureTheory.Measure.exists_isMarkovKernel_isCondKernel`. Every finite kernel with this property
agrees with it `ρ.fst`-almost everywhere (`ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`).
Only this almost-everywhere class is determined by `ρ`: every Markov kernel that agrees with
`ρ.condKernel` `ρ.fst`-almost everywhere also disintegrates `ρ`
(`MeasureTheory.Measure.compProd_congr`), so the values of `ρ.condKernel` on `ρ.fst`-null sets are a
choice. -/
noncomputable
def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    Kernel α Ω :=
  ρ.exists_isMarkovKernel_isCondKernel.choose

instance _root_.MeasureTheory.Measure.condKernel.instIsCondKernel (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] : ρ.IsCondKernel ρ.condKernel :=
  ρ.exists_isMarkovKernel_isCondKernel.choose_spec.2

instance _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : IsMarkovKernel ρ.condKernel :=
  ρ.exists_isMarkovKernel_isCondKernel.choose_spec.1

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero _ _ hx _

end Measure

section CountableOrCountablyGenerated
variable [h : CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ]

/-- A finite kernel `κ : Kernel α (β × Ω)`, where `Ω` is a nonempty standard Borel space and either
`α` is countable or `β` is countably generated, is disintegrated by a Markov kernel: there is a
Markov kernel `η : Kernel (α × β) Ω` with `fst κ ⊗ₖ η = κ`. -/
theorem exists_isMarkovKernel_isCondKernel :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η := by
  by_cases hα : Countable α
  · exact ⟨condKernelCountable (fun a ↦ (κ a).condKernel)
      (fun x y h ↦ by simp [apply_congr_of_indistinguishable _ h]), inferInstance, inferInstance⟩
  · have := h.countableOrCountablyGenerated.resolve_left hα
    exact exists_isMarkovKernel_isCondKernel_of_countablyGenerated κ

/-- Conditional kernel of a kernel `κ : Kernel α (β × Ω)`: a Markov kernel such that
`fst κ ⊗ₖ condKernel κ = κ` (`ProbabilityTheory.Kernel.disintegrate`).

It is chosen among the Markov kernels with this property, which exist whenever `Ω` is a nonempty
standard Borel space and either `α` is countable or `β` is countably generated
(`ProbabilityTheory.Kernel.exists_isMarkovKernel_isCondKernel`). For every `a`, every finite kernel
with this property agrees with it at `(a, b)` for `fst κ a`-almost every `b`
(`ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd`). Only these almost-everywhere classes are
determined by `κ`: every Markov kernel that agrees with `condKernel κ` in this sense also
disintegrates `κ` (`ProbabilityTheory.Kernel.compProd_congr`), so the values of `condKernel κ` on
such null sets are a choice. -/
noncomputable
def condKernel : Kernel (α × β) Ω :=
  (exists_isMarkovKernel_isCondKernel κ).choose

/-- `condKernel κ` is a Markov kernel. -/
instance instIsMarkovKernelCondKernel : IsMarkovKernel (condKernel κ) :=
  (exists_isMarkovKernel_isCondKernel κ).choose_spec.1

instance condKernel.instIsCondKernel : κ.IsCondKernel κ.condKernel :=
  (exists_isMarkovKernel_isCondKernel κ).choose_spec.2

end CountableOrCountablyGenerated

end ProbabilityTheory.Kernel

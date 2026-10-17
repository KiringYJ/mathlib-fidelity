/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional independence through conditional kernels

When the joint law of `(ω, ω)` has a unique conditional kernel, for example on a standard Borel
space, the conditional probabilities given a sub-σ-algebra `m'` have a regular version: the
measures that a Markov representative of `ProbabilityTheory.condExpKernel μ hm'` gives the sets.
Conditional independence of null-measurable sets is then independence with respect to any
representative of that class and `μ.trim hm'`, and conditional independence of random variables is
a factorization of joint laws.

Given a random variable `k`, conditional independence of random variables `f` and `g` is, for every
finite measure on every measurable space, a factorization of their joint law with `k` through their
conditional distributions given `k`. These need only the classes of the joint laws of `(k, f)` and
`(k, g)`, which instance search supplies for nonempty standard Borel value spaces, and no class of
the joint law of `(ω, ω)`.

## Main statements

* `ProbabilityTheory.condIndep_iff_of_mem`: two σ-algebras of null-measurable sets are
  conditionally independent exactly when they are independent with respect to a representative
  of `condExpKernel μ hm'` and `μ.trim hm'`, with variants for families, sets and functions.
* `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_map_map`: two random variables are
  conditionally independent exactly when the image under them of a representative factors.
* `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`: two random
  variables are conditionally independent given a third exactly when their joint law with it
  factors through their conditional distributions; no structure on `Ω` is needed.
* `ProbabilityTheory.condIndepFun_iff_prodMkRight_mem_condDistrib`: `g` is conditionally
  independent of `f` given `k` exactly when the conditional distribution of `f` given `k`, ignoring
  `g`, is its conditional distribution given `(k, g)`.
-/

@[expose] public section

open MeasureTheory SigmaAlgebra

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

section Helpers

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {μ : Measure Ω}

private lemma condExp_indicator_congr {s t : Set Ω} (h : s =ᵐ[μ] t) :
    μ⟦s | m'⟧ =ᵐ[μ] μ⟦t | m'⟧ :=
  condExp_congr_ae (indicator_ae_eq_of_ae_eq_set h)

private lemma nullMeasurableSet_of_mem_comap {β : Type*} {mβ : SigmaAlgebra β} {f : Ω → β}
    (hf : NullMeasurable f μ) {s : Set Ω} (hs : s ∈ mβ.comap f) : NullMeasurableSet s μ := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact hf ht

private lemma nullMeasurableSet_of_mem_generateFrom_singleton {s t : Set Ω}
    (hs : NullMeasurableSet s μ) (ht : t ∈ generateFrom {s}) : NullMeasurableSet t μ := by
  rcases mem_generateFrom_singleton_iff.1 ht with rfl | rfl | rfl | rfl
  exacts [nullMeasurableSet_empty, hs, hs.compl, nullMeasurableSet_univ]

end Helpers

/-! ### Independence with respect to a conditional expectation kernel

When the joint law of `(ω, ω)` has a unique conditional kernel, for example on a standard Borel
space, conditional independence of null-measurable sets is independence with respect to any
representative of `condExpKernel μ hm'` and `μ.trim hm'`: the measures that a Markov representative
gives the sets are versions of their conditional probabilities. Kernel independence is invariant
under almost-everywhere equality of kernels, so the representative does not matter. -/

section Representatives

variable {m' m₁ m₂ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ] [(condExpJointLaw μ hm').HasUniqueCondKernel] {η : @Kernel Ω Ω m' mΩ}

omit [IsFiniteMeasure μ] in
/-- A representative of `condExpKernel μ hm'` gives two `μ`-almost everywhere equal sets the same
measure, `μ.trim hm'`-almost everywhere. -/
private lemma ae_trim_apply_eq_of_ae_eq (hη : η ∈ condExpKernel μ hm') {s t : Set Ω}
    (hst : s =ᵐ[μ] t) : ∀ᵐ ω ∂(μ.trim hm'), η ω s = η ω t := by
  have h : ∀ᵐ x ∂(η ∘ₘ μ.trim hm'), (x ∈ s) = (x ∈ t) := by
    rw [condExpKernel_comp_trim hη]
    exact hst
  filter_upwards [Measure.ae_ae_of_ae_comp h] with ω hω using measure_congr hω

/-- For a Markov representative `η` of `condExpKernel μ hm'`, `ω ↦ (η ω).real s` is a version of the
conditional probability of a null-measurable set `s`. -/
private lemma condExp_ae_eq_measureReal [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm')
    {s : Set Ω} (hs : NullMeasurableSet s μ) :
    μ⟦s | m'⟧ =ᵐ[μ] fun ω ↦ (η ω).real s := by
  filter_upwards [condExp_indicator_congr (m' := m') hs.toMeasurable_ae_eq.symm,
    condExpKernel_ae_eq_condExp hη (measurableSet_toMeasurable μ s),
    ae_of_ae_trim hm' (ae_trim_apply_eq_of_ae_eq hη hs.toMeasurable_ae_eq)] with ω h₁ h₂ h₃
  rw [h₁, ← h₂]
  simp only [measureReal_def, h₃]

/-- For a Markov representative `η` of `condExpKernel μ hm'` and a null-measurable set `s`,
`ω ↦ η ω s` is `μ.trim hm'`-almost everywhere equal to the measurable function
`ω ↦ η ω (toMeasurable μ s)`, whose real values are a version of the conditional probability of `s`.
-/
private lemma ae_trim_measureReal_eq_condExp [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm')
    {s : Set Ω} (hs : NullMeasurableSet s μ) :
    (fun ω ↦ (η ω).real (toMeasurable μ s)) =ᵐ[μ.trim hm'] μ⟦s | m'⟧ := by
  refine ((η.measurable_coe (measurableSet_toMeasurable μ s)).ennreal_toReal.stronglyMeasurable
    |>.ae_eq_trim_iff hm' stronglyMeasurable_condExp).2 ?_
  filter_upwards [condExp_ae_eq_measureReal hη hs,
    ae_of_ae_trim hm' (ae_trim_apply_eq_of_ae_eq hη hs.toMeasurable_ae_eq)] with ω h₁ h₂
  rw [h₁]
  simp only [measureReal_def, h₂]

/-- For a Markov representative `η` of `condExpKernel μ hm'`, the conditional probabilities of
null-measurable sets multiply exactly when the measures that `η` gives the sets multiply. -/
private lemma condExp_prod_iff_kernel [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm')
    (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, NullMeasurableSet (f i) μ)
    {t : Set Ω} (ht : NullMeasurableSet t μ) :
    μ⟦t | m'⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦f i | m'⟧ ↔
      ∀ᵐ ω ∂(μ.trim hm'), η ω t = ∏ i ∈ s, η ω (f i) := by
  have hT := ae_trim_apply_eq_of_ae_eq hη ht.toMeasurable_ae_eq
  have hF : ∀ᵐ ω ∂(μ.trim hm'), ∀ i ∈ s, η ω (f i) = η ω (toMeasurable μ (f i)) :=
    (Filter.eventually_all_finset s).2 fun i hi ↦
      ae_trim_apply_eq_of_ae_eq hη (hf i hi).toMeasurable_ae_eq.symm
  have hF' : ∀ᵐ ω ∂(μ.trim hm'), ∀ i ∈ s,
      (η ω).real (toMeasurable μ (f i)) = (μ⟦f i | m'⟧) ω :=
    (Filter.eventually_all_finset s).2 fun i hi ↦ ae_trim_measureReal_eq_condExp hη (hf i hi)
  have h_meas : StronglyMeasurable[m'] (∏ i ∈ s, μ⟦f i | m'⟧) :=
    Finset.stronglyMeasurable_prod s fun _ _ ↦ stronglyMeasurable_condExp
  rw [← (stronglyMeasurable_condExp.ae_eq_trim_iff hm' h_meas)]
  constructor
  · intro h
    filter_upwards [h, ae_trim_measureReal_eq_condExp hη ht, hT, hF, hF'] with ω h₁ h₂ h₃ h₄ h₅
    have h_real : (η ω).real (toMeasurable μ t) = ∏ i ∈ s, (η ω).real (toMeasurable μ (f i)) := by
      rw [h₂, h₁, Finset.prod_apply]
      exact Finset.prod_congr rfl fun i hi ↦ (h₅ i hi).symm
    simp only [measureReal_def, ← ENNReal.toReal_prod] at h_real
    rw [ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top _ _)] at h_real
    rw [← h₃, h_real]
    exact Finset.prod_congr rfl fun i hi ↦ (h₄ i hi).symm
  · intro h
    filter_upwards [h, ae_trim_measureReal_eq_condExp hη ht, hT, hF, hF'] with ω h₁ h₂ h₃ h₄ h₅
    rw [← h₂, Finset.prod_apply, measureReal_def, h₃, h₁, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i hi ↦ by rw [h₄ i hi, ← measureReal_def, h₅ i hi]

lemma iCondIndepSets_iff_of_mem {π : ι → Set (Set Ω)}
    (hπ : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    iCondIndepSets m' hm' π μ ↔ Kernel.iIndepSets π η (μ.trim hm') := by
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_condExpKernel μ hm'
  rw [Kernel.iIndepSets_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀)]
  have h_meas (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ π i) :
      NullMeasurableSet (⋂ i ∈ s, f i) μ :=
    .biInter s.countable_toSet fun i hi ↦ hπ i _ (hf i hi)
  refine ⟨fun h s f hf ↦ ?_, fun h ↦ ⟨hπ, fun s f hf ↦ ?_⟩⟩
  · exact (condExp_prod_iff_kernel hη₀ s (fun i hi ↦ hπ i _ (hf i hi)) (h_meas s hf)).1
      (h.condExp_biInter s hf)
  · exact (condExp_prod_iff_kernel hη₀ s (fun i hi ↦ hπ i _ (hf i hi)) (h_meas s hf)).2
      (h s hf)

lemma condIndepSets_iff_of_mem {s₁ s₂ : Set (Set Ω)} (hs₁ : ∀ s ∈ s₁, NullMeasurableSet s μ)
    (hs₂ : ∀ s ∈ s₂, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    CondIndepSets m' hm' s₁ s₂ μ ↔ Kernel.IndepSets s₁ s₂ η (μ.trim hm') := by
  classical
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_condExpKernel μ hm'
  rw [Kernel.indepSets_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀)]
  -- a pair of sets is a family indexed by `Bool`
  have h_pair (t₁ t₂ : Set Ω) (ht₁ : NullMeasurableSet t₁ μ) (ht₂ : NullMeasurableSet t₂ μ) :
      μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧ ↔
        ∀ᵐ ω ∂(μ.trim hm'), η₀ ω (t₁ ∩ t₂) = η₀ ω t₁ * η₀ ω t₂ := by
    have h := condExp_prod_iff_kernel hη₀ Finset.univ (f := fun b : Bool ↦ if b then t₁ else t₂)
      (fun b _ ↦ by cases b <;> simpa) (ht₁.inter ht₂)
    simpa [Fintype.prod_bool, mul_comm] using h
  refine ⟨fun h t₁ t₂ ht₁ ht₂ ↦ ?_, fun h ↦ ⟨hs₁, hs₂, fun t₁ t₂ ht₁ ht₂ ↦ ?_⟩⟩
  · exact (h_pair t₁ t₂ (hs₁ t₁ ht₁) (hs₂ t₂ ht₂)).1 (h.condExp_inter t₁ t₂ ht₁ ht₂)
  · exact (h_pair t₁ t₂ (hs₁ t₁ ht₁) (hs₂ t₂ ht₂)).2 (h t₁ t₂ ht₁ ht₂)

lemma iCondIndep_iff_of_mem {m : ι → SigmaAlgebra Ω}
    (hm : ∀ i, ∀ s ∈ m i, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    iCondIndep m' hm' m μ ↔ Kernel.iIndep m η (μ.trim hm') :=
  iCondIndepSets_iff_of_mem hm hη

lemma condIndep_iff_of_mem (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    CondIndep m' m₁ m₂ hm' μ ↔ Kernel.Indep m₁ m₂ η (μ.trim hm') :=
  condIndepSets_iff_of_mem hm₁ hm₂ hη

lemma iCondIndepSet_iff_of_mem {s : ι → Set Ω} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (hη : η ∈ condExpKernel μ hm') :
    iCondIndepSet m' hm' s μ ↔ Kernel.iIndepSet s η (μ.trim hm') :=
  iCondIndep_iff_of_mem (fun i _ ht ↦ nullMeasurableSet_of_mem_generateFrom_singleton (hs i) ht) hη

lemma condIndepSet_iff_of_mem {s t : Set Ω} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t μ) (hη : η ∈ condExpKernel μ hm') :
    CondIndepSet m' hm' s t μ ↔ Kernel.IndepSet s t η (μ.trim hm') :=
  condIndep_iff_of_mem (fun _ hu ↦ nullMeasurableSet_of_mem_generateFrom_singleton hs hu)
    (fun _ hu ↦ nullMeasurableSet_of_mem_generateFrom_singleton ht hu) hη

lemma iCondIndepFun_iff_of_mem {β : ι → Type*} {m : ∀ i, SigmaAlgebra (β i)} {f : ∀ i, Ω → β i}
    (hf : ∀ i, NullMeasurable (f i) μ) (hη : η ∈ condExpKernel μ hm') :
    iCondIndepFun m' hm' f μ ↔ Kernel.iIndepFun f η (μ.trim hm') :=
  iCondIndep_iff_of_mem (fun i _ hs ↦ nullMeasurableSet_of_mem_comap (hf i) hs) hη

lemma condIndepFun_iff_of_mem {β γ : Type*} [SigmaAlgebra β] [SigmaAlgebra γ] {f : Ω → β}
    {g : Ω → γ} (hf : NullMeasurable f μ) (hg : NullMeasurable g μ)
    (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ ↔ Kernel.IndepFun f g η (μ.trim hm') :=
  condIndep_iff_of_mem (fun _ hs ↦ nullMeasurableSet_of_mem_comap hf hs)
    (fun _ hs ↦ nullMeasurableSet_of_mem_comap hg hs) hη

end Representatives

section CondIndepFun

variable {β β' : Type*} {m' : SigmaAlgebra Ω}
  {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → β'}

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with a finite representative `η` of `condExpKernel μ hm'`, and the almost sure
equality is expressed as equality of the composition-product with the measure, which is
equivalent to a.e. equality. See `condIndepFun_iff_map_prod_eq_prod_map_map` for the a.e. equality
version with kernels.

For a random variable `f` and a Markov representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: almost surely,
`(η.map f ω).real s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} (hf : Measurable f) (hg : Measurable g)
    [(condExpJointLaw μ hm').HasUniqueCondKernel]
    {η : @Kernel Ω Ω m' mΩ} [IsFiniteKernel η] (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ
      ↔ (μ.trim hm') ⊗ₘ η.map (fun ω ↦ (f ω, g ω))
        = (μ.trim hm') ⊗ₘ (η.map f ×ₖ η.map g) := by
  rw [condIndepFun_iff_of_mem hf.nullMeasurable hg.nullMeasurable hη]
  exact Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

/-- Two random variables are conditionally independent iff they satisfy the almost sure equality
of conditional expectations `μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ =ᵐ[μ] μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧`
for all measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with a finite representative `η` of `condExpKernel μ hm'`.

For a random variable `f` and a Markov representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: almost surely,
`(η.map f ω).real s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
theorem condIndepFun_iff_map_prod_eq_prod_map_map
    {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} [CountableOrCountablyGenerated Ω (β × β')]
    (hf : Measurable f) (hg : Measurable g) [(condExpJointLaw μ hm').HasUniqueCondKernel]
    {η : @Kernel Ω Ω m' mΩ} [IsFiniteKernel η] (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ
      ↔ η.map (fun ω ↦ (f ω, g ω)) =ᵐ[μ.trim hm'] η.map f ×ₖ η.map g := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg hη,
    ← Kernel.compProd_eq_iff]

/-- Two random variables are conditionally independent with respect to `m'` iff the law of
`(id, f, g)` under `μ`, in which the identity is to the space with σ-algebra `m'`, can be written
as a product involving the conditional expectations of `f` and `g` given `m'`, as expressed by a
finite representative `η` of `condExpKernel μ hm'`.

For a random variable `f` and a Markov representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: almost surely,
`(η.map f ω).real s = μ⟦f ⁻¹' s | m'⟧ ω`. -/
lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
    {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} (hf : Measurable f) (hg : Measurable g)
    [(condExpJointLaw μ hm').HasUniqueCondKernel]
    {η : @Kernel Ω Ω m' mΩ} [IsFiniteKernel η] (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ
      ↔ @Measure.map _ _ _ (m'.prod _) (fun ω ↦ (ω, f ω, g ω)) μ
          (by
            change @AEMeasurable Ω (Ω × β × β') (m'.prod (mβ.prod mβ')) mΩ
              (fun ω ↦ (ω, f ω, g ω)) μ
            have hfg : @Measurable Ω (β × β') mΩ (mβ.prod mβ')
                (fun ω ↦ (f ω, g ω)) := @Measurable.prodMk Ω mΩ β β' mβ mβ' f g hf hg
            have hjoint : @Measurable Ω (Ω × β × β') mΩ (mΩ.prod (mβ.prod mβ'))
                (fun ω ↦ (ω, f ω, g ω)) :=
              @Measurable.prodMk Ω mΩ Ω (β × β') mΩ (mβ.prod mβ') id
                (fun ω ↦ (f ω, g ω)) measurable_id hfg
            have htarget : m'.prod (mβ.prod mβ') ≤ mΩ.prod (mβ.prod mβ') := by
              unfold SigmaAlgebra.prod
              gcongr
            exact @Measurable.aemeasurable Ω (Ω × β × β') mΩ
              (m'.prod (mβ.prod mβ')) (fun ω ↦ (ω, f ω, g ω)) μ
              (hjoint.mono (mb' := m'.prod (mβ.prod mβ')) le_rfl htarget))
        = (Kernel.id ×ₖ (η.map f ×ₖ η.map g)) ∘ₘ μ.trim hm' := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg hη]
  congr!
  · rw [Measure.compProd_map (by fun_prop)]
    let F : Ω × Ω → Ω × (β × β') := Prod.map id fun ω ↦ (f ω, g ω)
    have hfg : @Measurable Ω (β × β') mΩ (mβ.prod mβ')
        (fun ω ↦ (f ω, g ω)) := @Measurable.prodMk Ω mΩ β β' mβ mβ' f g hf hg
    have hF : @Measurable (Ω × Ω) (Ω × (β × β')) (m'.prod mΩ)
        (m'.prod (mβ.prod mβ'))
        F := @Measurable.prodMap Ω Ω Ω (β × β') m' m' mΩ (mβ.prod mβ') id
          (fun ω ↦ (f ω, g ω)) measurable_id hfg
    have hdiag := compProd_trim_condExpKernel hη
    simp only [hdiag, condExpJointLaw]
    have hdiagAe := aemeasurable_diag_of_le μ hm'
    have hFae : @AEMeasurable (Ω × Ω) (Ω × (β × β'))
        (m'.prod (mβ.prod mβ')) (m'.prod mΩ) F
        (@Measure.map Ω (Ω × Ω) mΩ (m'.prod mΩ) (fun ω ↦ (ω, ω)) μ hdiagAe) :=
      @Measurable.aemeasurable (Ω × Ω) (Ω × (β × β')) (m'.prod mΩ)
        (m'.prod (mβ.prod mβ')) F _ hF
    rw [Measure.map_map hdiagAe hFae]
    apply Measure.map_congr (hf := AEMeasurable.comp_aemeasurable hdiagAe hFae)
    filter_upwards with ω
    rfl
  · exact Measure.compProd_eq_comp_prod _ _

/-- Two random variables `f, g` are conditionally independent given a third `k` iff the
joint distribution of `k, f, g` factors into a product of their conditional distributions
given `k`, as expressed by Markov representatives of these conditional distributions.

No structure on `Ω` or on the value spaces is needed beyond the classes of the joint laws of
`(k, f)` and `(k, g)` that the conditional distributions require: by `condDistrib_ae_eq_condExp`,
`ω ↦ (η₁ (k ω)).real t` and `ω ↦ (η₂ (k ω)).real u` are versions of the conditional probabilities
of `f ⁻¹' t` and `g ⁻¹' u` given `k`, and the two measures give a box `s ×ˢ t ×ˢ u` the integrals
over `k ⁻¹' s` of the conditional probability of `f ⁻¹' t ∩ g ⁻¹' u` and of the product of these
versions. -/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {γ : Type*} {mγ : SigmaAlgebra γ} {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) {k : Ω → γ} (hk : Measurable k)
    [(μ.map (fun ω ↦ (k ω, f ω)) (hk.aemeasurable.prodMk hf)).HasUniqueCondKernel]
    [(μ.map (fun ω ↦ (k ω, g ω)) (hk.aemeasurable.prodMk hg)).HasUniqueCondKernel]
    {η₁ : Kernel γ β} [IsMarkovKernel η₁] (hη₁ : η₁ ∈ condDistrib f k μ)
    {η₂ : Kernel γ β'} [IsMarkovKernel η₂] (hη₂ : η₂ ∈ condDistrib g k μ) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.aemeasurable.prodMk (hf.prodMk hg)) =
        (Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf.nullMeasurable hg.nullMeasurable,
    Measure.ext_prod₃_iff]
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.aemeasurable.prodMk (hf.prodMk hg)) (s ×ˢ t ×ˢ u) =
        μ (k ⁻¹' s ∩ (f ⁻¹' t ∩ g ⁻¹' u)) :=
    Measure.map_apply (hs.prod (ht.prod hu)) (hk.aemeasurable.prodMk (hf.prodMk hg))
  have h_right {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable) (s ×ˢ t ×ˢ u) =
        ∫⁻ ω in k ⁻¹' s, η₁ (k ω) t * η₂ (k ω) u ∂μ := by
    rw [← Measure.compProd_eq_comp_prod, Measure.compProd_apply_prod hs (ht.prod hu),
      setLIntegral_map hs ((η₁ ×ₖ η₂).measurable_coe (ht.prod hu)) hk]
    simp only [Kernel.prod_apply_prod]
  -- the masses that the representatives give are versions of the conditional probabilities
  have h_version {t : Set β} {u : Set β'} (ht : MeasurableSet t) (hu : MeasurableSet u) :
      (fun ω ↦ (η₁ (k ω) t * η₂ (k ω) u).toReal) =ᵐ[μ]
        fun ω ↦ (μ⟦f ⁻¹' t | mγ.comap k⟧) ω * (μ⟦g ⁻¹' u | mγ.comap k⟧) ω := by
    filter_upwards [condDistrib_ae_eq_condExp hk hf hη₁ ht,
      condDistrib_ae_eq_condExp hk hg hη₂ hu] with ω h₁ h₂
    rw [← h₁, ← h₂, ENNReal.toReal_mul, measureReal_def, measureReal_def]
  have h_key {t : Set β} {u : Set β'} (ht : MeasurableSet t) (hu : MeasurableSet u) :
      (fun ω ↦ (η₁ (k ω) t * η₂ (k ω) u).toReal) =ᵐ[μ] μ⟦f ⁻¹' t ∩ g ⁻¹' u | mγ.comap k⟧ ↔
        ∀ s ∈ mγ.comap k, ∫⁻ ω in s, η₁ (k ω) t * η₂ (k ω) u ∂μ = μ (s ∩ (f ⁻¹' t ∩ g ⁻¹' u)) :=
    toReal_ae_eq_condExp_indicator_iff_forall_setLIntegral_eq hk.comap_le
      ((hf.nullMeasurable ht).inter (hg.nullMeasurable hu)) (measure_ne_top _ _)
      (((η₁.measurable_coe ht).mul (η₂.measurable_coe hu)).comp
        (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  constructor
  · intro h s t u hs ht hu
    rw [h_left hs ht hu, h_right hs ht hu]
    exact ((h_key ht hu).1 ((h_version ht hu).trans (h t u ht hu).symm) _ ⟨s, hs, rfl⟩).symm
  · intro h t u ht hu
    refine ((h_key ht hu).2 ?_).symm.trans (h_version ht hu)
    rintro _ ⟨s, hs, rfl⟩
    rw [← h_left hs ht hu, ← h_right hs ht hu]
    exact (h hs ht hu).symm

/-- Two random variables `f, g` are conditionally independent given a third `k` iff for a Markov
representative `η` of the conditional distribution of `f` given `k`, the kernel `η.prodMkRight β'`,
which ignores the value of `g`, represents the conditional distribution of `f` given `k` and `g`.

Only the classes of the joint laws of `(k, f)` and `((k, g), f)` that these conditional
distributions require are needed: the representation is the identity
`μ (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) = ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ` on boxes, and since
`ω ↦ (η (k ω)).real t` is a version of the conditional probability of `f ⁻¹' t` given `k`, the
right side is the integral over `k ⁻¹' s` of the product of the conditional probabilities of
`g ⁻¹' u` and `f ⁻¹' t`, while the left side is the integral over `k ⁻¹' s` of the conditional
probability of `g ⁻¹' u ∩ f ⁻¹' t`. -/
theorem condIndepFun_iff_prodMkRight_mem_condDistrib
    {γ : Type*} {mγ : SigmaAlgebra γ} {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) {k : Ω → γ} (hk : Measurable k)
    [(μ.map (fun ω ↦ (k ω, f ω)) (hk.aemeasurable.prodMk hf)).HasUniqueCondKernel]
    [(μ.map (fun ω ↦ ((k ω, g ω), f ω))
      ((hk.aemeasurable.prodMk hg).prodMk hf)).HasUniqueCondKernel]
    {η : Kernel γ β} [IsMarkovKernel η] (hη : η ∈ condDistrib f k μ) :
    g ⟂ᵢ[k, hk; μ] f ↔ η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ := by
  have hm : mγ.comap k ≤ mΩ := hk.comap_le
  -- membership is an identity on boxes
  have h_mem : η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ ↔
      ∀ {s : Set γ} {u : Set β'} {t : Set β}, MeasurableSet s → MeasurableSet u →
        MeasurableSet t →
          μ (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) = ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ := by
    rw [mem_condDistrib_iff (hk.aemeasurable.prodMk hg) hf, Measure.ext_prod₃_iff']
    refine forall_congr' fun s ↦ forall_congr' fun u ↦ forall_congr' fun t ↦ ?_
    refine forall_congr' fun hs ↦ forall_congr' fun hu ↦ forall_congr' fun ht ↦ ?_
    rw [Measure.map_apply ((hs.prod hu).prod ht) ((hk.aemeasurable.prodMk hg).prodMk hf),
      Measure.compProd_apply_prod (hs.prod hu) ht,
      Measure.restrict_map_of_aemeasurable (hk.aemeasurable.prodMk hg) (hs.prod hu),
      lintegral_map' _ ((η.prodMkRight β').measurable_coe ht).aemeasurable]
    rfl
  -- conditional independence of `g ⁻¹' u` and `f ⁻¹' t` is the identity on the boxes over them
  have h_key {u : Set β'} {t : Set β} (hu : MeasurableSet u) (ht : MeasurableSet t) :
      (μ⟦g ⁻¹' u ∩ f ⁻¹' t | mγ.comap k⟧ =ᵐ[μ]
        fun ω ↦ (μ⟦g ⁻¹' u | mγ.comap k⟧) ω * (μ⟦f ⁻¹' t | mγ.comap k⟧) ω) ↔
      ∀ {s : Set γ}, MeasurableSet s →
        μ (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) = ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ := by
    have hB : NullMeasurableSet (g ⁻¹' u) μ := hg.nullMeasurable hu
    have hA : NullMeasurableSet (g ⁻¹' u ∩ f ⁻¹' t) μ := hB.inter (hf.nullMeasurable ht)
    have hH : StronglyMeasurable[mγ.comap k] fun ω ↦ (η (k ω)).real t :=
      ((η.measurable_coe ht).comp (Measurable.of_comap_le le_rfl)).ennreal_toReal.stronglyMeasurable
    have hH_le (ω : Ω) : ‖(η (k ω)).real t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    have hB_int : Integrable ((g ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) μ :=
      (integrable_const 1).indicator₀ hB
    have hA_int : Integrable ((g ⁻¹' u ∩ f ⁻¹' t).indicator fun _ ↦ (1 : ℝ)) μ :=
      (integrable_const 1).indicator₀ hA
    have h_eq : ((fun ω ↦ (η (k ω)).real t) * (g ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) =
        (g ⁻¹' u).indicator fun ω ↦ (η (k ω)).real t := by
      ext ω
      by_cases hω : ω ∈ g ⁻¹' u <;> simp [hω]
    have hHB_int : Integrable ((g ⁻¹' u).indicator fun ω ↦ (η (k ω)).real t) μ := by
      rw [← h_eq]
      exact hB_int.bdd_mul (c := 1) (hH.mono hm).aestronglyMeasurable (ae_of_all _ hH_le)
    -- the product is the conditional expectation of `η (k ·) t` on `g ⁻¹' u`
    have h_prod : (fun ω ↦ (μ⟦g ⁻¹' u | mγ.comap k⟧) ω * (μ⟦f ⁻¹' t | mγ.comap k⟧) ω) =ᵐ[μ]
        μ[(g ⁻¹' u).indicator fun ω ↦ (η (k ω)).real t | mγ.comap k] := by
      rw [← h_eq]
      filter_upwards [condDistrib_ae_eq_condExp hk hf hη ht,
        condExp_stronglyMeasurable_mul_of_bound hm hH hB_int 1 (ae_of_all _ hH_le)] with ω h₁ h₂
      rw [h₂, Pi.mul_apply, ← h₁, mul_comm]
    have h_int_A {s : Set γ} (hs : MeasurableSet s) :
        ∫ ω in k ⁻¹' s, (μ⟦g ⁻¹' u ∩ f ⁻¹' t | mγ.comap k⟧) ω ∂μ =
          μ.real (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) := by
      rw [setIntegral_condExp hm hA_int ⟨s, hs, rfl⟩,
        integral_indicator₀ (hA.mono Measure.restrict_le_self), setIntegral_const, smul_eq_mul,
        mul_one, measureReal_restrict_apply' (hk hs), Set.inter_comm, Set.inter_assoc]
    have h_int_H {s : Set γ} (hs : MeasurableSet s) :
        ∫ ω in k ⁻¹' s, (μ[(g ⁻¹' u).indicator fun ω ↦ (η (k ω)).real t | mγ.comap k]) ω ∂μ =
          (∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ).toReal := by
      rw [setIntegral_condExp hm hHB_int ⟨s, hs, rfl⟩,
        integral_indicator₀ (hB.mono Measure.restrict_le_self),
        Measure.restrict_restrict₀ (hB.mono Measure.restrict_le_self), Set.inter_comm]
      exact integral_toReal ((η.measurable_coe ht).comp hk).aemeasurable
        (ae_of_all _ fun ω ↦ measure_lt_top _ _)
    have h_fin {s : Set γ} : ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ ≠ ∞ :=
      ((setLIntegral_mono measurable_const fun ω _ ↦ prob_le_one).trans_lt (by simp)).ne
    refine ⟨fun h s hs ↦ ?_, fun h ↦ ?_⟩
    · have h₁ := setIntegral_congr_ae (hk hs) ((h.trans h_prod).mono fun _ hx _ ↦ hx)
      rw [h_int_A hs, h_int_H hs, measureReal_def] at h₁
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) h_fin).1 h₁
    · refine (ae_eq_condExp_of_forall_setIntegral_eq hm hHB_int
        (fun _ _ _ ↦ integrable_condExp.integrableOn) ?_
        stronglyMeasurable_condExp.aestronglyMeasurable).trans h_prod.symm
      rintro _ ⟨s, hs, rfl⟩ _
      rw [h_int_A hs, ← setIntegral_condExp hm hHB_int ⟨s, hs, rfl⟩, h_int_H hs, ← h hs,
        measureReal_def]
  rw [h_mem, condIndepFun_iff_condExp_inter_preimage_eq_mul hg.nullMeasurable hf.nullMeasurable]
  exact ⟨fun h s u t hs hu ht ↦ (h_key hu ht).1 (h u t hu ht) hs,
    fun h u t hu ht ↦ (h_key hu ht).2 fun hs ↦ h hs hu ht⟩

end CondIndepFun

end ProbabilityTheory

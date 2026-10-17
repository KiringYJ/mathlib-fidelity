/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional independence and the conditional expectation kernel

When the joint law of `(ω, ω)` has a unique conditional kernel, for example on a standard Borel
space, the conditional probabilities given a sub-σ-algebra `m'` have a regular version: the
measures that a Markov representative of `ProbabilityTheory.condExpKernel μ hm'` gives the sets.
Conditional independence of null-measurable sets is then independence with respect to any
representative of that class and `μ.trim hm'`, and conditional independence of random variables is
a factorization of joint laws.

## Main statements

* `ProbabilityTheory.condIndep_iff_of_mem`: two σ-algebras of null-measurable sets are
  conditionally independent exactly when they are independent with respect to a representative
  of `condExpKernel μ hm'` and `μ.trim hm'`, with variants for families, sets and functions.
* `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_map_map`: two random variables are
  conditionally independent exactly when the image under them of a representative factors.
* `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`: two random
  variables are conditionally independent given a third exactly when their joint law with it
  factors through their conditional distributions.
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
given `k`, as expressed by Markov representatives of these conditional distributions. The proof
uses the conditional expectation kernel given `k`, which the standard Borel space supplies. -/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib [StandardBorelSpace Ω]
    {γ : Type*} {mγ : SigmaAlgebra γ} {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k)
    {η₁ : Kernel γ β} [IsMarkovKernel η₁] (hη₁ : η₁ ∈ condDistrib f k μ)
    {η₂ : Kernel γ β'} [IsMarkovKernel η₂] (hη₂ : η₂ ∈ condDistrib g k μ) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.prodMk (hf.prodMk hg)).aemeasurable =
        (Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable := by
  obtain ⟨η, _, hη⟩ := exists_isMarkovKernel_mem_condExpKernel μ hk.comap_le
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg hη]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : k ⁻¹' s ∈ mγ.comap k :=
    ⟨s, hs, rfl⟩
  have hjoint_comap : @AEMeasurable Ω (Ω × β × β')
      ((mγ.comap k).prod (mβ.prod mβ')) mΩ
      (fun ω ↦ (ω, f ω, g ω)) μ := by
    have hfg : @Measurable Ω (β × β') mΩ (mβ.prod mβ')
        (fun ω ↦ (f ω, g ω)) := @Measurable.prodMk Ω mΩ β β' mβ mβ' f g hf hg
    have hjoint : @Measurable Ω (Ω × β × β') mΩ (mΩ.prod (mβ.prod mβ'))
        (fun ω ↦ (ω, f ω, g ω)) :=
      @Measurable.prodMk Ω mΩ Ω (β × β') mΩ (mβ.prod mβ') id
        (fun ω ↦ (f ω, g ω)) measurable_id hfg
    have htarget : (mγ.comap k).prod (mβ.prod mβ') ≤ mΩ.prod (mβ.prod mβ') := by
      unfold SigmaAlgebra.prod
      gcongr
      exact hk.comap_le
    exact @Measurable.aemeasurable Ω (Ω × β × β') mΩ
      ((mγ.comap k).prod (mβ.prod mβ')) (fun ω ↦ (ω, f ω, g ω)) μ
      (hjoint.mono (mb' := (mγ.comap k).prod (mβ.prod mβ')) le_rfl htarget)
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      (μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.prodMk (hf.prodMk hg)).aemeasurable)
          (s ×ˢ t ×ˢ u) =
        (@Measure.map _ _ _ ((mγ.comap k).prod inferInstance)
          (fun ω ↦ (ω, f ω, g ω)) μ hjoint_comap)
          ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.map_apply (hs.prod (ht.prod hu)) (hk.prodMk (hf.prodMk hg)).aemeasurable,
      Measure.map_apply ((measurableSet_iff_mem.mpr (hk_meas hs)).prod (ht.prod hu))
        hjoint_comap]
    · simp [Set.mk_preimage_prod]
  have h_right {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable) (s ×ˢ t ×ˢ u) =
        ((Kernel.id ×ₖ (η.map f ×ₖ η.map g)) ∘ₘ μ.trim hk.comap_le) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.bind_apply
        ((measurableSet_iff_mem.mpr (hk_meas hs)).prod (ht.prod hu)) (by fun_prop),
      Measure.bind_apply (hs.prod (ht.prod hu)) (by fun_prop), lintegral_map ?_ (by fun_prop),
      lintegral_trim]
    rotate_left
    · exact Kernel.measurable_coe _
        ((measurableSet_iff_mem.mpr (hk_meas hs)).prod (ht.prod hu))
    · exact Kernel.measurable_coe _ (hs.prod (ht.prod hu))
    refine lintegral_congr_ae ?_
    filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hf hk ht hη₁ hη,
      condDistrib_apply_ae_eq_condExpKernel_map hg hk hu hη₂ hη] with a haX haT
    simp only [Kernel.prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ hs]
    rw [@Measure.dirac_apply' _ (mγ.comap k) _ _ (hk_meas hs)]
    congr
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h ↦ ?_⟩
  · convert! h (hk_meas hs) ht hu
    · exact h_left hs ht hu
    · exact h_right hs ht hu
  · rintro - t u ⟨s, hs, rfl⟩ ht hu
    convert! h hs ht hu
    · exact (h_left hs ht hu).symm
    · exact (h_right hs ht hu).symm

/-- Two random variables `f, g` are conditionally independent given a third `k` iff for a Markov
representative `η` of the conditional distribution of `f` given `k`, the kernel `η.prodMkRight β'`,
which ignores the value of `g`, represents the conditional distribution of `f` given `k` and `g`. -/
theorem condIndepFun_iff_prodMkRight_mem_condDistrib [StandardBorelSpace Ω]
    {γ : Type*} {mγ : SigmaAlgebra γ} {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω → γ} (hk : Measurable k)
    {η : Kernel γ β} [IsMarkovKernel η] (hη : η ∈ condDistrib f k μ) :
    g ⟂ᵢ[k, hk; μ] f ↔ η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ := by
  obtain ⟨ζ, _, hζ⟩ := exists_isMarkovKernel_mem_condDistrib (Y := g) (X := k) (μ := μ)
    (hk.aemeasurable.prodMk hg.aemeasurable)
  rw [mem_condDistrib_iff (μ := μ) (by fun_prop) hf.aemeasurable,
    condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk hζ hη,
    Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ ζ) ×ₖ η) ∘ₘ μ.map k =
      (Kernel.id ×ₖ η.prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
    calc ((Kernel.id ×ₖ ζ) ×ₖ η) ∘ₘ μ.map k
    _ = (Kernel.id ×ₖ η.prodMkRight _) ∘ₘ (μ.map k ⊗ₘ ζ) := by
      rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc]
      congr 2
      have h := Kernel.prod_prodMkRight_comp_deterministic_prod ζ η Kernel.id measurable_id
      simp only [← Kernel.id.eq_1] at h
      simpa using h.symm
    _ = (Kernel.id ×ₖ η.prodMkRight _) ∘ₘ μ.map (fun a ↦ (k a, g a)) := by
      rw [compProd_map_condDistrib hk.aemeasurable hg.aemeasurable hζ]
  rw [← h_eq]
  have h1 : μ.map (fun x ↦ ((k x, g x), f x)) = (μ.map (fun a ↦ (k a, g a, f a))).map e := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h1_symm : μ.map (fun a ↦ (k a, g a, f a)) =
      (μ.map (fun x ↦ ((k x, g x), f x))).map e.symm := by
    exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp h1.symm
  have h2 : ((Kernel.id ×ₖ ζ) ×ₖ η) ∘ₘ μ.map k =
      ((Kernel.id ×ₖ (ζ ×ₖ η)) ∘ₘ μ.map k).map e := by
    rw [← Measure.deterministic_comp_eq_map e.measurable, Measure.comp_assoc]
    congr 2
    unfold e
    rw [Kernel.deterministic_comp_eq_map, Kernel.prodAssoc_symm_prod]
  have h2_symm : (Kernel.id ×ₖ (ζ ×ₖ η)) ∘ₘ μ.map k =
      (((Kernel.id ×ₖ ζ) ×ₖ η) ∘ₘ μ.map k).map e.symm := by
    exact (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp h2.symm
  rw [h1, h2]
  exact ⟨fun h ↦ by rw [h], fun h ↦ by rw [h1_symm, h1, h2_symm, h2, h]⟩

end CondIndepFun

end ProbabilityTheory

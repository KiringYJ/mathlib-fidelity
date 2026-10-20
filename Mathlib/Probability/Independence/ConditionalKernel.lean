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
space, the conditional probabilities given a sub-σ-algebra `m'` have a regular version: for a finite
measure `μ` and a finite representative `η` of `ProbabilityTheory.condExpKernel μ hm'`,
`ω ↦ (η ω).real s` is a version of the conditional probability of every measurable set `s`
(`ProbabilityTheory.isCondExp_condExpKernel_real`). Conditional independence of null-measurable
sets is then independence with respect to any representative of that class and `μ.trim hm'`, and
conditional independence of random variables is a factorization of joint laws.

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

private lemma nullMeasurableSet_of_mem_generateFrom_singleton {s t : Set Ω}
    (hs : NullMeasurableSet s μ) (ht : t ∈ generateFrom {s}) : NullMeasurableSet t μ := by
  rcases mem_generateFrom_singleton_iff.1 ht with rfl | rfl | rfl | rfl
  exacts [nullMeasurableSet_empty, hs, hs.compl, nullMeasurableSet_univ]

/-- A version `V` of the conditional expectation of an integrable function `F₁` given `m'` is one of
an integrable function `F₂` exactly when `F₁` and `F₂` have the same integral over each set of
`m'`. -/
private lemma isCondExp_iff_setIntegral_eq_of_isCondExp {F₁ F₂ V : Ω → ℝ}
    (h : IsCondExp m' μ F₁ V) (hF₁ : Integrable F₁ μ) (hF₂ : Integrable F₂ μ) :
    IsCondExp m' μ F₂ V ↔ ∀ s ∈ m', ∫ x in s, F₂ x ∂μ = ∫ x in s, F₁ x ∂μ := by
  refine ⟨fun h₂ s hs ↦ ?_, fun h_eq ↦ ⟨h.aestronglyMeasurable,
    fun _ _ _ ↦ (h.integrable hF₁).integrableOn, fun s hs _ ↦ ?_⟩⟩
  · rw [← h₂.setIntegral_eq s hs hF₂.integrableOn, h.setIntegral_eq s hs hF₁.integrableOn]
  · rw [h.setIntegral_eq s hs hF₁.integrableOn, h_eq s hs]

end Helpers

/-! ### Independence with respect to a conditional expectation kernel

When the joint law of `(ω, ω)` has a unique conditional kernel, for example on a standard Borel
space, conditional independence of null-measurable sets is independence with respect to any
representative of `condExpKernel μ hm'` and `μ.trim hm'`. For a finite representative `η` and a
null-measurable set `s`, `ω ↦ (η ω).real (toMeasurable μ s)` is an `m'`-measurable version of the
conditional probability of `s`, and an `m'`-strongly measurable function is a version exactly when
it agrees with `ω ↦ (η ω).real s` `μ.trim hm'`-almost everywhere. A product of such versions is
therefore a version for an intersection exactly when the measures that `η` gives the sets multiply
`μ.trim hm'`-almost everywhere. Kernel independence is invariant under almost-everywhere equality
of kernels, so the representative does not matter. -/

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

/-- For a finite representative `η` of `condExpKernel μ hm'` and a null-measurable set `s`, the
`m'`-measurable function `ω ↦ (η ω).real (toMeasurable μ s)` is a version of the conditional
probability of `s`. -/
private lemma isCondExp_measureReal_toMeasurable [IsFiniteKernel η]
    (hη : η ∈ condExpKernel μ hm') {s : Set Ω} (hs : NullMeasurableSet s μ) :
    IsCondExp m' μ (s.indicator fun _ ↦ (1 : ℝ)) fun ω ↦ (η ω).real (toMeasurable μ s) :=
  (isCondExp_condExpKernel_real hη (measurableSet_toMeasurable μ s)).congr_left
    (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)

/-- For a finite representative `η` of `condExpKernel μ hm'`, an `m'`-strongly measurable function
`g` is a version of the conditional probability of a null-measurable set `s` exactly when
`g ω = (η ω).real s` for `μ.trim hm'`-almost every `ω`. -/
private lemma isCondExp_iff_ae_trim_eq_measureReal [IsFiniteKernel η]
    (hη : η ∈ condExpKernel μ hm') {s : Set Ω} (hs : NullMeasurableSet s μ) {g : Ω → ℝ}
    (hg : StronglyMeasurable[m'] g) :
    IsCondExp m' μ (s.indicator fun _ ↦ (1 : ℝ)) g ↔ ∀ᵐ ω ∂(μ.trim hm'), g ω = (η ω).real s := by
  have hT := isCondExp_measureReal_toMeasurable hη hs
  have hT_meas : StronglyMeasurable[m'] fun ω ↦ (η ω).real (toMeasurable μ s) :=
    (η.measurable_coe (measurableSet_toMeasurable μ s)).ennreal_toReal.stronglyMeasurable
  have h_trim : ∀ᵐ ω ∂(μ.trim hm'), (η ω).real (toMeasurable μ s) = (η ω).real s := by
    filter_upwards [ae_trim_apply_eq_of_ae_eq hη hs.toMeasurable_ae_eq] with ω hω
    rw [measureReal_def, measureReal_def, hω]
  refine ⟨fun h ↦ ?_, fun h ↦ hT.congr_right (ae_eq_of_ae_eq_trim (hm := hm') ?_)⟩
  · filter_upwards [hg.ae_eq_trim_of_stronglyMeasurable hm' hT_meas
      (h.ae_eq hm' ((integrable_const 1).indicator₀ hs) hT), h_trim] with ω h₁ h₂
    rw [h₁, h₂]
  · filter_upwards [h, h_trim] with ω h₁ h₂
    rw [h₁, h₂]

/-- For a finite representative `η` of `condExpKernel μ hm'` and null-measurable sets `t` and
`f i`, `i ∈ s`, the product of the versions `ω ↦ (η ω).real (toMeasurable μ (f i))` of the
conditional probabilities of the sets `f i` is a version of the conditional probability of `t`
exactly when `η ω t = ∏ i ∈ s, η ω (f i)` for `μ.trim hm'`-almost every `ω`. -/
private lemma isCondExp_prod_iff_kernel [IsFiniteKernel η] (hη : η ∈ condExpKernel μ hm')
    (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, NullMeasurableSet (f i) μ)
    {t : Set Ω} (ht : NullMeasurableSet t μ) :
    IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ))
        (∏ i ∈ s, fun ω ↦ (η ω).real (toMeasurable μ (f i))) ↔
      ∀ᵐ ω ∂(μ.trim hm'), η ω t = ∏ i ∈ s, η ω (f i) := by
  have h_meas : StronglyMeasurable[m'] (∏ i ∈ s, fun ω ↦ (η ω).real (toMeasurable μ (f i))) :=
    Finset.stronglyMeasurable_prod s fun i _ ↦
      (η.measurable_coe (measurableSet_toMeasurable μ (f i))).ennreal_toReal.stronglyMeasurable
  have hF : ∀ᵐ ω ∂(μ.trim hm'), ∀ i ∈ s, η ω (toMeasurable μ (f i)) = η ω (f i) :=
    (Filter.eventually_all_finset s).2 fun i hi ↦
      ae_trim_apply_eq_of_ae_eq hη (hf i hi).toMeasurable_ae_eq
  rw [isCondExp_iff_ae_trim_eq_measureReal hη ht h_meas]
  refine Filter.eventually_congr (hF.mono fun ω hω ↦ ?_)
  have h_prod : (∏ i ∈ s, fun ω ↦ (η ω).real (toMeasurable μ (f i))) ω =
      (∏ i ∈ s, η ω (f i)).toReal := by
    simp only [Finset.prod_apply, ENNReal.toReal_prod, measureReal_def]
    exact Finset.prod_congr rfl fun i hi ↦ by rw [hω i hi]
  rw [h_prod, measureReal_def]
  exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top _ _)
    (measure_ne_top _ _)).trans eq_comm

lemma iCondIndepSets_iff_of_mem {π : ι → Set (Set Ω)}
    (hπ : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    iCondIndepSets m' hm' π μ ↔ Kernel.iIndepSets π η (μ.trim hm') := by
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_condExpKernel μ hm'
  rw [Kernel.iIndepSets_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀)]
  have h_meas (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ π i) :
      NullMeasurableSet (⋂ i ∈ s, f i) μ :=
    .biInter s.countable_toSet fun i hi ↦ hπ i _ (hf i hi)
  refine ⟨fun h s f hf ↦ ?_, fun h ↦ iCondIndepSets.of_isCondExp hπ fun s f hf ↦ ?_⟩
  · exact (isCondExp_prod_iff_kernel hη₀ s (fun i hi ↦ hπ i _ (hf i hi)) (h_meas s hf)).1
      (h.isCondExp_biInter s hf fun i hi ↦
        isCondExp_measureReal_toMeasurable hη₀ (hπ i _ (hf i hi)))
  · exact ⟨fun i ω ↦ (η₀ ω).real (toMeasurable μ (f i)),
      fun i hi ↦ isCondExp_measureReal_toMeasurable hη₀ (hπ i _ (hf i hi)),
      (isCondExp_prod_iff_kernel hη₀ s (fun i hi ↦ hπ i _ (hf i hi)) (h_meas s hf)).2 (h s hf)⟩

lemma condIndepSets_iff_of_mem {s₁ s₂ : Set (Set Ω)} (hs₁ : ∀ s ∈ s₁, NullMeasurableSet s μ)
    (hs₂ : ∀ s ∈ s₂, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    CondIndepSets m' hm' s₁ s₂ μ ↔ Kernel.IndepSets s₁ s₂ η (μ.trim hm') := by
  classical
  obtain ⟨η₀, _, hη₀⟩ := exists_isMarkovKernel_mem_condExpKernel μ hm'
  rw [Kernel.indepSets_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀)]
  -- a pair of sets is a family indexed by `Bool`
  have h_pair (t₁ t₂ : Set Ω) (ht₁ : NullMeasurableSet t₁ μ) (ht₂ : NullMeasurableSet t₂ μ) :
      IsCondExp m' μ ((t₁ ∩ t₂).indicator fun _ ↦ (1 : ℝ))
          ((fun ω ↦ (η₀ ω).real (toMeasurable μ t₁)) *
            fun ω ↦ (η₀ ω).real (toMeasurable μ t₂)) ↔
        ∀ᵐ ω ∂(μ.trim hm'), η₀ ω (t₁ ∩ t₂) = η₀ ω t₁ * η₀ ω t₂ := by
    have h := isCondExp_prod_iff_kernel hη₀ Finset.univ (f := fun b : Bool ↦ if b then t₁ else t₂)
      (fun b _ ↦ by cases b <;> simpa) (ht₁.inter ht₂)
    simpa [Fintype.prod_bool] using h
  refine ⟨fun h t₁ t₂ ht₁ ht₂ ↦ ?_,
    fun h ↦ CondIndepSets.of_isCondExp hs₁ hs₂ fun t₁ t₂ ht₁ ht₂ ↦ ?_⟩
  · exact (h_pair t₁ t₂ (hs₁ t₁ ht₁) (hs₂ t₂ ht₂)).1
      (h.isCondExp_inter t₁ t₂ ht₁ ht₂ (isCondExp_measureReal_toMeasurable hη₀ (hs₁ t₁ ht₁))
        (isCondExp_measureReal_toMeasurable hη₀ (hs₂ t₂ ht₂)))
  · exact ⟨_, _, isCondExp_measureReal_toMeasurable hη₀ (hs₁ t₁ ht₁),
      isCondExp_measureReal_toMeasurable hη₀ (hs₂ t₂ ht₂),
      (h_pair t₁ t₂ (hs₁ t₁ ht₁) (hs₂ t₂ ht₂)).2 (h t₁ t₂ ht₁ ht₂)⟩

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
  iCondIndep_iff_of_mem (fun i _ hs ↦ (hf i).measurable'.comap_le hs) hη

lemma condIndepFun_iff_of_mem {β γ : Type*} [SigmaAlgebra β] [SigmaAlgebra γ] {f : Ω → β}
    {g : Ω → γ} (hf : NullMeasurable f μ) (hg : NullMeasurable g μ)
    (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ ↔ Kernel.IndepFun f g η (μ.trim hm') :=
  condIndep_iff_of_mem (fun _ hs ↦ hf.measurable'.comap_le hs)
    (fun _ hs ↦ hg.measurable'.comap_le hs) hη

end Representatives

section CondIndepFun

variable {β β' : Type*} {m' : SigmaAlgebra Ω}
  {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → β'}

/-- Two random variables are conditionally independent iff
`μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ = μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧` as germs along `ae μ` for all
measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with a finite representative `η` of `condExpKernel μ hm'`, and the equality is
expressed as equality of the composition-products with `μ.trim hm'`. Under
`CountableOrCountablyGenerated Ω (β × β')`, this is `μ.trim hm'`-almost everywhere equality of the
kernels (`condIndepFun_iff_map_prod_eq_prod_map_map`).

For a random variable `f` and a finite representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: for every measurable set `s`,
`ω ↦ (η.map f ω).real s` is a version of the conditional probability of `f ⁻¹' s`
(`ProbabilityTheory.isCondExp_condExpKernel_real`). -/
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} (hf : Measurable f) (hg : Measurable g)
    [(condExpJointLaw μ hm').HasUniqueCondKernel]
    {η : @Kernel Ω Ω m' mΩ} [IsFiniteKernel η] (hη : η ∈ condExpKernel μ hm') :
    CondIndepFun m' hm' f g μ
      ↔ (μ.trim hm') ⊗ₘ η.map (fun ω ↦ (f ω, g ω))
        = (μ.trim hm') ⊗ₘ (η.map f ×ₖ η.map g) := by
  rw [condIndepFun_iff_of_mem hf.nullMeasurable hg.nullMeasurable hη]
  exact Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

/-- Two random variables are conditionally independent iff
`μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ = μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧` as germs along `ae μ` for all
measurable sets `s` and `t` (see `condIndepFun_iff_condExp_inter_preimage_eq_mul`).
Here, this is phrased with a finite representative `η` of `condExpKernel μ hm'`.

For a random variable `f` and a finite representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: for every measurable set `s`,
`ω ↦ (η.map f ω).real s` is a version of the conditional probability of `f ⁻¹' s`
(`ProbabilityTheory.isCondExp_condExpKernel_real`). -/
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
as a product involving the conditional distributions of `f` and `g` given `m'`, as expressed by a
finite representative `η` of `condExpKernel μ hm'`.

For a random variable `f` and a finite representative `η` of `condExpKernel μ hm'`, `η.map f` is a
regular conditional distribution of `f` given `m'`: for every measurable set `s`,
`ω ↦ (η.map f ω).real s` is a version of the conditional probability of `f ⁻¹' s`
(`ProbabilityTheory.isCondExp_condExpKernel_real`). -/
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
given `k`, as expressed by finite representatives of these conditional distributions.

No structure on `Ω` or on the value spaces is needed beyond the classes of the joint laws of
`(k, f)` and `(k, g)` that the conditional distributions require: by
`ProbabilityTheory.isCondExp_condDistrib_real`, `ω ↦ (η₁ (k ω)).real t` and
`ω ↦ (η₂ (k ω)).real u` are versions of the conditional probabilities of `f ⁻¹' t` and `g ⁻¹' u`
given `k`, and the two measures give a box `s ×ˢ t ×ˢ u` the masses
`μ (k ⁻¹' s ∩ (f ⁻¹' t ∩ g ⁻¹' u))` and `∫⁻ ω in k ⁻¹' s, η₁ (k ω) t * η₂ (k ω) u ∂μ`, which agree
for every measurable `s` exactly when the product of these versions is a version of the conditional
probability of `f ⁻¹' t ∩ g ⁻¹' u`. -/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {γ : Type*} {mγ : SigmaAlgebra γ} {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) {k : Ω → γ} (hk : Measurable k)
    [(μ.map (fun ω ↦ (k ω, f ω)) (hk.aemeasurable.prodMk hf)).HasUniqueCondKernel]
    [(μ.map (fun ω ↦ (k ω, g ω)) (hk.aemeasurable.prodMk hg)).HasUniqueCondKernel]
    {η₁ : Kernel γ β} [IsFiniteKernel η₁] (hη₁ : η₁ ∈ condDistrib f k μ)
    {η₂ : Kernel γ β'} [IsFiniteKernel η₂] (hη₂ : η₂ ∈ condDistrib g k μ) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.aemeasurable.prodMk (hf.prodMk hg)) =
        (Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable := by
  rw [condIndepFun_iff_isCondExp_inter_preimage hf.nullMeasurable hg.nullMeasurable,
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
  have hG₁ {t : Set β} (ht : MeasurableSet t) :
      IsCondExp (mγ.comap k) μ ((f ⁻¹' t).indicator fun _ ↦ (1 : ℝ))
        fun ω ↦ (η₁ (k ω)).real t :=
    isCondExp_condDistrib_real hk hf hη₁ ht
  have hG₂ {u : Set β'} (hu : MeasurableSet u) :
      IsCondExp (mγ.comap k) μ ((g ⁻¹' u).indicator fun _ ↦ (1 : ℝ))
        fun ω ↦ (η₂ (k ω)).real u :=
    isCondExp_condDistrib_real hk hg hη₂ hu
  -- their product is a version for the intersection exactly when it has the right integrals
  have h_key {t : Set β} {u : Set β'} (ht : MeasurableSet t) (hu : MeasurableSet u) :
      IsCondExp (mγ.comap k) μ ((f ⁻¹' t ∩ g ⁻¹' u).indicator fun _ ↦ (1 : ℝ))
          ((fun ω ↦ (η₁ (k ω)).real t) * fun ω ↦ (η₂ (k ω)).real u) ↔
        ∀ s ∈ mγ.comap k,
          ∫⁻ ω in s, η₁ (k ω) t * η₂ (k ω) u ∂μ = μ (s ∩ (f ⁻¹' t ∩ g ⁻¹' u)) := by
    have h_eq : ((fun ω ↦ (η₁ (k ω)).real t) * fun ω ↦ (η₂ (k ω)).real u) =
        fun ω ↦ (η₁ (k ω) t * η₂ (k ω) u).toReal := by
      ext ω
      simp only [Pi.mul_apply, measureReal_def, ENNReal.toReal_mul]
    rw [h_eq]
    exact isCondExp_indicator_toReal_iff hk.comap_le
      ((hf.nullMeasurable ht).inter (hg.nullMeasurable hu)) (measure_ne_top _ _)
      (((η₁.measurable_coe ht).mul (η₂.measurable_coe hu)).comp
        (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  constructor
  · intro h s t u hs ht hu
    rw [h_left hs ht hu, h_right hs ht hu]
    exact ((h_key ht hu).1 (h t u ht hu (hG₁ ht) (hG₂ hu)) _ ⟨s, hs, rfl⟩).symm
  · intro h t u ht hu g₁ g₂ hg₁ hg₂
    refine ((h_key ht hu).2 ?_).congr_right
      (((hG₁ ht).ae_eq hk.comap_le ((integrable_const 1).indicator₀ (hf.nullMeasurable ht))
        hg₁).mul ((hG₂ hu).ae_eq hk.comap_le
          ((integrable_const 1).indicator₀ (hg.nullMeasurable hu)) hg₂))
    rintro _ ⟨s, hs, rfl⟩
    rw [← h_left hs ht hu, ← h_right hs ht hu]
    exact (h hs ht hu).symm

/-- Two random variables `f, g` are conditionally independent given a third `k` iff for a Markov
representative `η` of the conditional distribution of `f` given `k`, the kernel `η.prodMkRight β'`,
which ignores the value of `g`, represents the conditional distribution of `f` given `k` and `g`.

Only the classes of the joint laws of `(k, f)` and `((k, g), f)` that these conditional
distributions require are needed: the representation is the identity
`μ (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) = ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ` on boxes. Since
`ω ↦ (η (k ω)).real t` is a version of the conditional probability of `f ⁻¹' t` given `k`
(`ProbabilityTheory.isCondExp_condDistrib_real`), the pull-out property makes the right side the
integral over `k ⁻¹' s` of its product with any version of the conditional probability of
`g ⁻¹' u`, while the left side is the integral over `k ⁻¹' s` of the indicator of
`g ⁻¹' u ∩ f ⁻¹' t`. The identity on all boxes thus states that this product is a version of the
conditional probability of `g ⁻¹' u ∩ f ⁻¹' t`. -/
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
  -- `ω ↦ (η (k ω)).real t` is a version of the conditional probability of `f ⁻¹' t` given `k`
  have hH {t : Set β} (ht : MeasurableSet t) :
      IsCondExp (mγ.comap k) μ ((f ⁻¹' t).indicator fun _ ↦ (1 : ℝ))
        fun ω ↦ (η (k ω)).real t :=
    isCondExp_condDistrib_real hk hf hη ht
  -- for a version `B` of the conditional probability of `g ⁻¹' u`, the product of `B` with that
  -- version is a version for `g ⁻¹' u ∩ f ⁻¹' t` exactly when the identity holds on the boxes
  have h_key {u : Set β'} {t : Set β} (hu : MeasurableSet u) (ht : MeasurableSet t) {B : Ω → ℝ}
      (hB : IsCondExp (mγ.comap k) μ ((g ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) B) :
      IsCondExp (mγ.comap k) μ ((g ⁻¹' u ∩ f ⁻¹' t).indicator fun _ ↦ (1 : ℝ))
          (B * fun ω ↦ (η (k ω)).real t) ↔
        ∀ {s : Set γ}, MeasurableSet s →
          μ (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) = ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ := by
    have hgu : NullMeasurableSet (g ⁻¹' u) μ := hg.nullMeasurable hu
    have hA : NullMeasurableSet (g ⁻¹' u ∩ f ⁻¹' t) μ := hgu.inter (hf.nullMeasurable ht)
    have hH_meas : StronglyMeasurable[mγ.comap k] fun ω ↦ (η (k ω)).real t :=
      ((η.measurable_coe ht).comp (Measurable.of_comap_le le_rfl)).ennreal_toReal.stronglyMeasurable
    have hH_le (ω : Ω) : ‖(η (k ω)).real t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    have hgu_int : Integrable ((g ⁻¹' u).indicator fun _ ↦ (1 : ℝ)) μ :=
      (integrable_const 1).indicator₀ hgu
    have hA_int : Integrable ((g ⁻¹' u ∩ f ⁻¹' t).indicator fun _ ↦ (1 : ℝ)) μ :=
      (integrable_const 1).indicator₀ hA
    have h_eq : ((g ⁻¹' u).indicator (fun _ ↦ (1 : ℝ)) * fun ω ↦ (η (k ω)).real t) =
        (g ⁻¹' u).indicator fun ω ↦ (η (k ω)).real t := by
      ext ω
      by_cases hω : ω ∈ g ⁻¹' u <;> simp [hω]
    have hHB_int :
        Integrable ((g ⁻¹' u).indicator (fun _ ↦ (1 : ℝ)) * fun ω ↦ (η (k ω)).real t) μ :=
      hgu_int.mul_bdd (c := 1) (hH_meas.mono hm).aestronglyMeasurable (ae_of_all _ hH_le)
    -- pull out the `k`-measurable factor
    have hBH := hB.mul_right hm hH_meas.aestronglyMeasurable hHB_int hgu_int
    have h_int_A {s : Set γ} (hs : MeasurableSet s) :
        ∫ ω in k ⁻¹' s, (g ⁻¹' u ∩ f ⁻¹' t).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ =
          μ.real (k ⁻¹' s ∩ g ⁻¹' u ∩ f ⁻¹' t) := by
      rw [integral_indicator₀ (hA.mono Measure.restrict_le_self), setIntegral_const, smul_eq_mul,
        mul_one, measureReal_restrict_apply' (hk hs), Set.inter_comm, Set.inter_assoc]
    have h_int_H {s : Set γ} (hs : MeasurableSet s) :
        ∫ ω in k ⁻¹' s,
            ((g ⁻¹' u).indicator (fun _ ↦ (1 : ℝ)) * fun ω ↦ (η (k ω)).real t) ω ∂μ =
          (∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ).toReal := by
      rw [h_eq, integral_indicator₀ (hgu.mono Measure.restrict_le_self),
        Measure.restrict_restrict₀ (hgu.mono Measure.restrict_le_self), Set.inter_comm]
      exact integral_toReal ((η.measurable_coe ht).comp hk).aemeasurable
        (ae_of_all _ fun ω ↦ measure_lt_top _ _)
    have h_fin {s : Set γ} : ∫⁻ ω in k ⁻¹' s ∩ g ⁻¹' u, η (k ω) t ∂μ ≠ ∞ :=
      ((setLIntegral_mono measurable_const fun ω _ ↦ prob_le_one).trans_lt (by simp)).ne
    rw [isCondExp_iff_setIntegral_eq_of_isCondExp hBH hHB_int hA_int]
    refine ⟨fun h s hs ↦ ?_, fun h ↦ ?_⟩
    · have h₁ := h _ ⟨s, hs, rfl⟩
      rw [h_int_A hs, h_int_H hs, measureReal_def] at h₁
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) h_fin).1 h₁
    · rintro _ ⟨s, hs, rfl⟩
      rw [h_int_A hs, h_int_H hs, measureReal_def, h hs]
  rw [h_mem, condIndepFun_iff_isCondExp_inter_preimage hg.nullMeasurable hf.nullMeasurable]
  constructor
  · intro h s u t hs hu ht
    obtain ⟨B, hB⟩ := (HasUniqueCondExp.of_integrable hm
      ((integrable_const (1 : ℝ)).indicator₀ (hg.nullMeasurable hu))).exists_isCondExp
    exact (h_key hu ht hB).1 (h u t hu ht hB (hH ht)) hs
  · intro h u t hu ht g₁ g₂ hg₁ hg₂
    exact ((h_key hu ht hg₁).2 fun hs ↦ h hs hu ht).congr_right
      ((Filter.EventuallyEq.refl _ g₁).mul ((hH ht).ae_eq hm
        ((integrable_const 1).indicator₀ (hf.nullMeasurable ht)) hg₂))

end CondIndepFun

end ProbabilityTheory

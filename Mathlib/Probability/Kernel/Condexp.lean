/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.ConditionalProbability

/-!
# Kernel associated with a conditional expectation

For a sub-σ-algebra `m ≤ mΩ`, we define `condExpKernel μ hm`, the `μ.trim hm`-almost-everywhere
class of the Markov kernels `η` from `(Ω, m)` to `Ω` with `(μ.trim hm) ⊗ₘ η = μ.map (ω ↦ (ω, ω))`.
Every such kernel satisfies, for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)`. These kernels are determined only up to
`μ.trim hm`-null sets, so the kernel associated with the conditional expectation is their class,
not a chosen kernel.

This class is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condExpKernel μ hm`: the `μ.trim hm`-almost-everywhere class of the Markov kernels `η` from
  `(Ω, m)` to `Ω` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.

## Main statements

* `mem_condExpKernel_iff`: a finite kernel `η` represents `condExpKernel μ hm` if and only if
  `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.
* `condExp_ae_eq_integral_condExpKernel`: `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)` for every
  Markov representative `η` of `condExpKernel μ hm`.

-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

theorem aemeasurable_diag_of_le {T : Type*} {m mT : SigmaAlgebra T}
    (μ : @Measure T mT) (hm : m ≤ mT) :
    @AEMeasurable T (T × T) (m.prod mT) mT Function.diag μ :=
  @Measurable.aemeasurable T (T × T) mT (m.prod mT) Function.diag μ
    (@Measurable.prodMk T mT T T m mT id id
      (@measurable_id'' T m mT hm) (@measurable_id T mT))

section AuxLemmas

variable {Ω F : Type*} {m mΩ : SigmaAlgebra Ω} {μ : Measure Ω} {f : Ω → F}

theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id (hm : m ≤ mΩ)
    [TopologicalSpace F] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m.prod mΩ] (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
        (aemeasurable_diag_of_le μ hm)) :=
  hf.comp_snd_map_prodMk (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm))

theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id (hm : m ≤ mΩ) [NormedAddCommGroup F]
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
        (aemeasurable_diag_of_le μ hm)) :=
  hf.comp_snd_map_prodMk (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm))

end AuxLemmas

variable {Ω F : Type*} {m : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Some class of kernels from `(Ω, m)` to `Ω` along `ae (μ.trim hm)` contains a Markov kernel `η`
with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`. Since two finite kernels with this property agree
`μ.trim hm`-almost everywhere (`ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`), such a class is
unique. -/
lemma exists_aeClass_condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ) :
    ∃ c : @Kernel.AEClass Ω (ae (μ.trim hm)) Ω m mΩ, ∃ η : @Kernel Ω Ω m mΩ,
      IsMarkovKernel η ∧
        (μ.trim hm) ⊗ₘ η = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
          (aemeasurable_diag_of_le μ hm) ∧ η ∈ c := by
  rcases isEmpty_or_nonempty Ω with h | h
  · refine ⟨Kernel.AEClass.mk _ 0, 0, ⟨fun a ↦ (IsEmpty.false a).elim⟩, ?_,
      Kernel.AEClass.mem_mk _ _⟩
    simp [Measure.eq_zero_of_isEmpty μ]
  · obtain ⟨η, hη, hη_mem⟩ := exists_isMarkovKernel_mem_condDistrib (mβ := m) (X := id) (Y := id)
      (μ := μ) (aemeasurable_diag_of_le μ hm)
    refine ⟨Kernel.AEClass.mk _ η, η, hη, ?_, Kernel.AEClass.mem_mk _ η⟩
    rw [trim_eq_map hm]
    exact compProd_map_condDistrib (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm))
      aemeasurable_id hη_mem

/-- The kernel associated with the conditional expectation with respect to a sub-σ-algebra
`m ≤ mΩ`: the `μ.trim hm`-almost-everywhere class of the Markov kernels `η` from `(Ω, m)` to
`(Ω, mΩ)` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.

Every Markov representative `η` satisfies `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)` for integrable
`f` (`ProbabilityTheory.condExp_ae_eq_integral_condExpKernel`). If `Ω` is nonempty, the Markov
representatives are those of the conditional distribution of the identity given the identity, where
the second identity is viewed as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with the σ-algebra
`m` (`ProbabilityTheory.mem_condExpKernel_iff_mem_condDistrib`). -/
noncomputable def condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ) :
    @Kernel.AEClass Ω (ae (μ.trim hm)) Ω m mΩ :=
  (exists_aeClass_condExpKernel μ hm).choose

/-- `condExpKernel μ hm` is represented by a Markov kernel. -/
lemma exists_isMarkovKernel_mem_condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) :
    ∃ η : @Kernel Ω Ω m mΩ, IsMarkovKernel η ∧ η ∈ condExpKernel μ hm :=
  let ⟨η, h₁, _, h₂⟩ := (exists_aeClass_condExpKernel μ hm).choose_spec
  ⟨η, h₁, h₂⟩

variable {hm : m ≤ mΩ} {η : @Kernel Ω Ω m mΩ}

/-- Every s-finite representative `η` of `condExpKernel μ hm` satisfies
`(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`. -/
lemma compProd_trim_condExpKernel [IsSFiniteKernel η] (hη : η ∈ condExpKernel μ hm) :
    (μ.trim hm) ⊗ₘ η
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
        (aemeasurable_diag_of_le μ hm) := by
  obtain ⟨η₀, _, h₀, hη₀⟩ := (exists_aeClass_condExpKernel μ hm).choose_spec
  rw [Measure.compProd_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀), h₀]

/-- A finite kernel `η` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))` represents
`condExpKernel μ hm`. -/
lemma mem_condExpKernel_of_compProd_eq [IsFiniteKernel η]
    (h : (μ.trim hm) ⊗ₘ η
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ (aemeasurable_diag_of_le μ hm)) :
    η ∈ condExpKernel μ hm := by
  obtain ⟨η₀, _, h₀, hη₀⟩ := (exists_aeClass_condExpKernel μ hm).choose_spec
  exact Kernel.AEClass.mem_of_eventuallyEq hη₀ (Kernel.ae_eq_of_compProd_eq (h₀.trans h.symm))

/-- A finite kernel `η` represents `condExpKernel μ hm` if and only if
`(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`. -/
lemma mem_condExpKernel_iff [IsFiniteKernel η] :
    η ∈ condExpKernel μ hm ↔
      (μ.trim hm) ⊗ₘ η
        = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ (aemeasurable_diag_of_le μ hm) :=
  ⟨compProd_trim_condExpKernel, mem_condExpKernel_of_compProd_eq⟩

/-- If `Ω` is nonempty, the finite representatives of `condExpKernel μ hm` are those of the
conditional distribution of the identity given the identity, the second identity being viewed as a
map from `Ω` with the σ-algebra `mΩ` to `Ω` with the σ-algebra `m`. -/
lemma mem_condExpKernel_iff_mem_condDistrib [Nonempty Ω] [IsFiniteKernel η] :
    η ∈ condExpKernel μ hm ↔
      η ∈ @condDistrib Ω Ω Ω mΩ _ _ mΩ m id id μ _ (aemeasurable_diag_of_le μ hm) := by
  rw [mem_condExpKernel_iff, mem_condDistrib_iff (@Measurable.aemeasurable Ω Ω mΩ m id μ
    (measurable_id'' hm)) aemeasurable_id, ← trim_eq_map hm]
  exact eq_comm

lemma condExpKernel_comp_trim [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) :
    η ∘ₘ μ.trim hm = μ := by
  rw [← Measure.snd_compProd, compProd_trim_condExpKernel hη]
  exact (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm) measurable_id).trans
    Measure.map_id

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂η ω) μ := by
  nontriviality Ω
  exact AEStronglyMeasurable.integral_condDistrib
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf.comp_snd_map_prod_id hm)

theorem aestronglyMeasurable_integral_condExpKernel [NormedSpace ℝ F] [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂η ω) μ := by
  nontriviality Ω
  have h := aestronglyMeasurable_integral_condDistrib
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf.comp_snd_map_prod_id hm)
  rwa [SigmaAlgebra.comap_id] at h

lemma aestronglyMeasurable_trim_condExpKernel [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm)
    (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂(μ.trim hm), f =ᵐ[η ω] hf.mk f := by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hη]
  exact hf.ae_eq_mk

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.Integrable.condExpKernel_ae [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (η ω) := by
  nontriviality Ω
  convert! Integrable.condDistrib_ae
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf_int.comp_snd_map_prod_id hm) using 1

theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂η ω) μ := by
  nontriviality Ω
  convert! Integrable.integral_norm_condDistrib
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf_int.comp_snd_map_prod_id hm) using 1

theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel [NormedSpace ℝ F]
    [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂η ω‖) μ := by
  nontriviality Ω
  convert! Integrable.norm_integral_condDistrib
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf_int.comp_snd_map_prod_id hm) using 1

theorem _root_.MeasureTheory.Integrable.integral_condExpKernel [NormedSpace ℝ F]
    [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂η ω) μ := by
  nontriviality Ω
  convert! Integrable.integral_condDistrib
    (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm)) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) (hf_int.comp_snd_map_prod_id hm) using 1

end Integrability

lemma condExpKernel_ae_eq_condExp [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) {s : Set Ω}
    (hs : MeasurableSet s) :
    (fun ω ↦ (η ω).real s) =ᵐ[μ] μ⟦s | m⟧ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have h := condDistrib_ae_eq_condExp (μ := μ) (measurable_id'' hm) measurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) hs
  simp only [id_eq, SigmaAlgebra.comap_id, preimage_id_eq] at h
  exact h

lemma condExpKernel_ae_eq_trim_condExp [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm)
    {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (η ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  simp_rw [measureReal_def]
  rw [(η.measurable_coe hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hη hs

lemma condDistrib_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} [StandardBorelSpace β] [Nonempty β] {X : Ω → β} {Y : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) {s : Set β} (hs : MeasurableSet s)
    {η₁ : Kernel γ β} [IsMarkovKernel η₁]
    (hη₁ : η₁ ∈ condDistrib X Y μ (hY.aemeasurable.prodMk hX.aemeasurable))
    {η₂ : @Kernel Ω Ω (mγ.comap Y) mΩ} [IsMarkovKernel η₂]
    (hη₂ : η₂ ∈ condExpKernel μ hY.comap_le) :
    (fun a ↦ η₁ (Y a) s) =ᵐ[μ] fun a ↦ η₂.map X hX a s := by
  simp_rw [Kernel.map_apply' _ _ hs hX]
  filter_upwards [condDistrib_ae_eq_condExp hY hX hη₁ (μ := μ) hs,
    condExpKernel_ae_eq_condExp hη₂ (hX hs)] with a ha₁ ha₂
  rw [← measureReal_eq_measureReal_iff, ha₁, ha₂]

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(η ω)` for every Markov representative `η` of `condExpKernel μ hm`. -/
theorem condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm)
    (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂η ω := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have hX : @Measurable Ω Ω mΩ m id := measurable_id'' hm
  have h := condExp_ae_eq_integral_condDistrib_id hX hf_int
    (mem_condExpKernel_iff_mem_condDistrib.1 hη)
  simpa only [SigmaAlgebra.comap_id, id_eq] using! h

/-- Auxiliary lemma for `condExp_ae_eq_trim_integral_condExpKernel`. -/
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
    [NormedAddCommGroup F] {f : Ω → F} [NormedSpace ℝ F] [CompleteSpace F]
    [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) (hf : StronglyMeasurable f)
    (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂η ω := by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact (hf.comp_measurable measurable_snd).integral_kernel_prod_right'
  · exact condExp_ae_eq_integral_condExpKernel hη hf_int

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is
(`μ.trim hm`)-almost everywhere equal to the integral `∫ y, f y ∂(η ω)` for every Markov
representative `η` of `condExpKernel μ hm`. -/
theorem condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm)
    (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂η ω := by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hη
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel hη hf_int.1] with ω hω
  rw [integral_congr_ae hω]

section Cond

/-! ### Relation between conditional expectation, conditional kernel and the conditional measure. -/

open SigmaAlgebra

variable {s t : Set Ω} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [StandardBorelSpace Ω]

lemma condExp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω → F} (hf : Integrable f μ) :
    μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ ↦ ∫ x, f x ∂μ[|s] := by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (SigmaAlgebra.mem_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.restrict ?_ ?_
      stronglyMeasurable_const.aestronglyMeasurable).symm
    · rintro t - -
      rw [integrableOn_const_iff]
      exact Or.inr <| measure_lt_top (μ.restrict s) t
    · rintro t ht -
      obtain (h | h | h | h) := mem_generateFrom_singleton_iff.1 ht
      · simp [h]
      · simp only [h, cond, integral_smul_measure, ENNReal.toReal_inv, integral_const,
        MeasurableSet.univ, measureReal_restrict_apply, univ_inter, measureReal_restrict_apply_self,
        ← measureReal_def]
        rw [smul_inv_smul₀, Measure.restrict_restrict hs, inter_self]
        exact ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩
      · simp only [h, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          measureReal_restrict_apply hs.compl, compl_inter_self, measureReal_empty, zero_smul,
          ((Measure.restrict_apply_eq_zero hs.compl).2 <| compl_inter_self s ▸ measure_empty),
          setIntegral_measure_zero]
      · simp only [h, Measure.restrict_univ, cond, integral_smul_measure, ENNReal.toReal_inv, ←
        measureReal_def, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
        rw [smul_inv_smul₀]
        exact (measureReal_ne_zero_iff (by finiteness)).2 hμs

lemma condExp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ ↦ μ[|s].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_generateFrom_singleton hs <| Integrable.indicator (integrable_const 1) ht

lemma condExpKernel_singleton_ae_eq_cond [StandardBorelSpace Ω] (hs : MeasurableSet s)
    (ht : MeasurableSet t) {ξ : @Kernel Ω Ω (generateFrom {s}) mΩ} [IsMarkovKernel ξ]
    (hξ : ξ ∈ condExpKernel μ (generateFrom_singleton_le hs)) :
    ∀ᵐ ω ∂μ.restrict s, ξ ω t = μ[t | s] := by
  have : (fun ω ↦ (ξ ω).real t) =ᵐ[μ.restrict s] μ⟦t | generateFrom {s}⟧ :=
    ae_restrict_le <| condExpKernel_ae_eq_condExp hξ ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ t) (measure_ne_top _ t)] at hω₂

end Cond

end ProbabilityTheory

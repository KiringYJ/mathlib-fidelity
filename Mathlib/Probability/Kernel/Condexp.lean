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
If `μ.trim hm` is σ-finite, every such kernel satisfies, for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)`. When the joint law below has a unique conditional
kernel, two such kernels agree `μ.trim hm`-almost everywhere, and every Markov kernel that agrees
with one of them `μ.trim hm`-almost everywhere is another, so the kernel associated with the
conditional expectation is their class, not a chosen kernel.

This class is the conditional kernel of the joint law of `(ω, ω)`, the first coordinate being
viewed in `Ω` with the σ-algebra `m` (`ProbabilityTheory.condExpJointLaw`), so it is defined when
that joint law has a unique conditional kernel, which the statements take as an instance argument.
Instance search supplies it when `Ω` is a standard Borel space and `μ.trim hm` is σ-finite, for
example when `μ` is finite, and for every measure on a countably generated space when `m` is the
whole σ-algebra. When `μ.trim hm` is σ-finite, the conditional probability `μ⟦s | m⟧` of a
measurable set `s` of finite measure is a function `Ω → ℝ` determined up to a `μ`-null set. For all
`a`, the map from sets to `ℝ` that we obtain that way verifies some of the properties of a measure,
but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of the
conditional expectation that combine into a true measure. The standard Borel space assumption on
`Ω` allows us to do so.

## Main definitions

* `condExpJointLaw μ hm`: the law of `(ω, ω)` under `μ`, the first coordinate being viewed in
  `Ω` with the σ-algebra `m`.
* `condExpKernel μ hm`: the `μ.trim hm`-almost-everywhere class of the Markov kernels `η` from
  `(Ω, m)` to `Ω` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.

## Main statements

* `mem_condExpKernel_iff_of_isMarkovKernel`: a Markov kernel `η` represents `condExpKernel μ hm`
  if and only if `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.
* `mem_condExpKernel_iff`: if `μ.trim hm` is σ-finite, a kernel `η` for which `(μ.trim hm) ⊗ₘ η`
  exists represents `condExpKernel μ hm` if and only if `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`.
* `condExp_ae_eq_integral_condExpKernel`: if `μ.trim hm` is σ-finite,
  `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)` for every Markov representative `η` of
  `condExpKernel μ hm`.

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

variable {Ω F : Type*} {m : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] {μ : Measure Ω}

/-- The law of `(ω, ω)` under `μ` when the first coordinate is viewed in `Ω` with the sub-σ-algebra
`m`: the joint law of the identity from `(Ω, mΩ)` to `(Ω, m)` and the identity. Its first marginal
is `μ.trim hm` (`ProbabilityTheory.fst_condExpJointLaw`), and its conditional kernel is
`ProbabilityTheory.condExpKernel μ hm`. -/
noncomputable def condExpJointLaw (μ : Measure Ω) (hm : m ≤ mΩ) : @Measure (Ω × Ω) (m.prod mΩ) :=
  @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ (aemeasurable_diag_of_le μ hm)

/-- The first marginal of the joint law of `(ω, ω)` is the trim of `μ`. -/
lemma fst_condExpJointLaw (μ : Measure Ω) (hm : m ≤ mΩ) :
    @Measure.fst Ω Ω m mΩ (condExpJointLaw μ hm) = μ.trim hm := by
  rw [trim_eq_map hm]
  exact @Measure.fst_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm) measurable_id

/-- The second marginal of the joint law of `(ω, ω)` is `μ`. -/
lemma snd_condExpJointLaw (μ : Measure Ω) (hm : m ≤ mΩ) :
    @Measure.snd Ω Ω m mΩ (condExpJointLaw μ hm) = μ :=
  (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm) measurable_id).trans
    Measure.map_id

/-- The first marginal of the joint law of `(ω, ω)` is σ-finite when `μ.trim hm` is. -/
instance sigmaFinite_fst_condExpJointLaw {hm : m ≤ mΩ} [SigmaFinite (μ.trim hm)] :
    SigmaFinite (@Measure.fst Ω Ω m mΩ (condExpJointLaw μ hm)) := by
  rw [fst_condExpJointLaw]
  infer_instance

/-- The joint law of `(ω, ω)` has a unique conditional kernel when `Ω` is a standard Borel space
and `μ.trim hm` is σ-finite, for example when `μ` is finite: for a nonempty space by
`MeasureTheory.Measure.hasUniqueCondKernel_of_sigmaFinite_fst`, and for the empty space by
`MeasureTheory.Measure.hasUniqueCondKernel_of_isEmpty`. -/
instance hasUniqueCondKernel_condExpJointLaw [StandardBorelSpace Ω] {hm : m ≤ mΩ}
    [SigmaFinite (μ.trim hm)] : (condExpJointLaw μ hm).HasUniqueCondKernel := by
  rcases isEmpty_or_nonempty Ω with h | h <;> infer_instance

/-- For the whole σ-algebra, the joint law of `(ω, ω)` has a unique conditional kernel for every
measure on a countably generated space, since its second coordinate is a measurable function of the
first (`MeasureTheory.Measure.hasUniqueCondKernel_map_prodMk_comp`). -/
instance hasUniqueCondKernel_condExpJointLaw_self [SigmaAlgebra.CountablyGenerated Ω]
    {hm : mΩ ≤ mΩ} : (condExpJointLaw μ hm).HasUniqueCondKernel :=
  Measure.hasUniqueCondKernel_map_prodMk_comp aemeasurable_id measurable_id

/-- The kernel associated with the conditional expectation with respect to a sub-σ-algebra
`m ≤ mΩ`: the conditional kernel of the joint law of `(ω, ω)` (`ProbabilityTheory.condExpJointLaw`),
that is, the `μ.trim hm`-almost-everywhere class of the Markov kernels `η` from `(Ω, m)` to
`(Ω, mΩ)` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`. It exists when that joint law has a
unique conditional kernel, for example when `Ω` is a standard Borel space and `μ.trim hm` is
σ-finite (`ProbabilityTheory.hasUniqueCondKernel_condExpJointLaw`).

If `μ.trim hm` is σ-finite, every Markov representative `η` satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(η ω)` for integrable `f`
(`ProbabilityTheory.condExp_ae_eq_integral_condExpKernel`). The representatives are those of the
conditional distribution of the identity given the identity, where the second identity is viewed as
a map from `Ω` with the σ-algebra `mΩ` to `Ω` with the σ-algebra `m`
(`ProbabilityTheory.mem_condExpKernel_iff_mem_condDistrib`). -/
noncomputable def condExpKernel (μ : Measure Ω) (hm : m ≤ mΩ)
    [(condExpJointLaw μ hm).HasUniqueCondKernel] : @Kernel.AEClass Ω (ae (μ.trim hm)) Ω m mΩ :=
  (condExpJointLaw μ hm).condKernel.copy (congrArg ae (fst_condExpJointLaw μ hm)).symm

/-- `condExpKernel μ hm` is represented by a Markov kernel. -/
lemma exists_isMarkovKernel_mem_condExpKernel (μ : Measure Ω) (hm : m ≤ mΩ)
    [(condExpJointLaw μ hm).HasUniqueCondKernel] :
    ∃ η : @Kernel Ω Ω m mΩ, IsMarkovKernel η ∧ η ∈ condExpKernel μ hm :=
  let ⟨η, h₁, _, h₂⟩ := (condExpJointLaw μ hm).exists_isMarkovKernel_mem_condKernel
  ⟨η, h₁, (Kernel.AEClass.mem_copy _).2 h₂⟩

/-- The law of the identity from `(Ω, mΩ)` to `(Ω, m)` is the trim of `μ`, so it is σ-finite when
the trim is. -/
private lemma sigmaFinite_map_id {hm : m ≤ mΩ} [SigmaFinite (μ.trim hm)] :
    SigmaFinite (@Measure.map Ω Ω mΩ m id μ
      (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm))) := by
  rw [← trim_eq_map hm]
  infer_instance

variable {hm : m ≤ mΩ} [(condExpJointLaw μ hm).HasUniqueCondKernel] {η : @Kernel Ω Ω m mΩ}

/-- The class of `condExpJointLaw μ hm` is that of the joint law of the identity from `(Ω, mΩ)` to
`(Ω, m)` and the identity, which defines the conditional distribution of the identity given the
identity: the two measures are definitionally equal. -/
private lemma hasUniqueCondKernel_map_id_id :
    (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun a ↦ (id a, id a)) μ
      (aemeasurable_diag_of_le μ hm)).HasUniqueCondKernel :=
  ‹(condExpJointLaw μ hm).HasUniqueCondKernel›

/-- The representatives of `condExpKernel μ hm` are those of the conditional kernel of the joint
law of `(ω, ω)`. -/
lemma mem_condExpKernel_iff_mem_condKernel :
    η ∈ condExpKernel μ hm ↔ η ∈ (condExpJointLaw μ hm).condKernel :=
  Kernel.AEClass.mem_copy _

/-- A representative of `condExpKernel μ hm` disintegrates the joint law of `(ω, ω)`. -/
lemma isCondKernel_of_mem_condExpKernel (hη : η ∈ condExpKernel μ hm) :
    (condExpJointLaw μ hm).IsCondKernel η :=
  Measure.isCondKernel_of_mem_condKernel (mem_condExpKernel_iff_mem_condKernel.1 hη)

/-- The composition-product of `μ.trim hm` with a representative of `condExpKernel μ hm` exists,
since the representative disintegrates the joint law of `(ω, ω)`, whose first marginal is
`μ.trim hm`. -/
lemma hasCompProd_trim_of_mem_condExpKernel (hη : η ∈ condExpKernel μ hm) :
    (μ.trim hm).HasCompProd η := by
  have := isCondKernel_of_mem_condExpKernel hη
  rw [← fst_condExpJointLaw μ hm]
  infer_instance

/-- Every representative `η` of `condExpKernel μ hm` satisfies
`(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`; the composition-product exists by
`ProbabilityTheory.hasCompProd_trim_of_mem_condExpKernel`. -/
lemma compProd_trim_condExpKernel [(μ.trim hm).HasCompProd η] (hη : η ∈ condExpKernel μ hm) :
    (μ.trim hm) ⊗ₘ η = condExpJointLaw μ hm := by
  have := isCondKernel_of_mem_condExpKernel hη
  rw [Measure.compProd_congr_measure (fst_condExpJointLaw μ hm).symm]
  exact Measure.disintegrate _ η

/-- A kernel `η` with `(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))` represents `condExpKernel μ hm`
if `μ.trim hm` is σ-finite. -/
lemma mem_condExpKernel_of_compProd_eq [SigmaFinite (μ.trim hm)] [(μ.trim hm).HasCompProd η]
    (h : (μ.trim hm) ⊗ₘ η = condExpJointLaw μ hm) :
    η ∈ condExpKernel μ hm := by
  have : (condExpJointLaw μ hm).IsCondKernel η := .of_compProd_eq (fst_condExpJointLaw μ hm) h
  exact mem_condExpKernel_iff_mem_condKernel.2 Measure.IsCondKernel.mem_condKernel

/-- A kernel `η` for which `(μ.trim hm) ⊗ₘ η` exists represents `condExpKernel μ hm` if and only if
`(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`, if `μ.trim hm` is σ-finite. -/
lemma mem_condExpKernel_iff [SigmaFinite (μ.trim hm)] [(μ.trim hm).HasCompProd η] :
    η ∈ condExpKernel μ hm ↔ (μ.trim hm) ⊗ₘ η = condExpJointLaw μ hm :=
  ⟨compProd_trim_condExpKernel, mem_condExpKernel_of_compProd_eq⟩

/-- A Markov kernel `η` represents `condExpKernel μ hm` if and only if
`(μ.trim hm) ⊗ₘ η = μ.map (fun ω ↦ (ω, ω))`. Unlike for a kernel that is not Markov, the class of
the joint law suffices. -/
lemma mem_condExpKernel_iff_of_isMarkovKernel [IsMarkovKernel η] :
    η ∈ condExpKernel μ hm ↔ (μ.trim hm) ⊗ₘ η = condExpJointLaw μ hm :=
  ⟨compProd_trim_condExpKernel, fun h ↦ mem_condExpKernel_iff_mem_condKernel.2
    (Measure.mem_condKernel_iff_of_isMarkovKernel.2 (.of_compProd_eq (fst_condExpJointLaw μ hm) h))⟩

/-- The representatives of `condExpKernel μ hm` are those of the conditional distribution of the
identity given the identity, the second identity being viewed as a map from `Ω` with the σ-algebra
`mΩ` to `Ω` with the σ-algebra `m`: both are the conditional kernel of the joint law of
`(ω, ω)`. -/
lemma mem_condExpKernel_iff_mem_condDistrib :
    η ∈ condExpKernel μ hm ↔
      η ∈ @condDistrib Ω Ω Ω mΩ mΩ m id id μ (aemeasurable_diag_of_le μ hm) ‹_› := by
  have := hasUniqueCondKernel_map_id_id (μ := μ) (hm := hm)
  exact mem_condExpKernel_iff_mem_condKernel.trans
    (mem_condDistrib_iff_mem_condKernel (mβ := m) (X := id) (Y := id)
      (aemeasurable_diag_of_le μ hm)).symm

/-- Every representative `η` of `condExpKernel μ hm` satisfies `η ∘ₘ μ.trim hm = μ`. -/
lemma condExpKernel_comp_trim (hη : η ∈ condExpKernel μ hm) : η ∘ₘ μ.trim hm = μ := by
  have := hasCompProd_trim_of_mem_condExpKernel hη
  rw [← Measure.snd_compProd, compProd_trim_condExpKernel hη, snd_condExpJointLaw]

/-! The measurability and integrability statements below hold for every representative and every
measure: a function on `Ω` integrates against `μ = η ∘ₘ μ.trim hm`
(`ProbabilityTheory.condExpKernel_comp_trim`) through its integrals against the measures `η ω`. -/

section Measurability

variable [NormedAddCommGroup F] {f : Ω → F}

/-- An almost everywhere strongly measurable function agrees with its strongly measurable version
almost everywhere for `η ω`, for `μ.trim hm`-almost every `ω`. -/
lemma aestronglyMeasurable_trim_condExpKernel (hη : η ∈ condExpKernel μ hm)
    (hf : AEStronglyMeasurable f μ) :
    ∀ᵐ ω ∂(μ.trim hm), f =ᵐ[η ω] hf.mk f := by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hη]
  exact hf.ae_eq_mk

theorem aestronglyMeasurable_integral_condExpKernel [NormedSpace ℝ F]
    (hη : η ∈ condExpKernel μ hm) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂η ω) μ :=
  ⟨fun ω ↦ ∫ y, hf.mk f y ∂η ω, hf.stronglyMeasurable_mk.integral_kernel,
    ae_of_ae_trim hm ((aestronglyMeasurable_trim_condExpKernel hη hf).mono fun _ hω ↦
      integral_congr_ae hω)⟩

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel [NormedSpace ℝ F]
    (hη : η ∈ condExpKernel μ hm) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂η ω) μ :=
  (aestronglyMeasurable_integral_condExpKernel hη hf).mono hm

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω → F}

theorem _root_.MeasureTheory.Integrable.condExpKernel_ae (hη : η ∈ condExpKernel μ hm)
    (hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Integrable f (η ω) := by
  have h : Integrable f (η ∘ₘ μ.trim hm) := by rwa [condExpKernel_comp_trim hη]
  exact ae_of_ae_trim hm (Measure.ae_integrable_of_integrable_comp h)

theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel (hη : η ∈ condExpKernel μ hm)
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂η ω) μ := by
  have h : Integrable f (η ∘ₘ μ.trim hm) := by rwa [condExpKernel_comp_trim hη]
  exact integrable_of_integrable_trim hm (Measure.integrable_integral_norm_of_integrable_comp h)

theorem _root_.MeasureTheory.Integrable.integral_condExpKernel [NormedSpace ℝ F]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂η ω) μ :=
  (hf_int.integral_norm_condExpKernel hη).mono (hf_int.1.integral_condExpKernel hη)
    (ae_of_all _ fun _ ↦ (norm_integral_le_integral_norm _).trans (Real.le_norm_self _))

theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel [NormedSpace ℝ F]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂η ω‖) μ :=
  (hf_int.integral_condExpKernel hη).norm

end Integrability

/-- If `μ.trim hm` is σ-finite, then for every Markov representative `η` of `condExpKernel μ hm`,
every measurable set `s` with `μ s ≠ ∞`, and almost every `ω`, `η ω s` is the conditional
probability `μ⟦s | m⟧ ω`. -/
lemma condExpKernel_ae_eq_condExp [SigmaFinite (μ.trim hm)] [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) {s : Set Ω} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞ := by finiteness) :
    (fun ω ↦ (η ω).real s) =ᵐ[μ] μ⟦s | m⟧ := by
  have := sigmaFinite_map_id (μ := μ) (hm := hm)
  have := hasUniqueCondKernel_map_id_id (μ := μ) (hm := hm)
  have h := condDistrib_ae_eq_condExp (μ := μ) (measurable_id'' hm) measurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη) hs hμs
  simp only [id_eq, SigmaAlgebra.comap_id, preimage_id_eq] at h
  exact h

lemma condExpKernel_ae_eq_trim_condExp [SigmaFinite (μ.trim hm)] [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) {s : Set Ω} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞ := by finiteness) :
    (fun ω ↦ (η ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  simp_rw [measureReal_def]
  rw [(η.measurable_coe hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hη hs hμs

/-- If the law of `Y` is σ-finite, a representative of the conditional distribution of `X` given
`Y`, composed with `Y`, agrees almost everywhere with the image under `X` of a representative of
`condExpKernel μ hY.comap_le` on every measurable set: both are measurable with respect to
`mγ.comap Y`, with the integral `μ (t ∩ X ⁻¹' s)` over each of its sets `t`. -/
lemma condDistrib_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} {X : Ω → β} {Y : Ω → γ} (hX : Measurable X) (hY : Measurable Y)
    [SigmaFinite (μ.map Y hY.aemeasurable)] {s : Set β} (hs : MeasurableSet s)
    [(μ.map (fun a => (Y a, X a)) (hY.aemeasurable.prodMk hX.aemeasurable)).HasUniqueCondKernel]
    {η₁ : Kernel γ β} (hη₁ : η₁ ∈ condDistrib X Y μ (hY.aemeasurable.prodMk hX.aemeasurable))
    [(condExpJointLaw μ hY.comap_le).HasUniqueCondKernel]
    {η₂ : @Kernel Ω Ω (mγ.comap Y) mΩ} (hη₂ : η₂ ∈ condExpKernel μ hY.comap_le) :
    (fun a ↦ η₁ (Y a) s) =ᵐ[μ] fun a ↦ η₂.map X hX a s := by
  have := sigmaFinite_trim_comap (μ := μ) hY
  have := hasUniqueCondKernel_map_id_id (μ := μ) (hm := hY.comap_le)
  simp_rw [Kernel.map_apply' _ _ hs hX]
  have h₁ : Measurable[mγ.comap Y] fun a ↦ η₁ (Y a) s :=
    (η₁.measurable_coe hs).comp (comap_measurable Y)
  have h₂ : Measurable[mγ.comap Y] fun a ↦ η₂ a (X ⁻¹' s) := η₂.measurable_coe (hX hs)
  refine ae_of_ae_trim hY.comap_le (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite h₁ h₂
    fun t ht _ ↦ ?_)
  rw [setLIntegral_trim hY.comap_le h₁ ht, setLIntegral_trim hY.comap_le h₂ ht,
    setLIntegral_condDistrib_of_measurableSet hY hX.aemeasurable hη₁ hs ht]
  have h := setLIntegral_condDistrib_of_measurableSet (μ := μ) (mβ := mγ.comap Y) (X := id)
    (Y := id) (measurable_id'' hY.comap_le) aemeasurable_id
    (mem_condExpKernel_iff_mem_condDistrib.1 hη₂) (hX hs) (t := t) ⟨t, ht, rfl⟩
  simpa using h.symm

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is almost everywhere equal to
the integral `∫ y, f y ∂(η ω)` for every Markov representative `η` of `condExpKernel μ hm`, if
`μ.trim hm` is σ-finite. -/
theorem condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] [SigmaFinite (μ.trim hm)] [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂η ω := by
  have := sigmaFinite_map_id (μ := μ) (hm := hm)
  have := hasUniqueCondKernel_map_id_id (μ := μ) (hm := hm)
  have hX : @Measurable Ω Ω mΩ m id := measurable_id'' hm
  have h := condExp_ae_eq_integral_condDistrib_id hX hf_int
    (mem_condExpKernel_iff_mem_condDistrib.1 hη)
  simpa only [SigmaAlgebra.comap_id, id_eq] using! h

/-- Auxiliary lemma for `condExp_ae_eq_trim_integral_condExpKernel`. -/
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
    [NormedAddCommGroup F] {f : Ω → F} [NormedSpace ℝ F] [CompleteSpace F] [SigmaFinite (μ.trim hm)]
    [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) (hf : StronglyMeasurable f)
    (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω ↦ ∫ y, f y ∂η ω := by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact (hf.comp_measurable measurable_snd).integral_kernel_prod_right'
  · exact condExp_ae_eq_integral_condExpKernel hη hf_int

/-- The conditional expectation of `f` with respect to a σ-algebra `m` is
(`μ.trim hm`)-almost everywhere equal to the integral `∫ y, f y ∂(η ω)` for every Markov
representative `η` of `condExpKernel μ hm`, if `μ.trim hm` is σ-finite. -/
theorem condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω → F}
    [NormedSpace ℝ F] [CompleteSpace F] [SigmaFinite (μ.trim hm)] [IsMarkovKernel η]
    (hη : η ∈ condExpKernel μ hm) (hf_int : Integrable f μ) :
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
  [IsFiniteMeasure μ]

lemma condExp_generateFrom_singleton (hs : MeasurableSet s) (hμs : μ s ≠ 0) {f : Ω → F}
    (hf : Integrable f μ) :
    μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ ↦ ∫ x, f x ∂μ[|s] := by
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

lemma condExp_set_generateFrom_singleton (hs : MeasurableSet s) (hμs : μ s ≠ 0)
    (ht : MeasurableSet t) :
    μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ ↦ μ[|s].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_generateFrom_singleton hs hμs <| Integrable.indicator (integrable_const 1) ht

omit [IsFiniteMeasure μ] in
/-- On a measurable set `s` of positive finite measure, every representative of the conditional
expectation kernel given the σ-algebra generated by `s` is the conditional measure `μ[|s]` at
every point of `s`: being measurable for that σ-algebra, it is constant on `s`, and its integral
over `s` of the mass of a measurable set `t` is `μ (s ∩ t)`. -/
lemma condExpKernel_singleton_eq_cond (hs : MeasurableSet s)
    [(condExpJointLaw μ (generateFrom_singleton_le hs)).HasUniqueCondKernel] (hμs₀ : μ s ≠ 0)
    {ξ : @Kernel Ω Ω (generateFrom {s}) mΩ}
    (hξ : ξ ∈ condExpKernel μ (generateFrom_singleton_le hs)) (hμs : μ s ≠ ∞ := by finiteness) :
    ∀ ω ∈ s, ξ ω = μ[|s] := by
  have := hasUniqueCondKernel_map_id_id (μ := μ) (hm := generateFrom_singleton_le hs)
  have h_const (ω : Ω) (hω : ω ∈ s) (ω' : Ω) (hω' : ω' ∈ s) : ξ ω' = ξ ω := by
    ext B hB
    change ω' ∈ {x | ξ x B = ξ ω B}
    have hP : {x | ξ x B = ξ ω B} ∈ SigmaAlgebra.generateFrom {s} :=
      ξ.measurable_coe hB (measurableSet_singleton (ξ ω B))
    have hωP : ω ∈ {x | ξ x B = ξ ω B} := rfl
    rcases mem_generateFrom_singleton_iff.1 hP with h | h | h | h <;> rw [h] at hωP ⊢
    · exact absurd hωP (notMem_empty ω)
    · exact hω'
    · exact absurd hω hωP
    · exact mem_univ ω'
  obtain ⟨ω₀, hω₀⟩ := nonempty_of_measure_ne_zero hμs₀
  have h_eq : ξ ω₀ = μ[|s] := by
    ext B hB
    have h : ∫⁻ a in s, ξ a B ∂μ = μ (s ∩ B) := by
      simpa using setLIntegral_condDistrib_of_measurableSet (μ := μ) (mβ := generateFrom {s})
        (X := id) (Y := id) (measurable_id'' (generateFrom_singleton_le hs)) aemeasurable_id
        (mem_condExpKernel_iff_mem_condDistrib.1 hξ) hB (t := s)
        ⟨s, SigmaAlgebra.mem_generateFrom rfl, rfl⟩
    rw [setLIntegral_congr_fun (g := fun _ ↦ ξ ω₀ B) hs
      (fun ω hω ↦ by rw [h_const ω₀ hω₀ ω hω]), setLIntegral_const] at h
    rw [cond_apply _ B, ← h, mul_comm, mul_assoc, ENNReal.mul_inv_cancel hμs₀ hμs, mul_one]
  exact fun ω hω ↦ (h_const ω₀ hω₀ ω hω).trans h_eq

end Cond

end ProbabilityTheory

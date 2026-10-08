/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Disintegration.Integral

import Mathlib.Probability.Kernel.Deterministic

/-!
# Uniqueness of conditional kernels

We prove that conditional kernels with values in a countably generated space are unique almost
everywhere: two kernels that disintegrate a measure `ρ` whose first marginal is σ-finite agree
`ρ.fst`-almost everywhere, and two kernels that disintegrate a kernel `κ` agree `fst κ a`-almost
everywhere at every `a` at which `fst κ a` is σ-finite. With the existence of a Markov
disintegration (`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean`), such a measure has
a unique conditional kernel when the space is a nonempty standard Borel space. Every representative
of a conditional kernel disintegrates the measure or kernel. A kernel represents
`MeasureTheory.Measure.condKernel ρ` exactly when it disintegrates `ρ` and is a probability measure
almost everywhere, which every disintegration of a measure with a σ-finite first marginal is, and
the representatives of `ProbabilityTheory.Kernel.condKernel κ` are exactly the conditional kernels
of `κ`. Within σ-finite measures, a σ-finite first marginal is also necessary for a Markov
disintegration (`MeasureTheory.Measure.IsCondKernel.sigmaFinite_fst`).

## Main statements

* `MeasureTheory.Measure.IsCondKernel.ae_eq`: a.e. uniqueness of conditional kernels of a measure.
* `MeasureTheory.Measure.hasUniqueCondKernel_of_sigmaFinite_fst`: a measure whose first marginal is
  σ-finite has a unique conditional kernel, for a nonempty standard Borel space.
* `MeasureTheory.Measure.hasUniqueCondKernel_iff_sigmaFinite_fst`: a σ-finite measure has a unique
  conditional kernel if and only if its first marginal is σ-finite.
* `ProbabilityTheory.Kernel.IsCondKernel.ae_eq`: a.e. uniqueness of conditional kernels of a kernel.
* `MeasureTheory.Measure.mem_condKernel_iff_isCondKernel_and_ae_isProbabilityMeasure`: a kernel
  represents `ρ.condKernel` if and only if it disintegrates `ρ` and is a probability measure almost
  everywhere.
* `MeasureTheory.Measure.mem_condKernel_iff`: for a measure whose first marginal is σ-finite, a
  kernel represents `ρ.condKernel` if and only if it disintegrates `ρ`.
* `ProbabilityTheory.Kernel.mem_condKernel_iff`: a kernel represents `κ.condKernel` if and only if
  it disintegrates `κ`.
* `ProbabilityTheory.Kernel.sectR_mem_condKernel_of_mem`: the section over `a` of a representative
  of `κ.condKernel` represents the conditional kernel of the measure `κ a`.
* `MeasureTheory.Measure.hasUniqueCondKernel_map_prodMk_comp`: the joint law of `X` and `f ∘ X`
  has a unique conditional kernel for every measure, for `f` with values in a countably generated
  space.
* `MeasureTheory.Measure.mem_condKernel_smul_iff`: scaling a measure by a nonzero constant keeps its
  conditional kernel.
* `MeasureTheory.Measure.HasUniqueCondKernel.smul`: scaling a measure by a finite constant keeps a
  unique conditional kernel.
-/

public section

open MeasureTheory Set Filter SigmaAlgebra ProbabilityTheory

open scoped ENNReal NNReal MeasureTheory Topology ProbabilityTheory

variable {α β Ω : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} [SigmaAlgebra Ω]

namespace ProbabilityTheory.Kernel

variable {γ : Type*} {mγ : SigmaAlgebra γ}

/-- The kernel equal to `η` at the points where it is a probability measure and to `η₀`
elsewhere. -/
private noncomputable def patch (η η₀ : Kernel γ Ω) : Kernel γ Ω :=
  piecewise (s := {c | η c univ = 1}) (η.measurable_coe .univ (measurableSet_singleton 1)) η η₀

private lemma patch_apply_of_isProbabilityMeasure {η η₀ : Kernel γ Ω} {c : γ}
    (hc : IsProbabilityMeasure (η c)) : patch η η₀ c = η c :=
  ite_eq_left hc.measure_univ

private lemma isMarkovKernel_patch (η η₀ : Kernel γ Ω) [IsMarkovKernel η₀] :
    IsMarkovKernel (patch η η₀) := ⟨fun c ↦ by
  by_cases hc : η c univ = 1
  · rw [show patch η η₀ c = η c from ite_eq_left hc]
    exact ⟨hc⟩
  · rw [show patch η η₀ c = η₀ c from ite_eq_right hc]
    infer_instance⟩

private lemma isFiniteKernel_patch_zero (η : Kernel γ Ω) : IsFiniteKernel (patch η 0) :=
  ⟨⟨1, ENNReal.one_lt_top, fun c ↦ by
    by_cases hc : η c univ = 1
    · rw [show patch η 0 c = η c from ite_eq_left hc, hc]
    · rw [show patch η 0 c = 0 from ite_eq_right hc]
      simp⟩⟩

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {ρ : Measure (α × Ω)} [SigmaFinite ρ.fst]

/-! ### Uniqueness of conditional kernels of a measure -/

/-- Two conditional kernels of a measure `ρ` whose first marginal is σ-finite agree
`ρ.fst`-almost everywhere on a measurable set.

With values in a countably generated space, `MeasureTheory.Measure.IsCondKernel.ae_eq` gives the
stronger statement that the kernels agree almost everywhere, not just on a given measurable set. -/
theorem IsCondKernel.ae_eq_apply (η η' : Kernel α Ω) [ρ.IsCondKernel η] [ρ.IsCondKernel η']
    {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, η x s = η' x s := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe η hs) (Kernel.measurable_coe η' hs) (fun t ht _ ↦ ?_)
  have h (ξ : Kernel α Ω) [ρ.IsCondKernel ξ] : ∫⁻ x in t, ξ x s ∂ρ.fst = ρ (t ×ˢ s) := by
    conv_rhs => rw [← ρ.disintegrate ξ]
    exact (compProd_apply_prod ht hs).symm
  rw [h η, h η']

/-- A conditional kernel of a measure whose first marginal is σ-finite agrees almost everywhere
with a finite conditional kernel: the kernel equal to it where it is a probability measure, which
it is almost everywhere (`MeasureTheory.Measure.IsCondKernel.ae_isProbabilityMeasure`), and to zero
elsewhere. -/
private lemma IsCondKernel.exists_isFiniteKernel_ae_eq (η : Kernel α Ω) [ρ.IsCondKernel η] :
    ∃ ξ : Kernel α Ω, IsFiniteKernel ξ ∧ ρ.IsCondKernel ξ ∧ ⇑η =ᵐ[ρ.fst] ⇑ξ := by
  have := Kernel.isFiniteKernel_patch_zero η
  have h_eq : ⇑η =ᵐ[ρ.fst] ⇑(Kernel.patch η 0) := by
    filter_upwards [IsCondKernel.ae_isProbabilityMeasure ρ η] with a ha
    exact (Kernel.patch_apply_of_isProbabilityMeasure ha).symm
  exact ⟨_, this, ⟨inferInstance, by rw [← compProd_congr h_eq, ρ.disintegrate η]⟩, h_eq⟩

/-- Two conditional kernels of a measure `ρ` whose first marginal is σ-finite, with values in a
countably generated space, agree `ρ.fst`-almost everywhere: they agree almost everywhere with
finite conditional kernels, which agree almost everywhere
(`ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`). -/
theorem IsCondKernel.ae_eq [SigmaAlgebra.CountablyGenerated Ω] (η η' : Kernel α Ω)
    [ρ.IsCondKernel η] [ρ.IsCondKernel η'] :
    ∀ᵐ x ∂ρ.fst, η x = η' x := by
  obtain ⟨ξ, _, _, hξ⟩ := IsCondKernel.exists_isFiniteKernel_ae_eq (ρ := ρ) η
  obtain ⟨ξ', _, _, hξ'⟩ := IsCondKernel.exists_isFiniteKernel_ae_eq (ρ := ρ) η'
  filter_upwards [hξ, hξ',
    Kernel.ae_eq_of_compProd_eq ((ρ.disintegrate ξ).trans (ρ.disintegrate ξ').symm)]
    with x h h' h''
  rw [h, h', h'']

/-- A measure on `α × Ω` whose first marginal is σ-finite, for a nonempty standard Borel space `Ω`,
has a unique conditional kernel. This includes every finite measure; instances supply the
σ-finiteness of the first marginal of a composition-product
(`MeasureTheory.Measure.sigmaFinite_fst_compProd`) and of a joint law
(`MeasureTheory.Measure.sigmaFinite_fst_map_prodMk`). -/
-- see Note [lower instance priority]
instance (priority := 100) hasUniqueCondKernel_of_sigmaFinite_fst [StandardBorelSpace Ω]
    [Nonempty Ω] : ρ.HasUniqueCondKernel :=
  ⟨ρ.exists_isMarkovKernel_isCondKernel, fun η η' _ _ _ _ ↦ IsCondKernel.ae_eq η η'⟩

/-- Within σ-finite measures, a Markov disintegration forces a σ-finite first marginal: for a
positive `f` with a finite `ρ`-integral, `a ↦ ∫⁻ ω, f (a, ω) ∂(η a)` is positive with a finite
`ρ.fst`-integral. -/
theorem IsCondKernel.sigmaFinite_fst {ρ : Measure (α × Ω)} [SigmaFinite ρ] (η : Kernel α Ω)
    [IsMarkovKernel η] [ρ.IsCondKernel η] : SigmaFinite ρ.fst := by
  obtain ⟨f, hf_pos, hf_meas, hf_int⟩ := exists_pos_lintegral_lt_of_sigmaFinite ρ one_ne_zero
  have hf : Measurable fun p ↦ (f p : ℝ≥0∞) := hf_meas.coe_nnreal_ennreal
  set g : α → ℝ≥0∞ := fun a ↦ ∫⁻ ω, f (a, ω) ∂(η a)
  have hg : Measurable g := hf.lintegral_kernel_prod_right'
  have hg_pos (a : α) : g a ≠ 0 := by
    intro h
    have hm : Measurable fun ω ↦ (f (a, ω) : ℝ≥0∞) :=
      (hf_meas.comp measurable_prodMk_left).coe_nnreal_ennreal
    have h0 : ∫⁻ ω, (f (a, ω) : ℝ≥0∞) ∂η a = 0 := h
    rw [lintegral_eq_zero_iff hm] at h0
    have h' : ∀ᵐ ω ∂(η a), False := h0.mono fun ω hω ↦ by simp [(hf_pos _).ne'] at hω
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h'
    exact IsProbabilityMeasure.ne_zero (η a) h'
  have hg_int : ∫⁻ a, g a ∂ρ.fst ≠ ∞ := by
    rw [← Measure.lintegral_compProd hf, ρ.disintegrate η]
    exact (hf_int.trans ENNReal.one_lt_top).ne
  have : IsFiniteMeasure (ρ.fst.withDensity g) := isFiniteMeasure_withDensity hg_int
  have h_inv : (ρ.fst.withDensity g).withDensity (fun a ↦ (g a)⁻¹) = ρ.fst :=
    withDensity_inv_same hg (ae_of_all _ hg_pos) ((ae_lt_top hg hg_int).mono fun _ h ↦ h.ne)
  rw [← h_inv]
  exact SigmaFinite.withDensity_of_ne_top' fun a ↦ ENNReal.inv_ne_top.2 (hg_pos a)

/-- A σ-finite measure on `α × Ω`, for a nonempty standard Borel space `Ω`, has a unique conditional
kernel if and only if its first marginal is σ-finite. Without the σ-finiteness of the measure, the
first marginal need not be σ-finite: see `Counterexamples/CondKernel.lean`. -/
theorem hasUniqueCondKernel_iff_sigmaFinite_fst {ρ : Measure (α × Ω)} [SigmaFinite ρ]
    [StandardBorelSpace Ω] [Nonempty Ω] : ρ.HasUniqueCondKernel ↔ SigmaFinite ρ.fst :=
  ⟨fun h ↦ let ⟨η, _, _⟩ := h.exists_isMarkovKernel_isCondKernel
    IsCondKernel.sigmaFinite_fst η, fun _ ↦ inferInstance⟩

/-- The joint law of `X` and `f ∘ X`, for a measurable `f` with values in a countably generated
space, has a unique conditional kernel, for every measure `μ`: the Dirac kernel of `f`
disintegrates it, and a Markov kernel that disintegrates it gives almost every point `a` no mass on
the measurable sets that `f a` avoids, hence is almost everywhere the Dirac kernel of `f`
(`ProbabilityTheory.Kernel.ae_eq_deterministic_iff`). Instance search cannot supply the
measurability of `f`; instances cover the identity and the constant maps. -/
theorem hasUniqueCondKernel_map_prodMk_comp [SigmaAlgebra.CountablyGenerated Ω] {μ : Measure β}
    {X : β → α} (hX : AEMeasurable X μ) {f : α → Ω} (hf : Measurable f) :
    (μ.map (fun b ↦ (X b, (f ∘ X) b))
      (hX.prodMk (hf.comp_aemeasurable hX))).HasUniqueCondKernel := by
  have hfX : AEMeasurable (f ∘ X) μ := hf.comp_aemeasurable hX
  have hfst : (μ.map (fun b ↦ (X b, (f ∘ X) b)) (hX.prodMk hfX)).fst = μ.map X hX :=
    fst_map_prodMk₀ hX hfX
  have h_det (η : Kernel α Ω) [IsMarkovKernel η]
      [(μ.map (fun b ↦ (X b, (f ∘ X) b)) (hX.prodMk hfX)).IsCondKernel η] :
      η =ᵐ[(μ.map (fun b ↦ (X b, (f ∘ X) b)) (hX.prodMk hfX)).fst]
        Kernel.deterministic f hf := by
    refine (Kernel.ae_eq_deterministic_iff hf).2 fun s hs ↦ ?_
    have hfs : MeasurableSet (f ⁻¹' sᶜ) := hf hs.compl
    have h0 : ∫⁻ a in f ⁻¹' sᶜ, η a s
        ∂(μ.map (fun b ↦ (X b, (f ∘ X) b)) (hX.prodMk hfX)).fst = 0 := by
      rw [← compProd_apply_prod hfs hs, disintegrate _ η,
        map_apply (hfs.prod hs) (hX.prodMk hfX)]
      convert measure_empty (μ := μ)
      ext b
      simp
    filter_upwards [(setLIntegral_eq_zero_iff hfs (η.measurable_coe hs)).1 h0] with a ha hfa
    exact ha hfa
  refine ⟨⟨Kernel.deterministic f hf, inferInstance, .of_compProd_eq hfst ?_⟩,
    fun η η' _ _ _ _ ↦ ?_⟩
  · rw [compProd_deterministic, map_map hX (measurable_id'.prodMk hf).aemeasurable]
    rfl
  · filter_upwards [h_det η, h_det η'] with a h h' using h.trans h'.symm

/-- The joint law of `(Y, Y)` has a unique conditional kernel, for every measure, in a countably
generated space (`MeasureTheory.Measure.hasUniqueCondKernel_map_prodMk_comp`). -/
instance hasUniqueCondKernel_map_prodMk_self [SigmaAlgebra.CountablyGenerated Ω] {μ : Measure β}
    {Y : β → Ω} {h : AEMeasurable (fun b ↦ (Y b, Y b)) μ} :
    (μ.map (fun b ↦ (Y b, Y b)) h).HasUniqueCondKernel :=
  hasUniqueCondKernel_map_prodMk_comp h.fst measurable_id

/-- The joint law of a map and a constant has a unique conditional kernel, for every measure, in a
countably generated space (`MeasureTheory.Measure.hasUniqueCondKernel_map_prodMk_comp`). -/
instance hasUniqueCondKernel_map_prodMk_const [SigmaAlgebra.CountablyGenerated Ω] {μ : Measure β}
    {X : β → α} {c : Ω} {h : AEMeasurable (fun b ↦ (X b, c)) μ} :
    (μ.map (fun b ↦ (X b, c)) h).HasUniqueCondKernel :=
  hasUniqueCondKernel_map_prodMk_comp (f := fun _ ↦ c) h.fst measurable_const

/-! ### Representatives of the conditional kernel of a measure -/

/-- A representative of `ρ.condKernel` disintegrates `ρ`: it agrees almost everywhere with a
Markov representative, so the composition-product with it exists and is the same. -/
theorem isCondKernel_of_mem_condKernel {ρ : Measure (α × Ω)} [ρ.HasUniqueCondKernel]
    {η : Kernel α Ω} (hη : η ∈ ρ.condKernel) :
    ρ.IsCondKernel η := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  have h := Kernel.AEClass.eventuallyEq_of_mem hη₀ hη
  have : ρ.fst.HasCompProd η := .congr h
  exact ⟨this, by rw [← Measure.compProd_congr h, ρ.disintegrate η₀]⟩

/-- A Markov kernel represents the conditional kernel of a measure with a unique conditional kernel
if and only if it disintegrates the measure. -/
theorem mem_condKernel_iff_of_isMarkovKernel {ρ : Measure (α × Ω)} [ρ.HasUniqueCondKernel]
    {η : Kernel α Ω} [IsMarkovKernel η] :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  refine ⟨fun hη ↦ isCondKernel_of_mem_condKernel hη, fun _ ↦ ?_⟩
  exact Kernel.AEClass.mem_of_eventuallyEq hη₀ (HasUniqueCondKernel.ae_eq_of_isCondKernel η₀ η)

/-- A Markov kernel `κ` represents the conditional kernel of `μ ⊗ₘ κ`, when `μ ⊗ₘ κ` has a unique
conditional kernel, for example when `μ` is σ-finite. -/
lemma mem_condKernel_compProd (μ : Measure α) (κ : Kernel α Ω) [IsMarkovKernel κ]
    [(μ ⊗ₘ κ).HasUniqueCondKernel] : κ ∈ (μ ⊗ₘ κ).condKernel :=
  mem_condKernel_iff_of_isMarkovKernel.2 (.of_compProd_eq (fst_compProd μ κ) rfl)

/-- A kernel represents the conditional kernel of a measure with a unique conditional kernel if and
only if it disintegrates the measure and is a probability measure almost everywhere: it then agrees
almost everywhere with the Markov kernel equal to it where it is a probability measure and to a
Markov representative elsewhere. Without the second condition, a finite kernel can disintegrate
such a measure without representing its conditional kernel (`Counterexamples/CondKernel.lean`). -/
theorem mem_condKernel_iff_isCondKernel_and_ae_isProbabilityMeasure {ρ : Measure (α × Ω)}
    [ρ.HasUniqueCondKernel] {η : Kernel α Ω} :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η ∧ ∀ᵐ a ∂ρ.fst, IsProbabilityMeasure (η a) := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  refine ⟨fun hη ↦ ⟨isCondKernel_of_mem_condKernel hη, ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · filter_upwards [Kernel.AEClass.eventuallyEq_of_mem hη hη₀] with a ha
    rw [ha]
    infer_instance
  have := Kernel.isMarkovKernel_patch η η₀
  have h_eq : ⇑η =ᵐ[ρ.fst] ⇑(Kernel.patch η η₀) := by
    filter_upwards [h] with a ha using (Kernel.patch_apply_of_isProbabilityMeasure ha).symm
  have : ρ.IsCondKernel (Kernel.patch η η₀) :=
    ⟨inferInstance, by rw [← compProd_congr h_eq, ρ.disintegrate η]⟩
  exact Kernel.AEClass.mem_of_eventuallyEq (mem_condKernel_iff_of_isMarkovKernel.2 this) h_eq.symm

/-- A kernel represents `ρ.condKernel`, for a measure `ρ` whose first marginal is σ-finite, if and
only if it disintegrates `ρ`, since such a disintegration is a probability measure almost
everywhere (`MeasureTheory.Measure.IsCondKernel.ae_isProbabilityMeasure`). A unique conditional
kernel alone does not suffice for a finite kernel that is not Markov: see
`Counterexamples/CondKernel.lean`. -/
theorem mem_condKernel_iff [ρ.HasUniqueCondKernel] {η : Kernel α Ω} :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η :=
  ⟨isCondKernel_of_mem_condKernel, fun _ ↦
    mem_condKernel_iff_isCondKernel_and_ae_isProbabilityMeasure.2
      ⟨‹_›, IsCondKernel.ae_isProbabilityMeasure ρ η⟩⟩

/-- Every conditional kernel of a measure `ρ` whose first marginal is σ-finite represents
`ρ.condKernel`. -/
theorem IsCondKernel.mem_condKernel [ρ.HasUniqueCondKernel] {η : Kernel α Ω}
    [ρ.IsCondKernel η] : η ∈ ρ.condKernel :=
  mem_condKernel_iff.2 ‹_›

/-- Scaling a measure by a nonzero constant keeps its conditional kernel, whenever both measures
have one: a Markov disintegration of the measure also disintegrates the scaled measure, and the
scaling does not change the null sets of the first marginal. -/
theorem mem_condKernel_smul_iff {ρ : Measure (α × Ω)} {c : ℝ≥0∞} (hc₀ : c ≠ 0)
    [ρ.HasUniqueCondKernel] [(c • ρ).HasUniqueCondKernel] {η : Kernel α Ω} :
    η ∈ (c • ρ).condKernel ↔ η ∈ ρ.condKernel := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  have hfst : (c • ρ).fst = c • ρ.fst := by
    ext s hs
    simp [fst_apply hs]
  have : (c • ρ).IsCondKernel η₀ :=
    ⟨inferInstance, by rw [hfst, compProd_smul_left, ρ.disintegrate η₀]⟩
  have hη₀' : η₀ ∈ (c • ρ).condKernel := mem_condKernel_iff_of_isMarkovKernel.2 this
  rw [Kernel.AEClass.mem_iff_eventuallyEq hη₀', Kernel.AEClass.mem_iff_eventuallyEq hη₀, hfst,
    ae_ennreal_smul_measure_eq hc₀]

/-- Scaling a measure with a unique conditional kernel by a finite constant keeps a unique
conditional kernel: for a nonzero constant, a Markov kernel disintegrates the scaled measure exactly
when it disintegrates the measure, and the null sets of the first marginal do not change. It fails
for the constant `∞`, whose multiples of two measures with the same null sets agree: the constant
kernels of `gaussianReal 0 1` and `gaussianReal 1 1` both disintegrate
`∞ • (dirac () ⊗ₘ Kernel.const Unit (gaussianReal 0 1))`, which is
`(∞ • dirac ()) ⊗ₘ Kernel.const Unit (gaussianReal 0 1)` by `compProd_smul_left`
(`Counterexample.CondKernel.not_hasUniqueCondKernel_infGaussian`). -/
lemma HasUniqueCondKernel.smul {ρ : Measure (α × Ω)} [ρ.HasUniqueCondKernel] {c : ℝ≥0∞}
    (hc : c ≠ ∞) : (c • ρ).HasUniqueCondKernel := by
  have hfst : (c • ρ).fst = c • ρ.fst := by
    ext s hs
    simp [fst_apply hs]
  obtain ⟨η₀, _, _⟩ := HasUniqueCondKernel.exists_isMarkovKernel_isCondKernel (ρ := ρ)
  refine ⟨⟨η₀, inferInstance, ⟨inferInstance, ?_⟩⟩, fun η η' _ _ _ _ ↦ ?_⟩
  · rw [hfst, compProd_smul_left, ρ.disintegrate η₀]
  rcases eq_or_ne c 0 with rfl | hc₀
  · simp
  have h_cond (ξ : Kernel α Ω) [IsMarkovKernel ξ] [(c • ρ).IsCondKernel ξ] : ρ.IsCondKernel ξ := by
    refine ⟨inferInstance, ?_⟩
    have h : c • (ρ.fst ⊗ₘ ξ) = c • ρ := by
      rw [← compProd_smul_left, ← compProd_congr_measure hfst, (c • ρ).disintegrate ξ]
    calc ρ.fst ⊗ₘ ξ = c⁻¹ • c • (ρ.fst ⊗ₘ ξ) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul]
      _ = ρ := by rw [h, smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul]
  have := h_cond η
  have := h_cond η'
  rw [hfst, ae_ennreal_smul_measure_eq hc₀]
  exact HasUniqueCondKernel.ae_eq_of_isCondKernel η η'

/-- Scaling by a nonnegative real number keeps a unique conditional kernel
(`MeasureTheory.Measure.HasUniqueCondKernel.smul`). -/
instance HasUniqueCondKernel.smul_nnreal {ρ : Measure (α × Ω)} [ρ.HasUniqueCondKernel] (c : ℝ≥0) :
    (c • ρ).HasUniqueCondKernel := by
  rw [← coe_nnreal_smul]
  exact HasUniqueCondKernel.smul ENNReal.coe_ne_top

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

/-! ### Uniqueness of conditional kernels of a kernel -/

variable {κ : Kernel α (β × Ω)}

/-- Two conditional kernels of a kernel `κ` with values in a countably generated space agree
`fst κ a`-almost everywhere at every `a` at which `fst κ a` is σ-finite, since their sections there
are conditional kernels of the measure `κ a`
(`ProbabilityTheory.Kernel.IsCondKernel.isCondKernel_sectR`). -/
theorem IsCondKernel.ae_eq [SigmaAlgebra.CountablyGenerated Ω] (η η' : Kernel (α × β) Ω)
    [κ.IsCondKernel η] [κ.IsCondKernel η'] (a : α) [SigmaFinite (fst κ a)] :
    ∀ᵐ b ∂(fst κ a), η (a, b) = η' (a, b) := by
  have := IsCondKernel.isCondKernel_sectR κ η a
  have := IsCondKernel.isCondKernel_sectR κ η' a
  rw [fst_apply_eq_fst]
  filter_upwards [Measure.IsCondKernel.ae_eq (ρ := κ a) (sectR η a) (sectR η' a)] with b hb
  simpa using hb

/-- The section over `a` of a conditional kernel of `κ` represents the conditional kernel of the
measure `κ a`, when `fst κ a` is σ-finite. -/
lemma IsCondKernel.sectR_mem_condKernel {η : Kernel (α × β) Ω} [κ.IsCondKernel η] (a : α)
    [(κ a).HasUniqueCondKernel] [SigmaFinite (fst κ a)] :
    sectR η a ∈ (κ a).condKernel := by
  have := IsCondKernel.isCondKernel_sectR κ η a
  exact Measure.IsCondKernel.mem_condKernel

/-! ### Representatives of the conditional kernel of a kernel -/

variable [IsFiniteKernel κ] [StandardBorelSpace Ω] [Nonempty Ω] [CountableOrCountablyGenerated α β]

/-- A representative of `condKernel κ` disintegrates `κ`: it agrees almost everywhere on every fiber
with a Markov representative, so the composition-product with it exists and is the same. -/
theorem isCondKernel_of_mem_condKernel {η : Kernel (α × β) Ω} (hη : η ∈ condKernel κ) :
    κ.IsCondKernel η := by
  obtain ⟨η₀, _, _, hη₀⟩ := exists_isMarkovKernel_mem_condKernel κ
  have h := eventuallyEq_fiberwiseAE_iff.1 (AEClass.eventuallyEq_of_mem hη₀ hη)
  have : (fst κ).HasCompProd η := .congr h
  exact ⟨this, by rw [← compProd_congr h, κ.disintegrate η₀]⟩

/-- Every conditional kernel of `κ` represents `condKernel κ`: on every fiber it is almost
everywhere a probability measure (`ProbabilityTheory.Kernel.IsCondKernel.ae_isProbabilityMeasure`),
so it agrees almost everywhere on every fiber with the Markov kernel equal to it where it is a
probability measure and to a Markov representative elsewhere. -/
theorem IsCondKernel.mem_condKernel {η : Kernel (α × β) Ω} [κ.IsCondKernel η] :
    η ∈ condKernel κ := by
  obtain ⟨η₀, _, _, hη₀⟩ := exists_isMarkovKernel_mem_condKernel κ
  have := isMarkovKernel_patch η η₀
  have h_eq (a : α) : ∀ᵐ b ∂(fst κ a), η (a, b) = patch η η₀ (a, b) := by
    filter_upwards [IsCondKernel.ae_isProbabilityMeasure κ η a] with b hb
    exact (patch_apply_of_isProbabilityMeasure hb).symm
  have : κ.IsCondKernel (patch η η₀) :=
    ⟨inferInstance, by rw [← compProd_congr h_eq, κ.disintegrate η]⟩
  refine AEClass.mem_of_eventuallyEq hη₀ (eventuallyEq_fiberwiseAE_iff.2 fun a ↦ ?_)
  filter_upwards [IsCondKernel.ae_eq η₀ (patch η η₀) a, h_eq a] with b h₁ h₂ using
    h₁.trans h₂.symm

/-- A kernel represents `condKernel κ` if and only if it disintegrates `κ`. -/
theorem mem_condKernel_iff {η : Kernel (α × β) Ω} : η ∈ condKernel κ ↔ κ.IsCondKernel η :=
  ⟨isCondKernel_of_mem_condKernel, fun _ ↦ IsCondKernel.mem_condKernel⟩

/-- The section over `a` of a representative of `condKernel κ` represents the conditional kernel of
the measure `κ a`. -/
lemma sectR_mem_condKernel_of_mem {η : Kernel (α × β) Ω} (hη : η ∈ condKernel κ) (a : α) :
    sectR η a ∈ (κ a).condKernel :=
  have := isCondKernel_of_mem_condKernel hη
  IsCondKernel.sectR_mem_condKernel a

end ProbabilityTheory.Kernel

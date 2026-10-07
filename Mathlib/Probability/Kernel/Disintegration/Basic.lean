/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if the
composition-product `ρ.fst ⊗ₘ ρCond` exists and equals `ρ`.

A kernel `κ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if the
composition-product `κ.fst ⊗ₖ κCond` exists and equals `κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `MeasureTheory.Measure.HasUniqueCondKernel ρ`: some Markov kernel disintegrates `ρ`, and any two
  agree `ρ.fst`-almost everywhere.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is an s-finite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` for a **construction** of
disintegrating kernels.
-/

@[expose] public section

open MeasureTheory Set Filter SigmaAlgebra ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} {mΩ : SigmaAlgebra Ω}

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure
variable (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)

/-- A kernel `ρCond` is a conditional kernel for a measure `ρ` if it disintegrates it in the sense
that the composition-product of the first marginal `ρ.fst` with `ρCond` exists and equals `ρ`.
A conditional kernel need not be s-finite, even for a nonzero `ρ`: see
`Counterexamples/KernelCompProd.lean`. -/
class IsCondKernel : Prop where
  /-- The composition-product of `ρ.fst` with `ρCond` exists. -/
  hasCompProd_fst : ρ.fst.HasCompProd ρCond
  disintegrate :
    haveI := hasCompProd_fst
    ρ.fst ⊗ₘ ρCond = ρ

attribute [instance] IsCondKernel.hasCompProd_fst

/-- A measure `ρ` on `α × Ω` has a unique conditional kernel if some Markov kernel disintegrates
it and any two Markov kernels that disintegrate it agree `ρ.fst`-almost everywhere. These are the
measures whose conditional kernel `MeasureTheory.Measure.condKernel`, the almost-everywhere class of
these Markov kernels, is determined. A finite measure has a unique conditional kernel when `Ω` is a
nonempty standard Borel space (`MeasureTheory.Measure.hasUniqueCondKernel_of_isFiniteMeasure`). -/
class HasUniqueCondKernel : Prop where
  /-- Some Markov kernel disintegrates `ρ`. -/
  exists_isMarkovKernel_isCondKernel : ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η
  /-- Two Markov kernels that disintegrate `ρ` agree `ρ.fst`-almost everywhere. -/
  ae_eq_of_isCondKernel (η η' : Kernel α Ω) [IsMarkovKernel η] [IsMarkovKernel η']
    [ρ.IsCondKernel η] [ρ.IsCondKernel η'] : ∀ᵐ a ∂ρ.fst, η a = η' a

variable [ρ.IsCondKernel ρCond]

lemma disintegrate : ρ.fst ⊗ₘ ρCond = ρ := IsCondKernel.disintegrate

variable [IsFiniteMeasure ρ]

/-- Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`. -/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := by
    obtain rfl | hax := eq_or_ne a x
    · simp only [singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_notMem]
      have : Prod.mk a ⁻¹' Prod.mk x '' s = ∅ := by ext y; simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) (s : Set Ω) : ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]

lemma IsCondKernel.isProbabilityMeasure [MeasurableSingletonClass α] {a : α} (ha : ρ.fst {a} ≠ 0) :
    IsProbabilityMeasure (ρCond a) := by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha, prod_univ, ← Measure.fst_apply
    (measurableSet_singleton _), ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]

lemma IsCondKernel.isMarkovKernel [MeasurableSingletonClass α] (hρ : ∀ a, ρ.fst {a} ≠ 0) :
    IsMarkovKernel ρCond := ⟨fun _ ↦ isProbabilityMeasure _ _ (hρ _)⟩

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel. It also proves that if `κ`
is an s-finite kernel from a countable `α` such that each measure `κ a` is disintegrated by some
kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.
-/

namespace ProbabilityTheory.Kernel
variable (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

/-- A kernel `κCond` is a conditional kernel for a kernel `κ` if it disintegrates it in the sense
that the composition-product of `κ.fst` with `κCond` exists and equals `κ`. -/
class IsCondKernel : Prop where
  /-- The composition-product of `κ.fst` with `κCond` exists. -/
  protected hasCompProd_fst : κ.fst.HasCompProd κCond
  protected disintegrate :
    haveI := hasCompProd_fst
    κ.fst ⊗ₖ κCond = κ

attribute [instance] IsCondKernel.hasCompProd_fst

instance instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond where
  hasCompProd_fst := by rw [fst_zero]; infer_instance
  disintegrate := by simp

lemma disintegrate [κ.IsCondKernel κCond] : κ.fst ⊗ₖ κCond = κ := IsCondKernel.disintegrate

/-- A conditional kernel is almost everywhere a probability measure. -/
lemma IsCondKernel.isProbabilityMeasure_ae [IsFiniteKernel κ.fst] [κ.IsCondKernel κCond] (a : α) :
    ∀ᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have h := disintegrate κ κCond
  suffices ∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ ↦ measure_univ, fun h ↦ ⟨h⟩⟩
  suffices (∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ ≤ 1)
      ∧ (∀ᵐ b ∂(κ.fst a), 1 ≤ κCond (a, b) Set.univ) by
    filter_upwards [this.1, this.2] with b h1 h2 using le_antisymm h1 h2
  have h_eq s (hs : MeasurableSet s) :
      ∫⁻ b, s.indicator (fun b ↦ κCond (a, b) Set.univ) b ∂κ.fst a = κ.fst a s := by
    conv_rhs => rw [← h]
    rw [fst_compProd_apply _ _ _ hs]
  have h_meas : Measurable fun b ↦ κCond (a, b) Set.univ :=
    (κCond.measurable_coe MeasurableSet.univ).comp measurable_prodMk_left
  constructor
  · rw [ae_le_const_iff_forall_gt_measure_zero]
    intro r hr
    let s := {b | r ≤ κCond (a, b) Set.univ}
    have hs : MeasurableSet s := h_meas measurableSet_Ici
    have h_2_le : s.indicator (fun _ ↦ r) ≤ s.indicator (fun b ↦ (κCond (a, b)) Set.univ) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) ≤ κ.fst a s :=
      (lintegral_mono h_2_le).trans_eq (h_eq s hs)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_lhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness
  · rw [ae_const_le_iff_forall_lt_measure_zero]
    intro r hr
    let s := {b | κCond (a, b) Set.univ ≤ r}
    have hs : MeasurableSet s := h_meas measurableSet_Iic
    have h_2_le : s.indicator (fun b ↦ (κCond (a, b)) Set.univ) ≤ s.indicator (fun _ ↦ r) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : κ.fst a s ≤ ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) :=
      (h_eq s hs).symm.trans_le (lintegral_mono h_2_le)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_rhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness


/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable
variable [Countable α] (κCond : α → Kernel β Ω)

/-- The kernel `(a, b) ↦ κCond a b` on `α × β`, for a countable `α`. When every `κCond a` is a
Markov conditional kernel of `κ a` for an s-finite `κ : Kernel α (β × Ω)`, it disintegrates `κ`
(`ProbabilityTheory.Kernel.condKernelCountable.instIsCondKernel`); this supplies the witness of
`ProbabilityTheory.Kernel.exists_isMarkovKernel_isCondKernel` when `α` is countable. -/
noncomputable def condKernelCountable
    (h_class : ∀ x y, x ∈ (inferInstance : SigmaAlgebra α).indistinguishabilityClass y →
      κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a ↦ (κCond a).measurable) fun x y hx hy ↦ ?_
    simpa using DFunLike.congr (h_class _ _ hy) rfl

lemma condKernelCountable_apply
    (h_class : ∀ x y, x ∈ (inferInstance : SigmaAlgebra α).indistinguishabilityClass y →
      κCond x = κCond y) (p : α × β) :
    condKernelCountable κCond h_class p = κCond p.1 p.2 := rfl

instance condKernelCountable.instIsMarkovKernel [∀ a, IsMarkovKernel (κCond a)]
    (h_class : ∀ x y, x ∈ (inferInstance : SigmaAlgebra α).indistinguishabilityClass y →
      κCond x = κCond y) : IsMarkovKernel (condKernelCountable κCond h_class) where
  isProbabilityMeasure p := (‹∀ a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2

instance condKernelCountable.instIsCondKernel [∀ a, IsMarkovKernel (κCond a)]
    (h_class : ∀ x y, x ∈ (inferInstance : SigmaAlgebra α).indistinguishabilityClass y →
      κCond x = κCond y) (κ : Kernel α (β × Ω))
    [IsSFiniteKernel κ] [∀ a, (κ a).IsCondKernel (κCond a)] :
    κ.IsCondKernel (condKernelCountable κCond h_class) := by
  refine ⟨inferInstance, ?_⟩
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable
end ProbabilityTheory.Kernel

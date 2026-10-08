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

variable {ρ ρCond} in
/-- A kernel disintegrates a measure `ρ` if its composition-product with a measure equal to the
first marginal of `ρ` exists and is `ρ`. -/
lemma IsCondKernel.of_compProd_eq {ν : Measure α} (h_fst : ρ.fst = ν) [ν.HasCompProd ρCond]
    (h : ν ⊗ₘ ρCond = ρ) : ρ.IsCondKernel ρCond := by
  subst h_fst
  exact ⟨inferInstance, h⟩

/-- A measure `ρ` on `α × Ω` has a unique conditional kernel if some Markov kernel disintegrates
it and any two Markov kernels that disintegrate it agree `ρ.fst`-almost everywhere. These are the
measures whose conditional kernel `MeasureTheory.Measure.condKernel`, the almost-everywhere class of
these Markov kernels, is determined. A measure whose first marginal is σ-finite, in particular a
finite measure, has a unique conditional kernel when `Ω` is a nonempty standard Borel space
(`MeasureTheory.Measure.hasUniqueCondKernel_of_sigmaFinite_fst`). The condition is not necessary,
and without it a conditional kernel need not be unique or exist: see
`Counterexamples/CondKernel.lean`. -/
class HasUniqueCondKernel : Prop where
  /-- Some Markov kernel disintegrates `ρ`. -/
  exists_isMarkovKernel_isCondKernel : ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η
  /-- Two Markov kernels that disintegrate `ρ` agree `ρ.fst`-almost everywhere. -/
  ae_eq_of_isCondKernel (η η' : Kernel α Ω) [IsMarkovKernel η] [IsMarkovKernel η']
    [ρ.IsCondKernel η] [ρ.IsCondKernel η'] : ∀ᵐ a ∂ρ.fst, η a = η' a

/-- A measure on `α × Ω` for an empty type `α` has a unique conditional kernel: it is zero, and the
zero kernel is Markov on the empty type and disintegrates it. -/
instance hasUniqueCondKernel_of_isEmpty [IsEmpty α] : ρ.HasUniqueCondKernel where
  exists_isMarkovKernel_isCondKernel := by
    refine ⟨0, ⟨fun a ↦ isEmptyElim a⟩, ⟨inferInstance, ?_⟩⟩
    rw [compProd_zero_right, Measure.eq_zero_of_isEmpty ρ]
  ae_eq_of_isCondKernel _ _ _ _ _ _ := .of_forall fun a ↦ isEmptyElim a

variable [ρ.IsCondKernel ρCond]

lemma disintegrate : ρ.fst ⊗ₘ ρCond = ρ := IsCondKernel.disintegrate

/-- Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`. -/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) (hx_top : ρ.fst {x} ≠ ∞) {s : Set Ω} (hs : MeasurableSet s) :
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
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx hx_top, one_mul]

/-- If the singleton `{x}` has non-zero finite mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)`. The finiteness is supplied by default for a finite
or σ-finite first marginal. At a point of infinite mass the formula fails for `s = univ`: its
right side vanishes, while `ρ.fst {x} = ρCond x univ * ρ.fst {x}` forces `ρCond x univ ≠ 0`. -/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) (s : Set Ω)
    (hx_top : ρ.fst {x} ≠ ∞ := by measure_singleton_ne_top) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hx_top hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]

/-- A disintegration is a probability measure at a point of non-zero finite mass for `ρ.fst`. -/
lemma IsCondKernel.isProbabilityMeasure [MeasurableSingletonClass α] {a : α} (ha : ρ.fst {a} ≠ 0)
    (ha_top : ρ.fst {a} ≠ ∞ := by measure_singleton_ne_top) :
    IsProbabilityMeasure (ρCond a) := by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha _ ha_top, prod_univ, ← Measure.fst_apply
    (measurableSet_singleton _), ENNReal.inv_mul_cancel ha ha_top]

/-- A disintegration is a Markov kernel if every point has non-zero finite mass for `ρ.fst`. -/
lemma IsCondKernel.isMarkovKernel [MeasurableSingletonClass α] (hρ : ∀ a, ρ.fst {a} ≠ 0)
    (hρ_top : ∀ a, ρ.fst {a} ≠ ∞ := by measure_singleton_ne_top) :
    IsMarkovKernel ρCond := ⟨fun a ↦ isProbabilityMeasure _ _ (hρ a) (hρ_top a)⟩

/-- A disintegration of a measure whose first marginal is σ-finite is a probability measure almost
everywhere, since `ρ.fst t = ∫⁻ a in t, ρCond a univ ∂ρ.fst` for every measurable `t`. -/
lemma IsCondKernel.ae_isProbabilityMeasure [SigmaFinite ρ.fst] :
    ∀ᵐ a ∂ρ.fst, IsProbabilityMeasure (ρCond a) := by
  have h : ∀ᵐ a ∂ρ.fst, ρCond a univ = 1 := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (f := fun a ↦ ρCond a univ)
      (g := fun _ ↦ 1) (ρCond.measurable_coe .univ) measurable_const fun t ht _ ↦ ?_
    rw [← compProd_apply_prod ht .univ, ρ.disintegrate ρCond, setLIntegral_const, one_mul,
      fst_apply ht, prod_univ]
  filter_upwards [h] with a ha using ⟨ha⟩

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

/-- The section over `a` of a conditional kernel of `κ` is a conditional kernel of the measure
`κ a`. -/
lemma IsCondKernel.isCondKernel_sectR [κ.IsCondKernel κCond] (a : α) :
    (κ a).IsCondKernel (sectR κCond a) := by
  have : (κ a).fst.HasCompProd (sectR κCond a) := by rw [← fst_apply_eq_fst]; infer_instance
  refine ⟨this, ?_⟩
  ext s hs
  conv_rhs => rw [← κ.disintegrate κCond]
  rw [Measure.compProd_apply hs, compProd_apply hs, ← fst_apply_eq_fst]
  rfl

/-- On the fiber over a point `a` at which `κ.fst a` is σ-finite, a conditional kernel of `κ` is
almost everywhere a probability measure, as are the disintegrations of a measure with a σ-finite
first marginal (`MeasureTheory.Measure.IsCondKernel.ae_isProbabilityMeasure`). -/
lemma IsCondKernel.ae_isProbabilityMeasure [κ.IsCondKernel κCond] (a : α)
    [SigmaFinite (κ.fst a)] :
    ∀ᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have := IsCondKernel.isCondKernel_sectR κ κCond a
  rw [fst_apply_eq_fst]
  exact Measure.IsCondKernel.ae_isProbabilityMeasure (κ a) (sectR κCond a)


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

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd.Defs
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c)` integrates the `η c`-measures of the sections
against `κ a`, that is, `(κ ∥ₖ η) (a, c) = κ a ⊗ₘ Kernel.const β (η c)`. For s-finite kernels this
is `(κ a).productBySections (η c)`.

These section integrals determine at most one kernel. The class `HasParallelComp κ η` says that
they define one; it is the domain of `κ ∥ₖ η`, and instance search derives it from the s-finiteness
of both kernels.

## Main definitions

* `HasParallelComp κ η`: the parallel composition of `κ` and `η` exists.
* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`. For s-finite kernels,
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`.

## Notation

* `κ ∥ₖ η = ProbabilityTheory.Kernel.parallelComp κ η`

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
  {mγ : SigmaAlgebra γ} {mδ : SigmaAlgebra δ}
  {κ : Kernel α β} {η : Kernel γ δ} {x : α × γ}

/-- The parallel composition of `κ` and `η` exists: at every point `x`, the composition-product of
`κ x.1` with the constant kernel `η x.2` exists, and its values on measurable sets depend
measurably on `x`. Then the section integrals `∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1` are the values
of a unique kernel.

This is the exact domain of `ProbabilityTheory.Kernel.parallelComp`. Instance search derives it
from the s-finiteness of both kernels and supplies it when either kernel is zero. -/
class HasParallelComp (κ : Kernel α β) (η : Kernel γ δ) : Prop where
  /-- At every point, the composition-product of `κ x.1` with the constant kernel `η x.2`
  exists. -/
  hasCompProd_apply (x : α × γ) : (κ x.1).HasCompProd (const β (η x.2))
  /-- The section integrals of a measurable set depend measurably on the point. -/
  measurable_lintegral ⦃s : Set (β × δ)⦄ (hs : MeasurableSet s) :
    Measurable fun x : α × γ ↦ ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1

attribute [instance] HasParallelComp.hasCompProd_apply

/-- Parallel product of two kernels: `(κ ∥ₖ η) x` integrates the `η x.2`-measures of the sections
against `κ x.1`. Its domain is `HasParallelComp κ η`. -/
noncomputable
irreducible_def parallelComp (κ : Kernel α β) (η : Kernel γ δ) [κ.HasParallelComp η] :
    Kernel (α × γ) (β × δ) :=
  { toFun x := κ x.1 ⊗ₘ const β (η x.2)
    measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
      simpa only [Measure.compProd_apply hs, const_apply] using
        HasParallelComp.measurable_lintegral hs }

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

lemma parallelComp_apply' [κ.HasParallelComp η] {s : Set (β × δ)} (hs : MeasurableSet s) :
    (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1 := by
  rw [parallelComp]
  simp [Measure.compProd_apply hs]

/-- Parallel compositions of s-finite kernels exist. -/
instance [IsSFiniteKernel κ] [IsSFiniteKernel η] : κ.HasParallelComp η where
  hasCompProd_apply _ := inferInstance
  measurable_lintegral s hs := by
    refine Measurable.lintegral_kernel_prod_right'
      (f := fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s)) (κ := prodMkRight γ κ) ?_
    have : (fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s))
        = fun y ↦ prodMkRight β (prodMkLeft α η) y (Prod.mk y.2 ⁻¹' s) := rfl
    rw [this]
    exact measurable_kernel_prodMk_left (measurable_fst.snd.prodMk measurable_snd hs)

instance (η : Kernel γ δ) : (0 : Kernel α β).HasParallelComp η where
  hasCompProd_apply _ := by rw [zero_apply]; infer_instance
  measurable_lintegral _ _ := by simp

instance (κ : Kernel α β) : κ.HasParallelComp (0 : Kernel γ δ) where
  hasCompProd_apply _ := by rw [zero_apply, const_zero]; infer_instance
  measurable_lintegral _ _ := by simp

lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).productBySections (η x.2) := by
  ext s hs
  rw [parallelComp_apply' hs, Measure.productBySections_apply hs]

lemma parallelComp_apply_prod [IsSFiniteKernel κ] [IsSFiniteKernel η] (s : Set β) (t : Set δ) :
    (κ ∥ₖ η) x (s ×ˢ t) = (κ x.1 s) * (η x.2 t) := by
  rw [parallelComp_apply, Measure.productBySections_prod]

@[simp]
lemma parallelComp_apply_univ [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) x Set.univ = κ x.1 Set.univ * η x.2 Set.univ := by
  rw [parallelComp_apply, Measure.productBySections_apply .univ, mul_comm]
  simp

@[simp]
lemma parallelComp_zero_left (η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0 := by
  ext x s hs
  simp [parallelComp_apply' hs]

@[simp]
lemma parallelComp_zero_right (κ : Kernel α β) : κ ∥ₖ (0 : Kernel γ δ) = 0 := by
  ext x s hs
  simp [parallelComp_apply' hs]

@[simp]
lemma id_parallelComp_id :
    Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (α × β) (α × β)) := by
  ext : 1
  simp [parallelComp_apply, id_apply, Measure.dirac_productBySections_dirac]

lemma deterministic_parallelComp_deterministic
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (deterministic f hf) ∥ₖ (deterministic g hg)
      = deterministic (Prod.map f g) (hf.prodMap hg) := by
  ext x : 1
  simp_rw [parallelComp_apply, deterministic_apply, Prod.map, Measure.dirac_productBySections_dirac]

lemma lintegral_parallelComp [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_productBySections _ hg.aemeasurable]

lemma lintegral_parallelComp_symm [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ d, ∫⁻ b, g (b, d) ∂κ ac.1 ∂η ac.2 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_productBySections_symm _ hg.aemeasurable]

lemma parallelComp_sum_left {ι : Type*} [Countable ι] (κ : ι → Kernel α β)
    [∀ i, IsSFiniteKernel (κ i)] (η : Kernel γ δ) [IsSFiniteKernel η] :
    Kernel.sum κ ∥ₖ η = Kernel.sum fun i ↦ κ i ∥ₖ η := by
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply,
    Measure.productBySections_sum_left]

lemma parallelComp_sum_right {ι : Type*} [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : ι → Kernel γ δ) [∀ i, IsSFiniteKernel (η i)] :
    κ ∥ₖ Kernel.sum η = Kernel.sum fun i ↦ κ ∥ₖ η i := by
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply,
    Measure.productBySections_sum_right]

instance [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (κ ∥ₖ η) :=
  ⟨fun x ↦ ⟨by simp [parallelComp_apply_univ]⟩⟩

instance [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ∥ₖ η) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

instance [IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (κ ∥ₖ η) := by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a ↦ ?_⟩⟩
  calc (κ ∥ₖ η) a Set.univ
  _ = κ a.1 Set.univ * η a.2 Set.univ := parallelComp_apply_univ
  _ ≤ κ.bound * η.bound := by
    gcongr
    · exact measure_le_bound κ a.1 Set.univ
    · exact measure_le_bound η a.2 Set.univ

instance [IsSFiniteKernel κ] [IsSFiniteKernel η] : IsSFiniteKernel (κ ∥ₖ η) := by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, parallelComp_sum_left, parallelComp_sum_right]
  infer_instance

end ProbabilityTheory.Kernel

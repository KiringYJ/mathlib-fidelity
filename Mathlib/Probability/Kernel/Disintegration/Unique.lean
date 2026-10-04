/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Uniqueness of conditional kernels

We prove that conditional kernels with values in a countably generated space are unique almost
everywhere: two finite kernels that disintegrate a finite measure `ρ` agree `ρ.fst`-almost
everywhere, and two finite kernels that disintegrate a finite kernel `κ` agree `fst κ a`-almost
everywhere for every `a`. Consequently the finite representatives of the classes
`MeasureTheory.Measure.condKernel ρ` and `ProbabilityTheory.Kernel.condKernel κ` are exactly the
finite conditional kernels.

## Main statements

* `MeasureTheory.Measure.IsCondKernel.ae_eq`: a.e. uniqueness of conditional kernels of a measure.
* `ProbabilityTheory.Kernel.IsCondKernel.ae_eq`: a.e. uniqueness of conditional kernels of a kernel.
* `MeasureTheory.Measure.mem_condKernel_iff`: a finite kernel represents `ρ.condKernel` if and only
  if it disintegrates `ρ`.
* `ProbabilityTheory.Kernel.mem_condKernel_iff`: a finite kernel represents `κ.condKernel` if and
  only if it disintegrates `κ`.
* `ProbabilityTheory.Kernel.comap_mem_condKernel_of_mem`: the restriction to the fiber over `a` of
  a representative of `κ.condKernel` represents the conditional kernel of the measure `κ a`.
-/

public section

open MeasureTheory Set Filter SigmaAlgebra ProbabilityTheory

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

variable {α β Ω : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} [SigmaAlgebra Ω]

namespace MeasureTheory.Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-! ### Uniqueness of conditional kernels of a measure -/

/-- Two s-finite conditional kernels of `ρ` agree `ρ.fst`-almost everywhere on a measurable set.

For finite kernels with values in a countably generated space,
`MeasureTheory.Measure.IsCondKernel.ae_eq` gives the stronger statement that the kernels agree
almost everywhere, not just on a given measurable set. -/
theorem IsCondKernel.ae_eq_apply (η η' : Kernel α Ω) [IsSFiniteKernel η] [IsSFiniteKernel η']
    [ρ.IsCondKernel η] [ρ.IsCondKernel η'] {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, η x s = η' x s := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe η hs) (Kernel.measurable_coe η' hs) (fun t ht _ ↦ ?_)
  have h (ξ : Kernel α Ω) [IsSFiniteKernel ξ] [ρ.IsCondKernel ξ] :
      ∫⁻ x in t, ξ x s ∂ρ.fst = ρ (t ×ˢ s) := by
    conv_rhs => rw [← ρ.disintegrate ξ]
    exact (compProd_apply_prod ht hs).symm
  rw [h η, h η']

/-- Two finite conditional kernels of a finite measure `ρ` with values in a countably generated
space agree `ρ.fst`-almost everywhere. -/
theorem IsCondKernel.ae_eq [SigmaAlgebra.CountablyGenerated Ω] (η η' : Kernel α Ω)
    [IsFiniteKernel η] [IsFiniteKernel η'] [ρ.IsCondKernel η] [ρ.IsCondKernel η'] :
    ∀ᵐ x ∂ρ.fst, η x = η' x :=
  Kernel.ae_eq_of_compProd_eq ((ρ.disintegrate η).trans (ρ.disintegrate η').symm)

/-! ### Representatives of the conditional kernel of a measure -/

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- Every finite conditional kernel of `ρ` represents `ρ.condKernel`. -/
theorem IsCondKernel.mem_condKernel {η : Kernel α Ω} [IsFiniteKernel η] [ρ.IsCondKernel η] :
    η ∈ ρ.condKernel := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  exact Kernel.AEClass.mem_of_eventuallyEq hη₀ (IsCondKernel.ae_eq η₀ η)

/-- An s-finite representative of `ρ.condKernel` disintegrates `ρ`. -/
theorem isCondKernel_of_mem_condKernel {η : Kernel α Ω} [IsSFiniteKernel η]
    (hη : η ∈ ρ.condKernel) :
    ρ.IsCondKernel η := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ.exists_isMarkovKernel_mem_condKernel
  constructor
  rw [Measure.compProd_congr (Kernel.AEClass.eventuallyEq_of_mem hη hη₀), ρ.disintegrate η₀]

/-- A finite kernel represents `ρ.condKernel` if and only if it disintegrates `ρ`. -/
theorem mem_condKernel_iff {η : Kernel α Ω} [IsFiniteKernel η] :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η :=
  ⟨isCondKernel_of_mem_condKernel, fun _ ↦ IsCondKernel.mem_condKernel⟩

/-- A Markov kernel `κ` represents the conditional kernel of `μ ⊗ₘ κ`. -/
lemma mem_condKernel_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω)
    [IsMarkovKernel κ] :
    κ ∈ (μ ⊗ₘ κ).condKernel :=
  mem_condKernel_iff.2 ⟨by rw [Measure.fst_compProd]⟩

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

/-! ### Uniqueness of conditional kernels of a kernel -/

variable {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]

/-- The restriction to the fiber over `a` of a conditional kernel of `κ` is a conditional kernel
of the measure `κ a`. -/
lemma IsCondKernel.isCondKernel_comap (η : Kernel (α × β) Ω) [IsSFiniteKernel η]
    [κ.IsCondKernel η] (a : α) :
    (κ a).IsCondKernel (comap η (fun b ↦ (a, b)) measurable_prodMk_left) := by
  constructor
  ext s hs
  conv_rhs => rw [← κ.disintegrate η]
  rw [Measure.compProd_apply hs, compProd_apply hs, fst_apply]
  rfl

/-- Two finite conditional kernels of a finite kernel `κ` with values in a countably generated space
agree `fst κ a`-almost everywhere for every `a`. -/
theorem IsCondKernel.ae_eq [SigmaAlgebra.CountablyGenerated Ω] (η η' : Kernel (α × β) Ω)
    [IsFiniteKernel η] [IsFiniteKernel η'] [κ.IsCondKernel η] [κ.IsCondKernel η'] (a : α) :
    ∀ᵐ b ∂(fst κ a), η (a, b) = η' (a, b) := by
  have := IsCondKernel.isCondKernel_comap (κ := κ) η a
  have := IsCondKernel.isCondKernel_comap (κ := κ) η' a
  have h := Measure.IsCondKernel.ae_eq (ρ := κ a) (comap η (fun b ↦ (a, b)) measurable_prodMk_left)
    (comap η' (fun b ↦ (a, b)) measurable_prodMk_left)
  rw [fst_apply]
  filter_upwards [h] with b hb
  simpa [comap_apply] using hb

variable [StandardBorelSpace Ω]

/-- The restriction to the fiber over `a` of a finite conditional kernel of `κ` represents the
conditional kernel of the measure `κ a`. -/
lemma IsCondKernel.comap_mem_condKernel [Nonempty Ω] {η : Kernel (α × β) Ω} [IsFiniteKernel η]
    [κ.IsCondKernel η] (a : α) :
    comap η (fun b ↦ (a, b)) measurable_prodMk_left ∈ (κ a).condKernel :=
  have := IsCondKernel.isCondKernel_comap (κ := κ) η a
  Measure.IsCondKernel.mem_condKernel

/-! ### Representatives of the conditional kernel of a kernel -/

variable [Nonempty Ω] [CountableOrCountablyGenerated α β]

/-- Every finite conditional kernel of `κ` represents `condKernel κ`. -/
theorem IsCondKernel.mem_condKernel {η : Kernel (α × β) Ω} [IsFiniteKernel η]
    [κ.IsCondKernel η] :
    η ∈ condKernel κ := by
  obtain ⟨η₀, _, _, hη₀⟩ := exists_isMarkovKernel_mem_condKernel κ
  exact AEClass.mem_of_eventuallyEq hη₀
    (eventuallyEq_fiberwiseAE_iff.2 (IsCondKernel.ae_eq η₀ η))

/-- An s-finite representative of `condKernel κ` disintegrates `κ`. -/
theorem isCondKernel_of_mem_condKernel {η : Kernel (α × β) Ω} [IsSFiniteKernel η]
    (hη : η ∈ condKernel κ) :
    κ.IsCondKernel η := by
  obtain ⟨η₀, _, _, hη₀⟩ := exists_isMarkovKernel_mem_condKernel κ
  constructor
  rw [compProd_congr (eventuallyEq_fiberwiseAE_iff.1 (AEClass.eventuallyEq_of_mem hη hη₀)),
    κ.disintegrate η₀]

/-- A finite kernel represents `condKernel κ` if and only if it disintegrates `κ`. -/
theorem mem_condKernel_iff {η : Kernel (α × β) Ω} [IsFiniteKernel η] :
    η ∈ condKernel κ ↔ κ.IsCondKernel η :=
  ⟨isCondKernel_of_mem_condKernel, fun _ ↦ IsCondKernel.mem_condKernel⟩

/-- The restriction to the fiber over `a` of a representative of `condKernel κ` represents the
conditional kernel of the measure `κ a`. -/
lemma comap_mem_condKernel_of_mem {η : Kernel (α × β) Ω} (hη : η ∈ condKernel κ) (a : α) :
    comap η (fun b ↦ (a, b)) measurable_prodMk_left ∈ (κ a).condKernel := by
  obtain ⟨η₀, _, _, hη₀⟩ := exists_isMarkovKernel_mem_condKernel κ
  refine AEClass.mem_of_eventuallyEq (IsCondKernel.comap_mem_condKernel (κ := κ) (η := η₀) a) ?_
  have h := eventuallyEq_fiberwiseAE_iff.1 (AEClass.eventuallyEq_of_mem hη₀ hη) a
  rw [fst_apply] at h
  filter_upwards [h] with b hb
  simpa [comap_apply] using hb

end ProbabilityTheory.Kernel

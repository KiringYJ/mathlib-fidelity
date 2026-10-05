import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Kernel products on their exact domains

These tests check that the composition-product `μ ⊗ₘ κ` of a measure and a kernel, the
composition-product `κ ⊗ₖ η` and the parallel composition `κ ∥ₖ η` of kernels, and the product
`κ ×ₖ η` require their domains `μ.HasCompProd κ`, `κ.HasCompProd η`, `κ.HasParallelComp η` and
`κ.HasCompProd (prodMkRight β η)`, and that the former fallback lemmas, which made each of them zero
outside s-finite inputs, are gone. Instance search finds the domains for s-finite kernels; for the
measure composition-product it needs no condition on the measure, and it also covers zero kernels
and measures and Dirac measures on spaces with measurable singletons. Outside s-finite inputs, the
section integrals give the values that the former definitions replaced by zero, and the
almost-everywhere lemmas and several absolute-continuity and mutual-singularity lemmas hold on the
domains. The instances that make the products s-finite need s-finite inputs. A conditional kernel
carries the domain of its composition-product, and statements that held only through the fallback,
such as the s-finiteness of every conditional kernel of a nonzero measure, are removed. A
deterministic kernel is s-finite, by a proof from its defining equation.
-/

open MeasureTheory Measure Set
open ProbabilityTheory (Kernel IsSFiniteKernel IsMarkovKernel IsDeterministic)
open scoped ProbabilityTheory ENNReal

noncomputable section

variable {α β γ δ : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ] [SigmaAlgebra δ]

/-! ### The fallback lemmas are gone -/

/-- error: Unknown constant `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left

/-- error: Unknown constant `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right

/-- error: Unknown constant `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left

/-- error: Unknown constant `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right

/-- error: Unknown constant `ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_left` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_left

/-- error: Unknown constant `ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_right` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_right

/-- error: Unknown constant `MeasureTheory.Measure.compProd_of_not_sfinite` -/
#guard_msgs in
#check MeasureTheory.Measure.compProd_of_not_sfinite

/-- error: Unknown constant `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel` -/
#guard_msgs in
#check MeasureTheory.Measure.compProd_of_not_isSFiniteKernel

/-- error: Unknown constant `MeasureTheory.Measure.IsCondKernel.isSFiniteKernel` -/
#guard_msgs in
#check MeasureTheory.Measure.IsCondKernel.isSFiniteKernel

/-! ### The domains are enforced -/

/--
error: failed to synthesize instance of type class
  κ.HasCompProd η

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ) := κ ⊗ₖ η

-- One s-finite kernel is not enough.
/--
error: failed to synthesize instance of type class
  κ.HasCompProd η

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) : Kernel α (β × γ) := κ ⊗ₖ η

/--
error: failed to synthesize instance of type class
  κ.HasCompProd η

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel η] : Kernel α (β × γ) := κ ⊗ₖ η

/--
error: failed to synthesize instance of type class
  κ.HasParallelComp η

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) : Kernel (α × γ) (β × δ) := κ ∥ₖ η

/--
error: failed to synthesize instance of type class
  κ.HasCompProd (Kernel.prodMkRight β η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) : Kernel α (β × γ) := κ ×ₖ η

-- An s-finite measure does not supply the domain of `μ ⊗ₘ κ`.
/--
error: failed to synthesize instance of type class
  μ.HasCompProd κ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure α) [SFinite μ] (κ : Kernel α β) : Measure (α × β) := μ ⊗ₘ κ

/-! ### The s-finiteness of a product needs s-finite inputs -/

/--
error: failed to synthesize instance of type class
  IsSFiniteKernel (κ ⊗ₖ η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [κ.HasCompProd η] :
    IsSFiniteKernel (κ ⊗ₖ η) := inferInstance

/--
error: failed to synthesize instance of type class
  IsSFiniteKernel (κ ∥ₖ η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [κ.HasParallelComp η] :
    IsSFiniteKernel (κ ∥ₖ η) := inferInstance

/--
error: failed to synthesize instance of type class
  IsSFiniteKernel (κ ×ₖ η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [κ.HasCompProd (Kernel.prodMkRight β η)] :
    IsSFiniteKernel (κ ×ₖ η) := inferInstance

-- `count ⊗ₘ Kernel.const ℝ (dirac 0)` is not s-finite
-- (`Counterexample.KernelCompProd.not_sFinite_count_compProd_const_dirac`).
/--
error: failed to synthesize instance of type class
  SFinite (μ ⊗ₘ κ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure α) (κ : Kernel α β) [IsSFiniteKernel κ] : SFinite (μ ⊗ₘ κ) := inferInstance

/-! ### Routine evidence is found -/

example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] :
    Kernel α (β × γ) := κ ⊗ₖ η

example (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] :
    Kernel (α × γ) (β × δ) := κ ∥ₖ η

example (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsMarkovKernel η] :
    IsMarkovKernel (κ ×ₖ η) := inferInstance

-- The measure needs no condition when the kernel is s-finite.
example (μ : Measure α) (κ : Kernel α β) [IsSFiniteKernel κ] : Measure (α × β) := μ ⊗ₘ κ

-- Zero kernels and measures.
example (η : Kernel (α × β) γ) : (0 : Kernel α β) ⊗ₖ η = 0 := by simp

example (κ : Kernel α β) : κ ⊗ₖ (0 : Kernel (α × β) γ) = 0 := by simp

example (η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0 := by simp

example (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0 := by simp

example (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp

-- A Dirac measure on a space with measurable singletons.
example [MeasurableSingletonClass α] (x : α) (κ : Kernel α β) : Measure (α × β) :=
  Measure.dirac x ⊗ₘ κ

-- Almost everywhere measurable section measures.
example (μ : Measure α) (κ : Kernel α β)
    (h : ∀ ⦃s : Set (α × β)⦄, MeasurableSet s → AEMeasurable (fun a ↦ κ a (Prod.mk a ⁻¹' s)) μ) :
    μ.HasCompProd κ :=
  .of_aemeasurable h

/-! ### The section integrals on the exact domain -/

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ :=
  compProd_apply hs

example (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α) {s : Set (β × γ)}
    (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a :=
  Kernel.compProd_apply hs κ η a

example (κ : Kernel α β) (η : Kernel γ δ) [κ.HasParallelComp η] (x : α × γ) {s : Set (β × δ)}
    (hs : MeasurableSet s) :
    (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1 :=
  Kernel.parallelComp_apply' hs

-- Counting measure on `ℝ` is not s-finite, but its composition-product with `dirac 0` is the
-- image of counting measure under `a ↦ (a, 0)`, not the former zero value.
example :
    ((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ))) ({1} ×ˢ univ) = 1 := by
  rw [compProd_apply_prod (measurableSet_singleton _) .univ]
  simp

-- A Dirac measure composed with counting measure as a constant kernel.
example :
    (Measure.dirac (0 : ℝ) ⊗ₘ Kernel.const ℝ (Measure.count : Measure ℝ)) ({0} ×ˢ univ) = ∞ := by
  rw [compProd_apply_prod (measurableSet_singleton _) .univ]
  simp

/-! ### Proof independence and rewriting -/

example (κ : Kernel α β) (η : Kernel (α × β) γ) (h₁ h₂ : κ.HasCompProd η) :
    @Kernel.compProd _ _ _ _ _ _ κ η h₁ = @Kernel.compProd _ _ _ _ _ _ κ η h₂ := rfl

example (μ ν : Measure α) (κ : Kernel α β) [IsSFiniteKernel κ] (h : μ = ν) :
    μ ⊗ₘ κ = ν ⊗ₘ κ := by
  rw [h]

example (μ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [μ.HasCompProd η]
    (h : κ =ᵐ[μ] η) :
    μ ⊗ₘ κ = μ ⊗ₘ η :=
  compProd_congr h

/-! ### Almost everywhere statements on the exact domain -/

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) :=
  ae_ae_of_ae_compProd h

example (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α) {p : β × γ → Prop}
    (h : ∀ᵐ x ∂(κ ⊗ₖ η) a, p x) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  Kernel.ae_ae_of_ae_compProd h

example (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd κ] (h : μ ≪ ν) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ :=
  h.compProd_left κ

example (μ ν : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd η] (h : μ ≪ ν)
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  h.compProd hκη

example (μ ν ξ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ a ∂ξ, κ a ⟂ₘ η a :=
  mutuallySingular_of_mutuallySingular_compProd h hμ hν

example (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd κ]
    [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν :=
  absolutelyContinuous_compProd_left_iff

example (μ ν : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [μ.HasCompProd η]
    [ν.HasCompProd η] (hμν : μ ≪ ν) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  hμν.compProd_of_compProd hκη

example (μ ν : Measure α) [SFinite μ] [SigmaFinite ν] (κ : Kernel α β) [μ.HasCompProd κ]
    [ν.HasCompProd κ] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν :=
  mutuallySingular_compProd_left_iff

/-! ### Conditional kernels and deterministic kernels carry the domain -/

example (ρ : Measure (α × β)) (κ : Kernel α β) [ρ.IsCondKernel κ] : ρ.fst.HasCompProd κ :=
  inferInstance

example (ρ : Measure (α × β)) (κ : Kernel α β) [ρ.IsCondKernel κ] : ρ.fst ⊗ₘ κ = ρ :=
  ρ.disintegrate κ

example (κ : Kernel α β) [IsDeterministic κ] : κ.HasParallelComp κ := inferInstance

-- A deterministic kernel is s-finite: each of its values is a zero-one measure, possibly zero, or
-- `∞` times a zero-one probability measure.
example (κ : Kernel α β) [IsDeterministic κ] : IsSFiniteKernel κ := inferInstance

example (κ : Kernel α β) [IsDeterministic κ] (a : α) {s t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    κ a (s ∩ t) = κ a s * κ a t :=
  Kernel.IsDeterministic.measure_inter_eq_mul κ a hs ht

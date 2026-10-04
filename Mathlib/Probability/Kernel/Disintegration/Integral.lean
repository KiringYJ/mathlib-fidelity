/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Lebesgue and Bochner integrals of conditional kernels

Integrals against a conditional kernel: an s-finite kernel `η` that disintegrates a kernel `κ`
(`κ.IsCondKernel η`) or a measure `ρ` (`ρ.IsCondKernel η`). The statements hold for every such
kernel, in particular for every s-finite representative of `ProbabilityTheory.Kernel.condKernel κ`
or `MeasureTheory.Measure.condKernel ρ`, which are classes of kernels.

## Main statements

* `ProbabilityTheory.setIntegral_condKernel`: the integral
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)` is equal to
  `∫ x in s ×ˢ t, f x ∂(κ a)`.
* `MeasureTheory.Measure.setIntegral_condKernel`:
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(η b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ`

Corresponding statements for the Lebesgue integral and/or without the sets `s` and `t` are also
provided.
-/

public section

open MeasureTheory ProbabilityTheory SigmaAlgebra

open scoped ENNReal

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} [SigmaAlgebra Ω]

section Lintegral

variable {κ : Kernel α (β × Ω)} [IsFiniteKernel κ] {η : Kernel (α × β) Ω} [IsSFiniteKernel η]
  [κ.IsCondKernel η] {f : β × Ω → ℝ≥0∞}

lemma lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, η (a, x) (Prod.mk x ⁻¹' s) ∂(Kernel.fst κ a) = κ a s := by
  conv_rhs => rw [← κ.disintegrate η]
  simp_rw [Kernel.compProd_apply hs]

lemma setLIntegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, η (a, b) t ∂(Kernel.fst κ a) = κ a (s ×ˢ t) := by
  have : κ a (s ×ˢ t) = (Kernel.fst κ ⊗ₖ η) a (s ×ˢ t) := by
    congr; exact (κ.disintegrate η).symm
  simpa [this] using (Kernel.compProd_apply_prod hs ht).symm

lemma lintegral_condKernel (hf : Measurable f) (a : α) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a) = ∫⁻ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate η]
  rw [Kernel.lintegral_compProd _ _ _ hf]

lemma setLIntegral_condKernel (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate η]
  rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]

lemma setLIntegral_condKernel_univ_right (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel (η := η) hf a hs MeasurableSet.univ]
  simp_rw [Measure.restrict_univ]

lemma setLIntegral_condKernel_univ_left (hf : Measurable f) (a : α) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel (η := η) hf a MeasurableSet.univ ht]
  simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable {κ : Kernel α (β × Ω)} [IsFiniteKernel κ] {η : Kernel (α × β) Ω} [IsSFiniteKernel η]
  [κ.IsCondKernel η] {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel (a : α)
    (hf : AEStronglyMeasurable f (κ a)) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂(η (a, x)))
      (Kernel.fst κ a) := by
  rw [← κ.disintegrate η] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

lemma integral_condKernel (a : α) (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a) = ∫ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate η]
  rw [← κ.disintegrate η] at hf
  rw [integral_compProd hf]

lemma setIntegral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate η]
  rw [← κ.disintegrate η] at hf
  rw [setIntegral_compProd hs ht hf]

lemma setIntegral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setIntegral_condKernel (η := η) a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

lemma setIntegral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(η (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setIntegral_condKernel (η := η) a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {β Ω : Type*} {mβ : SigmaAlgebra β} [SigmaAlgebra Ω]

section Lintegral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ] {η : Kernel β Ω} [IsSFiniteKernel η]
  [ρ.IsCondKernel η] {f : β × Ω → ℝ≥0∞}

lemma lintegral_condKernel_mem {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, η x {y | (x, y) ∈ s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [← ρ.disintegrate η]
  simp_rw [compProd_apply hs]
  rfl

lemma setLIntegral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b in s, η b t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) = (ρ.fst ⊗ₘ η) (s ×ˢ t) := by
    congr; exact (ρ.disintegrate η).symm
  simpa [this] using (compProd_apply_prod hs ht).symm

lemma lintegral_condKernel (hf : Measurable f) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(η b) ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate η]
  rw [lintegral_compProd hf]

lemma setLIntegral_condKernel (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(η b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate η]
  rw [setLIntegral_compProd hf hs ht]

lemma setLIntegral_condKernel_univ_right (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(η b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setLIntegral_condKernel (η := η) hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

lemma setLIntegral_condKernel_univ_left (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(η b) ∂ρ.fst
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setLIntegral_condKernel (η := η) hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ] {η : Kernel β Ω} [IsSFiniteKernel η]
  [ρ.IsCondKernel η] {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel
    (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂η x) ρ.fst := by
  rw [← ρ.disintegrate η] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

lemma integral_condKernel (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂(η b) ∂ρ.fst = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate η]
  rw [← ρ.disintegrate η] at hf
  rw [integral_compProd hf]

lemma setIntegral_condKernel {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(η b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate η]
  rw [← ρ.disintegrate η] at hf
  rw [setIntegral_compProd hs ht hf]

lemma setIntegral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) ρ) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(η b) ∂ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setIntegral_condKernel (η := η) hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

lemma setIntegral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) ρ) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(η b) ∂ρ.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setIntegral_condKernel (η := η) MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end MeasureTheory.Measure

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/

open ProbabilityTheory

variable {α Ω E F : Type*} {mα : SigmaAlgebra α} [SigmaAlgebra Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {η : Kernel α Ω}
  [IsSFiniteKernel η] [ρ.IsCondKernel η]

theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω → F}
    (hf : AEStronglyMeasurable f ρ) :
    (∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (η a)) ∧
      Integrable (fun a ↦ ∫ ω, ‖f (a, ω)‖ ∂η a) ρ.fst ↔ Integrable f ρ := by
  rw [← ρ.disintegrate η] at hf
  conv_rhs => rw [← ρ.disintegrate η]
  rw [Measure.integrable_compProd_iff hf]

theorem Integrable.condKernel_ae {f : α × Ω → F} (hf_int : Integrable f ρ) :
    ∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (η a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff (η := η)] at hf_int
  exact hf_int.1

theorem Integrable.integral_norm_condKernel {f : α × Ω → F} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂η x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff (η := η)] at hf_int
  exact hf_int.2

theorem Integrable.norm_integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ‖∫ y, f (x, y) ∂η x‖) ρ.fst := by
  refine (hf_int.integral_norm_condKernel (η := η)).mono
    (hf_int.1.integral_condKernel (η := η)).norm ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y ↦ norm_nonneg _)

theorem Integrable.integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂η x) ρ.fst :=
  (integrable_norm_iff (hf_int.1.integral_condKernel (η := η))).mp
    (hf_int.norm_integral_condKernel (η := η))

end MeasureTheory

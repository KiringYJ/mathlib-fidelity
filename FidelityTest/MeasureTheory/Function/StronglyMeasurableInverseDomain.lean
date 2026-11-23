/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

open MeasureTheory

-- Inversion is strongly measurable on its actual nonzero domain.
example : StronglyMeasurable (fun x : {r : ℝ // r ≠ 0} =>
    have hx := x.property
    (x : ℝ)⁻¹) := by
  exact (continuous_subtype_val.stronglyMeasurable).fun_inv₀

-- A zero numerator imposes no extra restriction on the quotient domain.
example : StronglyMeasurable (fun x : {r : ℝ // r ≠ 0} =>
    have hx := x.property
    (0 : ℝ) / (x : ℝ)) := by
  exact stronglyMeasurable_const.div₀ continuous_subtype_val.stronglyMeasurable

-- The scalar-cancellation theorem still needs only almost-everywhere nonvanishing.
example {α E : Type*} [SigmaAlgebra α] [TopologicalSpace E] [MulAction ℝ E]
    [ContinuousSMul ℝ E] {μ : Measure α} {c : α → ℝ} {f : α → E}
    (hc : AEStronglyMeasurable c μ) (hc0 : ∀ᵐ x ∂μ, c x ≠ 0) :
    AEStronglyMeasurable (fun x => c x • f x) μ ↔ AEStronglyMeasurable f μ :=
  aestronglyMeasurable_smul_iff₀ hc hc0

-- The representative remains measurable for m even when the measure uses an unrelated m₀.
example {α : Type*} {m m₀ : SigmaAlgebra α} {μ : Measure[m₀] α} {f : α → ℝ}
    (hf : AEStronglyMeasurable[m] f μ) (h0 : ∀ᵐ x ∂μ, IsUnit (f x)) :
    ∃ g : α → ℝ, StronglyMeasurable[m] g ∧ (∀ x, IsUnit (g x)) ∧ f =ᵐ[μ] g :=
  hf.exists_stronglyMeasurable_isUnit h0

-- Ambient inversion is rejected at its missing mathematical domain obligation.
/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
x : ℝ
⊢ IsUnit x
-/
#guard_msgs in
example : StronglyMeasurable (fun x : ℝ => x⁻¹) := by
  fun_prop

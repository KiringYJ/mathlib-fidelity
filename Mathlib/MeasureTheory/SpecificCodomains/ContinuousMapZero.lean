/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap

/-!
# Specific results about `ContinuousMapZero`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)₀`-valued function, where `Y` is a compact topological space with a distinguished `0`,
and `E` is a normed group.

The structure of this file is largely similar to that of
`Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`, which contains a more detailed
module docstring. The difference is that a bundled representative `F : X → C(Y, E)₀` of a family
of functions `f : X → Y → E` automatically satisfies `F x 0 = 0`, so that no assumption on the
values `f x 0` is needed.

-/

public section

open MeasureTheory

namespace ContinuousMapZero

variable {X Y : Type*} [SigmaAlgebra X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)₀`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] [Zero Y] (f : X → C(Y, E)₀) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  have bound_nonneg : 0 ≤ᵐ[μ] bound := by
    filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x 0)
  refine .mono' bound_int ?_
  filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
  exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_of_bound` for a bundled representative `F` of
a family of functions `f : X → Y → E`: the bound is only required for `f`. -/
lemma hasFiniteIntegral_of_ae_coe_eq_of_bound [CompactSpace Y] [Zero Y] {f : X → Y → E}
    {F : X → C(Y, E)₀} (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral F μ := by
  refine hasFiniteIntegral_of_bound F bound bound_int ?_
  filter_upwards [hF, bound_ge] with x hFx bound_ge_x y
  rw [hFx]
  exact bound_ge_x y

/-- A variant of `ContinuousMapZero.hasFiniteIntegral_of_ae_coe_eq_of_bound` for a family of
functions which are continuous on a compact set. -/
lemma hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound {s : Set Y} [CompactSpace s] [Zero s]
    {f : X → Y → E} {F : X → C(s, E)₀} (hF : ∀ᵐ x ∂μ, ⇑(F x) = s.domRestrict (f x))
    (bound : X → ℝ) (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral F μ := by
  refine hasFiniteIntegral_of_ae_coe_eq_of_bound hF bound bound_int ?_
  filter_upwards [bound_ge] with x bound_ge_x y
  exact bound_ge_x y.1 y.2

/-- A bundled representative `F` of a jointly continuous family of functions `f : X → Y → E` is
almost everywhere strongly measurable. -/
lemma aeStronglyMeasurable_of_uncurry [CompactSpace Y] [Zero Y] [TopologicalSpace X]
    [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(Y, E))]
    {f : X → Y → E} {F : X → C(Y, E)₀} (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x)
    (f_cont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable F μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  exact ContinuousMap.aeStronglyMeasurable_of_uncurry
    (hF.mono fun x hx ↦ (ContinuousMap.coe_coe (F x)).trans hx) f_cont

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `s ×ˢ univ`, is almost everywhere strongly measurable with respect to `μ.restrict s`
for a measurable set `s`. -/
lemma aeStronglyMeasurable_restrict_of_uncurry [CompactSpace Y] [Zero Y] {s : Set X}
    [TopologicalSpace X] [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) {f : X → Y → E} {F : X → C(Y, E)₀}
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = f x)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    AEStronglyMeasurable F (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  exact ContinuousMap.aeStronglyMeasurable_restrict_of_uncurry hs
    (hF.mono fun x hx ↦ (ContinuousMap.coe_coe (F x)).trans hx) f_cont

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `univ ×ˢ t` for a compact set `t`, is almost everywhere strongly measurable. -/
lemma aeStronglyMeasurable_domRestrict_of_uncurry {t : Set Y} [CompactSpace t] [Zero t]
    [TopologicalSpace X] [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(t, E))]
    {f : X → Y → E} {F : X → C(t, E)₀} (hF : ∀ᵐ x ∂μ, ⇑(F x) = t.domRestrict (f x))
    (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    AEStronglyMeasurable F μ := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  exact ContinuousMap.aeStronglyMeasurable_domRestrict_of_uncurry
    (hF.mono fun x hx ↦ (ContinuousMap.coe_coe (F x)).trans hx) f_cont

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `s ×ˢ t` for a compact set `t`, is almost everywhere strongly measurable with respect
to `μ.restrict s` for a measurable set `s`. -/
lemma aeStronglyMeasurable_restrict_domRestrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [Zero t] [TopologicalSpace X] [OpensSigmaAlgebra X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) {f : X → Y → E} {F : X → C(t, E)₀}
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = t.domRestrict (f x))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    AEStronglyMeasurable F (μ.restrict s) := by
  rw [← ContinuousMapZero.isEmbedding_toContinuousMap.aestronglyMeasurable_comp_iff]
  exact ContinuousMap.aeStronglyMeasurable_restrict_domRestrict_of_uncurry hs
    (hF.mono fun x hx ↦ (ContinuousMap.coe_coe (F x)).trans hx) f_cont

end ContinuousMapZero

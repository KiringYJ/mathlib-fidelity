/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Specific results about `ContinuousMap`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)`-valued function, where `Y` is a compact topological space and `E` is a normed group.

These are all elementary from a mathematical point of view, but they require a bit of care in order
to be conveniently usable. In particular, to accommodate the need of families `f : X → Y → E` such
that `f x` is only continuous for *almost every* `x`, we give a variety of results about the
integrability and measurability of a bundled representative `F : X → C(Y, E)` of `f`, that is a
function such that `⇑(F x) = f x` for almost every `x`. Apart from the representative itself, the
assumptions of these results only mention `f` (so that users don't have to convert between `f` and
`F` by hand).

## Main results

* `hasFiniteIntegral_of_bound`: given `f : X → C(Y, E)`, the natural way to show
  `HasFiniteIntegral f` is to give a `bound : X → ℝ`, which itself has finite integral, and such
  that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
* `hasFiniteIntegral_of_ae_coe_eq_of_bound` is the analog of the above for a representative: given
  `f : X → Y → E`, a bundled representative `F : X → C(Y, E)` of `f`, as well as a bound for `f` as
  above, we prove `HasFiniteIntegral F μ`. Note that the bound is only required for `f`.
* `aeStronglyMeasurable_of_uncurry`: if now `X` is a topological space with the Borel σ-algebra,
  and `f : X → Y → E` is continuous on `X × Y`, then every bundled representative `F` of `f` is
  `AEStronglyMeasurable`. Note that, since every `f x` is continuous in that case, one can choose
  the representative `F x = ⟨f x, _⟩`, which is even a continuous function of `x`, and any other
  representative agrees with it almost everywhere. Nevertheless, this form is the most convenient
  when the representative is obtained from `ContinuousMap.exists_eventually_coe_eq_iff`, as we
  explain below.

## Implementation Note

A family of bare functions `f : X → Y → E` such that `f x` is continuous for almost every `x` does
not define a `C(Y, E)`-valued function: for the exceptional `x`, `f x` is not an element of
`C(Y, E)`, and there is no canonical element to replace it with. What it defines is an almost
everywhere class of `C(Y, E)`-valued functions. We do not replace `f x` by a fallback value where it
is not continuous. Instead, to integrate `f` in `C(Y, E)`, one works with a *bundled
representative* `F : X → C(Y, E)` of `f`, that is a function such that `∀ᵐ x ∂μ, ⇑(F x) = f x`:

- Such a representative exists if and only if `∀ᵐ x ∂μ, Continuous (f x)`, see
  `ContinuousMap.exists_eventually_coe_eq_iff`. Its values on the null set where `f x` is not
  continuous are arbitrary, and appear in no statement.
- Two representatives of `f` are almost everywhere equal, see
  `ContinuousMap.eventuallyEq_of_eventually_coe_eq`. Hence, by `Integrable.congr`,
  `integral_congr_ae` and `AEStronglyMeasurable.congr`, the integrability of `F`, the value of
  `∫ x, F x ∂μ` and the almost everywhere strong measurability of `F` only depend on `f`. For an
  integrable `F`, `ContinuousMap.integral_apply` gives `(∫ x, F x ∂μ) y = ∫ x, F x y ∂μ`, which is
  `∫ x, f x y ∂μ` since `F x y = f x y` almost everywhere.
- Almost everywhere continuity of `f` does not by itself give measurability or integrability of
  `F`. These are separate assumptions (`Integrable F μ`), or they are deduced from the joint
  continuity of `f` and a bound, as in the results above.

-/

public section

open MeasureTheory

namespace ContinuousMap

variable {X Y : Type*} [SigmaAlgebra X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] (f : X → C(Y, E)) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  rcases isEmpty_or_nonempty Y with (h | h)
  · simp
  · have bound_nonneg : 0 ≤ᵐ[μ] bound := by
      filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x h.some)
    refine .mono' bound_int ?_
    filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
    exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_bound` for a bundled representative `F` of a
family of functions `f : X → Y → E`: the bound is only required for `f`. -/
lemma hasFiniteIntegral_of_ae_coe_eq_of_bound [CompactSpace Y] {f : X → Y → E}
    {F : X → C(Y, E)} (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral F μ := by
  refine hasFiniteIntegral_of_bound F bound bound_int ?_
  filter_upwards [hF, bound_ge] with x hFx bound_ge_x y
  rw [hFx]
  exact bound_ge_x y

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_ae_coe_eq_of_bound` for a family of
functions which are continuous on a compact set. -/
lemma hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound {s : Set Y} [CompactSpace s]
    {f : X → Y → E} {F : X → C(s, E)} (hF : ∀ᵐ x ∂μ, ⇑(F x) = s.domRestrict (f x))
    (bound : X → ℝ) (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral F μ := by
  refine hasFiniteIntegral_of_ae_coe_eq_of_bound hF bound bound_int ?_
  filter_upwards [bound_ge] with x bound_ge_x y
  exact bound_ge_x y.1 y.2

/-- A bundled representative `F` of a jointly continuous family of functions `f : X → Y → E` is
almost everywhere strongly measurable. -/
lemma aeStronglyMeasurable_of_uncurry [CompactSpace Y] [TopologicalSpace X]
    [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(Y, E))]
    {f : X → Y → E} {F : X → C(Y, E)} (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x)
    (f_cont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable F μ := by
  obtain ⟨G, hG⟩ : ∃ G : X → C(Y, E), ∀ x, ⇑(G x) = f x :=
    ⟨fun x ↦ ⟨f x, f_cont.comp (Continuous.prodMk_right x)⟩, fun x ↦ rfl⟩
  refine (continuous_of_coe_eq_of_continuous_uncurry G hG f_cont).aestronglyMeasurable.congr ?_
  filter_upwards [hF] with x hx
  exact DFunLike.ext' ((hG x).trans hx.symm)

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `s ×ˢ univ`, is almost everywhere strongly measurable with respect to `μ.restrict s`
for a measurable set `s`. -/
lemma aeStronglyMeasurable_restrict_of_uncurry [CompactSpace Y] {s : Set X}
    [TopologicalSpace X] [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) {f : X → Y → E} {F : X → C(Y, E)}
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = f x)
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    AEStronglyMeasurable F (μ.restrict s) := by
  have hf_cont (x : X) (hx : x ∈ s) : Continuous (f x) :=
    f_cont.comp_continuous (Continuous.prodMk_right x) fun _ ↦ ⟨hx, trivial⟩
  obtain ⟨G, hG⟩ := exists_eventually_coe_eq_iff.mpr
    (Filter.eventually_principal.mpr hf_cont : ∀ᶠ x in Filter.principal s, Continuous (f x))
  have hG' : ∀ x ∈ s, ⇑(G x) = f x := Filter.eventually_principal.mp hG
  have hG_meas : AEStronglyMeasurable G (μ.restrict s) :=
    (continuousOn_of_coe_eq_of_continuousOn_uncurry G hG' f_cont).aestronglyMeasurable hs
  refine hG_meas.congr ?_
  filter_upwards [hF, ae_restrict_mem hs] with x hx hxs
  exact DFunLike.ext' ((hG' x hxs).trans hx.symm)

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `univ ×ˢ t` for a compact set `t`, is almost everywhere strongly measurable. -/
lemma aeStronglyMeasurable_domRestrict_of_uncurry {t : Set Y} [CompactSpace t]
    [TopologicalSpace X] [OpensSigmaAlgebra X] [SecondCountableTopologyEither X (C(t, E))]
    {f : X → Y → E} {F : X → C(t, E)} (hF : ∀ᵐ x ∂μ, ⇑(F x) = t.domRestrict (f x))
    (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    AEStronglyMeasurable F μ := by
  have f_cont' : Continuous (Function.uncurry fun x (y : t) ↦ f x y) :=
    f_cont.comp_continuous (.prodMap continuous_id continuous_subtype_val)
      fun xz ↦ ⟨trivial, xz.2.2⟩
  exact aeStronglyMeasurable_of_uncurry (f := fun x (y : t) ↦ f x y) hF f_cont'

open Set in
/-- A bundled representative `F` of a family of functions `f : X → Y → E`, which is jointly
continuous on `s ×ˢ t` for a compact set `t`, is almost everywhere strongly measurable with respect
to `μ.restrict s` for a measurable set `s`. -/
lemma aeStronglyMeasurable_restrict_domRestrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [TopologicalSpace X] [OpensSigmaAlgebra X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) {f : X → Y → E} {F : X → C(t, E)}
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = t.domRestrict (f x))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    AEStronglyMeasurable F (μ.restrict s) := by
  have hproj : ContinuousOn (Prod.map id (Subtype.val : t → Y)) (s ×ˢ (univ : Set t)) :=
    (continuous_id.prodMap continuous_subtype_val).continuousOn
  have hmaps : MapsTo (Prod.map id (Subtype.val : t → Y)) (s ×ˢ (univ : Set t)) (s ×ˢ t) :=
    fun xz hxz ↦ ⟨hxz.1, xz.2.2⟩
  exact aeStronglyMeasurable_restrict_of_uncurry hs (f := fun x (y : t) ↦ f x y) hF
    (f_cont.comp hproj hmaps)

end ContinuousMap

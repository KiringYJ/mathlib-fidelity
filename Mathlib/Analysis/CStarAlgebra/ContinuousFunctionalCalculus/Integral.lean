/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMapZero
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_setIntegral`, `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrableOn_cfc`, `integrableOn_cfcₙ`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## Implementation Notes

The lemmas mentioned above are stated under much stricter hypotheses than necessary
(typically, simultaneous continuity of `f` in the parameter and the spectrum element).
They all come with primed version which only assume what's needed. Instead of continuity, the primed
versions take a bundled representative `F : X → C(spectrum 𝕜 a, 𝕜)` of the family of restrictions
of the functions `f x` to the spectrum, that is
`∀ᵐ x ∂μ, ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x)`, together with the integrability of `F`.
The existence of such an `F` is equivalent to the almost everywhere continuity of `f x` on the
spectrum (`ContinuousMap.exists_eventually_coe_eq_iff`), and the statements do not depend on the
choice of `F`. The primed versions may be used together with the API developed in
`Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`, which also explains why no fallback value
is used for the functions which are not continuous.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

public section

open MeasureTheory
open scoped ContinuousMapZero

section unital

open ContinuousMap

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [SigmaAlgebra X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

lemma cfcL_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcL_integrable (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

lemma cfcHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

/-- An integrability criterion for the continuous functional calculus, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the spectrum of `a`: the
hypothesis `hF` implies that `f x` is continuous on the spectrum for almost every `x`, and the
integrability of `F` is assumed.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfc`. -/
lemma integrable_cfc' (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(spectrum 𝕜 a, 𝕜))
    (hF : ∀ᵐ x ∂μ, ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x))
    (hF_int : Integrable F μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine (cfcL_integrable a F hF_int ha).congr ?_
  filter_upwards [hF] with x hFx
  exact (cfc_eq_cfcL_of_coe_eq (f x) a hFx ha).symm

/-- An integrability criterion for the continuous functional calculus, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the spectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfc`. -/
lemma integrableOn_cfc' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(spectrum 𝕜 a, 𝕜))
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x))
    (hF_int : IntegrableOn F s μ) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  exact integrable_cfc' f a F hF hF_int ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfc'` for a statement
with weaker assumptions. -/
lemma integrable_cfc [TopologicalSpace X] [OpensSigmaAlgebra X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  have hf_cont (x : X) : ContinuousOn (f x) (spectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  have hcont : ∀ᵐ x ∂μ, Continuous ((spectrum 𝕜 a).domRestrict (f x)) :=
    .of_forall fun x ↦ continuousOn_iff_continuous_domRestrict.mp (hf_cont x)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_eventually_coe_eq_iff.mpr hcont
  refine integrable_cfc' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_domRestrict_of_uncurry hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfc'` for a statement
with weaker assumptions. -/
lemma integrableOn_cfc [TopologicalSpace X] [OpensSigmaAlgebra X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  have hf_cont (x : X) (hx : x ∈ s) : ContinuousOn (f x) (spectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  have hcont : ∀ᵐ x ∂(μ.restrict s), Continuous ((spectrum 𝕜 a).domRestrict (f x)) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      continuousOn_iff_continuous_domRestrict.mp (hf_cont x hx)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_eventually_coe_eq_iff.mpr hcont
  refine integrableOn_cfc' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_domRestrict_of_uncurry hs hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Set in
/-- The continuous functional calculus commutes with integration, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the spectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_integral`. -/
lemma cfc_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(spectrum 𝕜 a, 𝕜))
    (hF : ∀ᵐ x ∂μ, ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x))
    (hF_int : Integrable F μ) (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have key (z : spectrum 𝕜 a) : (∫ x, F x ∂μ) z = ∫ x, f x z ∂μ := by
    rw [integral_apply hF_int]
    refine integral_congr_ae ?_
    filter_upwards [hF] with x hFx
    exact congr_fun hFx z
  have hint : ⇑(∫ x, F x ∂μ) = (spectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ) :=
    funext fun z ↦ key z
  calc cfc (fun z => ∫ x, f x z ∂μ) a
    _ = cfcHom (a := a) ha (∫ x, F x ∂μ) := cfc_apply_of_coe_eq _ a hint ha
    _ = ∫ x, cfcHom (a := a) ha (F x) ∂μ := (cfcHom_integral a F hF_int ha).symm
    _ = ∫ x, cfc (f x) a ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hFx
      exact (cfc_apply_of_coe_eq (f x) a hFx ha).symm

open Set in
/-- The continuous functional calculus commutes with integration, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the spectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_setIntegral`. -/
lemma cfc_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (F : X → C(spectrum 𝕜 a, 𝕜))
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x))
    (hF_int : IntegrableOn F s μ) (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfc (f x) a ∂μ :=
  cfc_integral' f a F hF hF_int ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_integral'` for a statement
with weaker assumptions. -/
lemma cfc_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensSigmaAlgebra X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have hf_cont (x : X) : ContinuousOn (f x) (spectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  have hcont : ∀ᵐ x ∂μ, Continuous ((spectrum 𝕜 a).domRestrict (f x)) :=
    .of_forall fun x ↦ continuousOn_iff_continuous_domRestrict.mp (hf_cont x)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_eventually_coe_eq_iff.mpr hcont
  refine cfc_integral' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_domRestrict_of_uncurry hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_setIntegral'` for a statement
with weaker assumptions. -/
lemma cfc_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensSigmaAlgebra X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  have hf_cont (x : X) (hx : x ∈ s) : ContinuousOn (f x) (spectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  have hcont : ∀ᵐ x ∂(μ.restrict s), Continuous ((spectrum 𝕜 a).domRestrict (f x)) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      continuousOn_iff_continuous_domRestrict.mp (hf_cont x hx)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_eventually_coe_eq_iff.mpr hcont
  refine cfc_setIntegral' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_domRestrict_of_uncurry hs hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

end unital

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [SigmaAlgebra X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

lemma cfcₙL_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcₙHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

lemma cfcₙL_integrable (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcₙL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/-- An integrability criterion for the continuous functional calculus, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the quasispectrum of `a`: the
hypothesis `hF` implies that `f x` is continuous on the quasispectrum and maps `0` to `0` for
almost every `x`, and the integrability of `F` is assumed.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfcₙ`. -/
lemma integrable_cfcₙ' (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hF : ∀ᵐ x ∂μ, ⇑(F x) = (quasispectrum 𝕜 a).domRestrict (f x))
    (hF_int : Integrable F μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine (cfcₙL_integrable a F hF_int ha).congr ?_
  filter_upwards [hF] with x hFx
  exact (cfcₙ_eq_cfcₙL_of_coe_eq (f x) a hFx ha).symm

/-- An integrability criterion for the continuous functional calculus, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the quasispectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfcₙ`. -/
lemma integrableOn_cfcₙ' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = (quasispectrum 𝕜 a).domRestrict (f x))
    (hF_int : IntegrableOn F s μ) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  exact integrable_cfcₙ' f a F hF hF_int ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfcₙ'` for a statement
with weaker assumptions. -/
lemma integrable_cfcₙ [TopologicalSpace X] [OpensSigmaAlgebra X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  have hf_cont (x : X) : ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  have hcont : ∀ᵐ x ∂μ, Continuous ((quasispectrum 𝕜 a).domRestrict (f x)) ∧
      (quasispectrum 𝕜 a).domRestrict (f x) 0 = 0 := by
    filter_upwards [f_zero] with x hx0
    exact ⟨continuousOn_iff_continuous_domRestrict.mp (hf_cont x), hx0⟩
  obtain ⟨F, hF⟩ := ContinuousMapZero.exists_eventually_coe_eq_iff.mpr hcont
  refine integrable_cfcₙ' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_domRestrict_of_uncurry hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfcₙ'` for a statement
with weaker assumptions. -/
lemma integrableOn_cfcₙ [TopologicalSpace X] [OpensSigmaAlgebra X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  have hf_cont (x : X) (hx : x ∈ s) : ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  have hcont : ∀ᵐ x ∂(μ.restrict s), Continuous ((quasispectrum 𝕜 a).domRestrict (f x)) ∧
      (quasispectrum 𝕜 a).domRestrict (f x) 0 = 0 := by
    filter_upwards [ae_restrict_mem hs, f_zero] with x hx hx0
    exact ⟨continuousOn_iff_continuous_domRestrict.mp (hf_cont x hx), hx0⟩
  obtain ⟨F, hF⟩ := ContinuousMapZero.exists_eventually_coe_eq_iff.mpr hcont
  refine integrableOn_cfcₙ' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_domRestrict_of_uncurry hs hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Set in
/-- The continuous functional calculus commutes with integration, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the quasispectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_integral`. -/
lemma cfcₙ_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hF : ∀ᵐ x ∂μ, ⇑(F x) = (quasispectrum 𝕜 a).domRestrict (f x))
    (hF_int : Integrable F μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have key (z : quasispectrum 𝕜 a) : (∫ x, F x ∂μ) z = ∫ x, f x z ∂μ := by
    rw [integral_apply hF_int]
    refine integral_congr_ae ?_
    filter_upwards [hF] with x hFx
    exact congr_fun hFx z
  have hint : ⇑(∫ x, F x ∂μ) = (quasispectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ) :=
    funext fun z ↦ key z
  calc cfcₙ (fun z => ∫ x, f x z ∂μ) a
    _ = cfcₙHom (a := a) ha (∫ x, F x ∂μ) := cfcₙ_apply_of_coe_eq _ a hint ha
    _ = ∫ x, cfcₙHom (a := a) ha (F x) ∂μ := (cfcₙHom_integral a F hF_int ha).symm
    _ = ∫ x, cfcₙ (f x) a ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hFx
      exact (cfcₙ_apply_of_coe_eq (f x) a hFx ha).symm

open Set in
/-- The continuous functional calculus commutes with integration, in terms of a bundled
representative `F` of the restrictions of the functions `f x` to the quasispectrum of `a`.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_setIntegral`. -/
lemma cfcₙ_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (F : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hF : ∀ᵐ x ∂(μ.restrict s), ⇑(F x) = (quasispectrum 𝕜 a).domRestrict (f x))
    (hF_int : IntegrableOn F s μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  cfcₙ_integral' f a F hF hF_int ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_integral'` for a statement
with weaker assumptions. -/
lemma cfcₙ_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensSigmaAlgebra X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have hf_cont (x : X) : ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  have hcont : ∀ᵐ x ∂μ, Continuous ((quasispectrum 𝕜 a).domRestrict (f x)) ∧
      (quasispectrum 𝕜 a).domRestrict (f x) 0 = 0 := by
    filter_upwards [f_zero] with x hx0
    exact ⟨continuousOn_iff_continuous_domRestrict.mp (hf_cont x), hx0⟩
  obtain ⟨F, hF⟩ := ContinuousMapZero.exists_eventually_coe_eq_iff.mpr hcont
  refine cfcₙ_integral' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_domRestrict_of_uncurry hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_setIntegral'` for a statement
with weaker assumptions. -/
lemma cfcₙ_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensSigmaAlgebra X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  have hf_cont (x : X) (hx : x ∈ s) : ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  have hcont : ∀ᵐ x ∂(μ.restrict s), Continuous ((quasispectrum 𝕜 a).domRestrict (f x)) ∧
      (quasispectrum 𝕜 a).domRestrict (f x) 0 = 0 := by
    filter_upwards [ae_restrict_mem hs, f_zero] with x hx hx0
    exact ⟨continuousOn_iff_continuous_domRestrict.mp (hf_cont x hx), hx0⟩
  obtain ⟨F, hF⟩ := ContinuousMapZero.exists_eventually_coe_eq_iff.mpr hcont
  refine cfcₙ_setIntegral' f a F hF ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_domRestrict_of_uncurry hs hF hf
  · exact hasFiniteIntegral_of_ae_coe_eq_domRestrict_of_bound hF bound bound_int bound_ge

end nonunital

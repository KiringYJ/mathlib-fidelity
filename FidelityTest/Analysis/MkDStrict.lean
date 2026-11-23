import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral

/-!
# Almost everywhere continuous families through bundled representatives

`ContinuousMap.mkD`, which replaced a noncontinuous function by a fallback, is removed.  A family
`f : X → Y → E` that is continuous for almost every `x` is represented by a bundled
`F : X → C(Y, E)` with `∀ᵐ x ∂μ, ⇑(F x) = f x`; such a representative exists exactly for almost
everywhere continuous families, and any two agree almost everywhere.  Measurability and
integrability of the representative remain separate hypotheses.
-/

open MeasureTheory
open scoped ContinuousMapZero

/-- info: Unknown constant `ContinuousMap.mkD` -/
#guard_msgs in
#check_failure ContinuousMap.mkD

/-- info: Unknown constant `ContinuousMapZero.mkD` -/
#guard_msgs in
#check_failure ContinuousMapZero.mkD

/-- info: Unknown identifier `cfc_apply_mkD` -/
#guard_msgs in
#check_failure cfc_apply_mkD

section ContinuousMap

variable {X Y E : Type*} [SigmaAlgebra X] [TopologicalSpace Y] [NormedAddCommGroup E]
  {μ : Measure X}

example (f : X → Y → E) (h : ∀ᵐ x ∂μ, Continuous (f x)) :
    ∃ F : X → C(Y, E), ∀ᵐ x ∂μ, ⇑(F x) = f x :=
  ContinuousMap.exists_eventually_coe_eq_iff.mpr h

example (f : X → Y → E) (F : X → C(Y, E)) (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x) :
    ∀ᵐ x ∂μ, Continuous (f x) :=
  ContinuousMap.exists_eventually_coe_eq_iff.mp ⟨F, hF⟩

example (f : X → Y → E) (F F' : X → C(Y, E)) (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x)
    (hF' : ∀ᵐ x ∂μ, ⇑(F' x) = f x) : F =ᵐ[μ] F' :=
  ContinuousMap.eventuallyEq_of_eventually_coe_eq hF hF'

example [CompactSpace Y] (f : X → Y → E) (F : X → C(Y, E)) (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x)
    (bound : X → ℝ) (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y, ‖f x y‖ ≤ bound x) : HasFiniteIntegral F μ :=
  ContinuousMap.hasFiniteIntegral_of_ae_coe_eq_of_bound hF bound bound_int bound_ge

example [CompactSpace Y] [TopologicalSpace X] [OpensSigmaAlgebra X]
    [SecondCountableTopologyEither X (C(Y, E))]
    (f : X → Y → E) (F : X → C(Y, E)) (hF : ∀ᵐ x ∂μ, ⇑(F x) = f x)
    (hf : Continuous (Function.uncurry f)) : AEStronglyMeasurable F μ :=
  ContinuousMap.aeStronglyMeasurable_of_uncurry hF hf

example {t : Set Y} [CompactSpace t] [TopologicalSpace X] [OpensSigmaAlgebra X]
    [SecondCountableTopologyEither X (C(t, E))]
    (f : X → Y → E) (F : X → C(t, E)) (hF : ∀ᵐ x ∂μ, ⇑(F x) = t.domRestrict (f x))
    (hf : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ t)) : AEStronglyMeasurable F μ :=
  ContinuousMap.aeStronglyMeasurable_domRestrict_of_uncurry hF hf

/-- An empty domain makes every function continuous, so representatives exist without a fallback
value. -/
example (f : X → Empty → E) : ∃ F : X → C(Empty, E), ∀ᵐ x ∂μ, ⇑(F x) = f x :=
  ContinuousMap.exists_eventually_coe_eq_iff.mpr (.of_forall fun _ ↦ continuous_of_discreteTopology)

end ContinuousMap

section ContinuousMapZero

variable {X Y E : Type*} [SigmaAlgebra X] [TopologicalSpace Y] [Zero Y] [NormedAddCommGroup E]
  {μ : Measure X}

example (f : X → Y → E) (h : ∀ᵐ x ∂μ, Continuous (f x) ∧ f x 0 = 0) :
    ∃ F : X → C(Y, E)₀, ∀ᵐ x ∂μ, ⇑(F x) = f x :=
  ContinuousMapZero.exists_eventually_coe_eq_iff.mpr h

end ContinuousMapZero

section CFC

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [SigmaAlgebra X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

example (f : 𝕜 → 𝕜) (a : A) (F : C(spectrum 𝕜 a, 𝕜))
    (hF : ⇑F = (spectrum 𝕜 a).domRestrict f) (ha : p a) :
    cfc f a = cfcHom ha F :=
  cfc_apply_of_coe_eq f a hF ha

example [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A) (F : X → C(spectrum 𝕜 a, 𝕜))
    (hF : ∀ᵐ x ∂μ, ⇑(F x) = (spectrum 𝕜 a).domRestrict (f x)) (hF_int : Integrable F μ)
    (ha : p a) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ :=
  cfc_integral' f a F hF hF_int ha

end CFC

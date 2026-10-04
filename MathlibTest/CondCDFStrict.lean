import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Disintegration.CondCDF

/-!
# Strict domain of the conditional cumulative distribution function

These tests check that `ProbabilityTheory.condCDF ρ` requires `HasUniqueCondCDF ρ`, that is, that a
conditional cdf of `ρ` exists and is unique almost everywhere; that instance search derives this
from `SigmaFinite ρ.fst`, in particular for finite measures; that the domain includes infinite
measures with a σ-finite first marginal, such as `volume.prod (gaussianReal 0 1)`, once that
instance is supplied; that neither s-finiteness nor σ-finiteness of `ρ` itself is enough; that
statements about Bochner integrals assume `IsFiniteMeasure ρ`; and that a conditional cdf is
determined only up to null sets of the first marginal.
-/

open MeasureTheory Measure Set Filter
open ProbabilityTheory (condCDF IsCondCDF HasUniqueCondCDF IsCondKernelCDF Kernel IsFiniteKernel cdf
  gaussianReal condCDF_nonneg condCDF_le_one tendsto_condCDF_atBot tendsto_condCDF_atTop
  measurable_condCDF setLIntegral_condCDF integrable_condCDF setIntegral_condCDF integral_condCDF
  isCondCDF_condCDF isCondKernelCDF_condCDF hasUniqueCondCDF_of_sigmaFinite_fst
  tendsto_cdf_atBot tendsto_cdf_atTop ofReal_cdf)
open scoped Topology ENNReal

noncomputable section

/-! ### The domain is enforced -/

-- Planar Lebesgue measure is σ-finite, but its first marginal is not.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF volume

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : ℝ → StieltjesFunction ℝ := condCDF (volume : Measure (ℝ × ℝ))

-- Neither s-finiteness nor σ-finiteness of `ρ` is the domain.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SFinite ρ] :
    α → StieltjesFunction ℝ := condCDF ρ

/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ] :
    α → StieltjesFunction ℝ := condCDF ρ

-- Statements about the conditional cdf need the same evidence.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  inferInstance

/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    condCDF ρ a x ≤ 1 :=
  condCDF_le_one ρ a x

-- Statements about Bochner integrals assume `IsFiniteMeasure ρ`, which a σ-finite marginal does
-- not supply.
/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  integrable_condCDF ρ x

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  setIntegral_condCDF ρ x hs

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  integral_condCDF ρ x

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (Kernel.const Unit ρ)
      (Kernel.const Unit ρ.fst) :=
  isCondKernelCDF_condCDF ρ

/-! ### Routine evidence is found -/

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    HasUniqueCondCDF ρ :=
  inferInstance

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsProbabilityMeasure ρ] :
    HasUniqueCondCDF ρ :=
  inferInstance

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] :
    HasUniqueCondCDF ρ :=
  inferInstance

example {α : Type*} [SigmaAlgebra α] (κ : Kernel Unit (α × ℝ))
    [IsFiniteKernel κ] : HasUniqueCondCDF (κ ()) :=
  inferInstance

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  inferInstance

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (a : α) (x : ℝ) :
    condCDF ρ a x ≤ 1 :=
  condCDF_le_one ρ a x

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (a : α) (x : ℝ) :
    0 ≤ condCDF ρ a x ∧ condCDF ρ a x ≤ 1 :=
  ⟨condCDF_nonneg ρ a x, condCDF_le_one ρ a x⟩

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) ∧ Tendsto (condCDF ρ a) atTop (𝓝 1) :=
  ⟨tendsto_condCDF_atBot ρ a, tendsto_condCDF_atTop ρ a⟩

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) :
    Measurable fun a ↦ condCDF ρ a x :=
  measurable_condCDF ρ x

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  integrable_condCDF ρ x

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsProbabilityMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  integral_condCDF ρ x

/-! ### The specification -/

example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} {F : α → StieltjesFunction ℝ}
    (hF : IsCondCDF ρ F) (a : α) (x : ℝ) : 0 ≤ F a x ∧ F a x ≤ 1 :=
  ⟨hF.nonneg a x, hF.le_one a x⟩

-- The identity for the rays holds at every real `x` and for every measurable set.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) :
    ρ.fst.withDensity (fun a ↦ ENNReal.ofReal (condCDF ρ a x)) = ρ.IicSnd x :=
  (isCondCDF_condCDF ρ).withDensity_eq x

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondCDF_condCDF ρ).lintegral x

-- Two conditional cdfs agree almost everywhere with respect to the first marginal.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F G : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (hG : IsCondCDF ρ G) :
    ∀ᵐ a ∂ρ.fst, F a = G a :=
  HasUniqueCondCDF.ae_eq_of_isCondCDF hF hG

-- Any conditional cdf, not only `condCDF ρ`, satisfies the statements for a finite measure.
example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (x : ℝ) :
    Integrable (fun a ↦ F a x) ρ.fst :=
  hF.integrable x

example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, F a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  hF.setIntegral x hs

example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (x : ℝ) :
    ∫ a, F a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  hF.integral x

example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) :
    IsCondKernelCDF (fun p : Unit × α ↦ F p.2) (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  hF.isCondKernelCDF

-- A conditional cdf is a version of the Radon-Nikodym derivative of the rays.
example {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} [SigmaFinite ρ.fst]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (x : ℝ) :
    (fun a ↦ ENNReal.ofReal (F a x)) =ᵐ[ρ.fst] (ρ.IicSnd x).rnDeriv ρ.fst :=
  hF.ofReal_ae_eq_rnDeriv x

/-! ### Infinite measures in the domain -/

/-- A measure with first marginal Lebesgue measure and all conditional distributions standard
Gaussian. -/
abbrev ρ₀ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (gaussianReal 0 1)

-- It is infinite.
theorem measure_univ_ρ₀ : ρ₀ univ = ∞ := by
  rw [← univ_prod_univ, Measure.prod_prod _ _ MeasurableSet.univ MeasurableSet.univ]
  simp

example : ¬ IsFiniteMeasure ρ₀ := fun _ ↦ measure_ne_top ρ₀ univ measure_univ_ρ₀

-- Its first marginal is Lebesgue measure, and instance search finds that it is σ-finite.
theorem fst_ρ₀ : ρ₀.fst = volume := by
  simp

example : SigmaFinite ρ₀.fst := inferInstance

example : SigmaFinite ((gaussianReal 0 1).prod (volume : Measure ℝ)).snd := inferInstance

-- The marginal instances need the other factor to be finite: the first marginal of planar
-- Lebesgue measure is infinity times Lebesgue measure, which is not σ-finite.
example : ((volume : Measure ℝ).prod (volume : Measure ℝ)).fst = ∞ • (volume : Measure ℝ) := by
  simp

/--
error: failed to synthesize instance of type class
  SigmaFinite (volume.prod volume ⋯).fst

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : SigmaFinite ((volume : Measure ℝ).prod (volume : Measure ℝ)).fst := inferInstance

-- So the conditional cdf of the infinite measure is defined without local evidence.
example : HasUniqueCondCDF ρ₀ :=
  inferInstance

example (x : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ₀ a x) ∂ρ₀.fst = ρ₀ (s ×ˢ Iic x) :=
  setLIntegral_condCDF ρ₀ x hs

/-- For a probability measure `γ`, the constant family `fun _ ↦ cdf γ` is a conditional cdf of the
product measure `μ.prod γ`. -/
theorem isCondCDF_prod_cdf (μ : Measure ℝ) [SigmaFinite μ] (γ : Measure ℝ)
    [IsProbabilityMeasure γ] :
    IsCondCDF (μ.prod γ) fun _ ↦ cdf γ where
  measurable _ := measurable_const
  tendsto_atBot_zero _ := tendsto_cdf_atBot γ
  tendsto_atTop_one _ := tendsto_cdf_atTop γ
  setLIntegral x s hs := by
    rw [Measure.fst, Measure.map_fst_prod, measure_univ, one_smul, setLIntegral_const,
      ofReal_cdf, Measure.prod_prod s (Iic x) hs measurableSet_Iic, mul_comm]

-- The conditional cdf of `volume.prod γ` is almost everywhere the cdf of `γ`.
example : ∀ᵐ a ∂ρ₀.fst, condCDF ρ₀ a = cdf (gaussianReal 0 1) :=
  (isCondCDF_prod_cdf volume (gaussianReal 0 1)).ae_eq_condCDF.mono fun _ h ↦ h.symm

/-! ### Degenerate and non-canonical cases -/

-- Every measurable family of probability distribution functions is a conditional cdf of the zero
-- measure.
theorem isCondCDF_zero {α : Type*} [SigmaAlgebra α] (F : α → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun a ↦ F a x) (h₀ : ∀ a, Tendsto (F a) atBot (𝓝 0))
    (h₁ : ∀ a, Tendsto (F a) atTop (𝓝 1)) : IsCondCDF (0 : Measure (α × ℝ)) F where
  measurable := hF
  tendsto_atBot_zero := h₀
  tendsto_atTop_one := h₁
  setLIntegral x s _ := by simp

-- Hence two such families agree almost everywhere, since the first marginal is zero, and the
-- conditional cdf of the zero measure agrees almost everywhere with any one of them.
example {α : Type*} [SigmaAlgebra α] (F : α → StieltjesFunction ℝ)
    (hF : ∀ x, Measurable fun a ↦ F a x) (h₀ : ∀ a, Tendsto (F a) atBot (𝓝 0))
    (h₁ : ∀ a, Tendsto (F a) atTop (𝓝 1)) :
    ∀ᵐ a ∂(0 : Measure (α × ℝ)).fst, F a = condCDF (0 : Measure (α × ℝ)) a :=
  (isCondCDF_zero F hF h₀ h₁).ae_eq_condCDF

-- A conditional cdf can be modified on a null set of the first marginal.
open scoped Classical in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] {s : Set α}
    (hs : MeasurableSet s) (hρs : ρ.fst s = 0) (G : StieltjesFunction ℝ)
    (hG₀ : Tendsto G atBot (𝓝 0)) (hG₁ : Tendsto G atTop (𝓝 1)) :
    IsCondCDF ρ fun a ↦ if a ∈ s then G else condCDF ρ a := by
  refine (isCondCDF_condCDF ρ).congr (fun x ↦ ?_) (fun a ↦ ?_) (fun a ↦ ?_) ?_
  · have h_eq : (fun a ↦ (if a ∈ s then G else condCDF ρ a) x) =
        fun a ↦ if a ∈ s then G x else condCDF ρ a x := by
      ext a
      split_ifs <;> rfl
    rw [h_eq]
    exact Measurable.ite hs measurable_const (measurable_condCDF ρ x)
  · split_ifs
    exacts [hG₀, tendsto_condCDF_atBot ρ a]
  · split_ifs
    exacts [hG₁, tendsto_condCDF_atTop ρ a]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρs] with a ha
    simp [ha]

-- For a probability measure on `Unit × ℝ`, the conditional cdf is the cdf of the second marginal.
example (ρ : Measure (Unit × ℝ)) [IsProbabilityMeasure ρ] : condCDF ρ () = cdf ρ.snd := by
  have h : IsCondCDF ρ fun _ ↦ cdf ρ.snd :=
    { measurable := fun _ ↦ measurable_const
      tendsto_atBot_zero := fun _ ↦ tendsto_cdf_atBot ρ.snd
      tendsto_atTop_one := fun _ ↦ tendsto_cdf_atTop ρ.snd
      setLIntegral := fun x s hs ↦ by
        rcases s.eq_empty_or_nonempty with rfl | hne
        · simp
        · rw [Subsingleton.eq_univ_of_nonempty hne, setLIntegral_univ, lintegral_const,
            ofReal_cdf, measure_univ, mul_one, univ_prod,
            ← Measure.snd_apply measurableSet_Iic] }
  obtain ⟨a, ha⟩ := h.ae_eq_condCDF.exists
  rw [Subsingleton.elim a ()] at ha
  exact ha.symm

/-! ### Proof independence and rewriting -/

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) (h₁ h₂ : HasUniqueCondCDF ρ) :
    @condCDF _ _ ρ h₁ = @condCDF _ _ ρ h₂ :=
  rfl

-- The instance derived from finiteness agrees with any other proof.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (h : HasUniqueCondCDF ρ) : condCDF ρ = @condCDF _ _ ρ h :=
  rfl

-- `rw [h]` cannot replace `ρ` below its instance argument; `simp only [h]` and `subst` can.
example {α : Type*} [SigmaAlgebra α] (ρ ν : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    [SigmaFinite ν.fst] (h : ρ = ν) (a : α) (x : ℝ) : condCDF ρ a x = condCDF ν a x := by
  simp only [h]

example {α : Type*} [SigmaAlgebra α] (ρ ν : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    [SigmaFinite ν.fst] (h : ρ = ν) : condCDF ρ = condCDF ν := by
  subst h
  rfl

-- A lemma proved from σ-finiteness of the first marginal rewrites a goal whose evidence comes from
-- finiteness of the measure, and conversely.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) := by
  rw [@setLIntegral_condCDF _ _ ρ
    (hasUniqueCondCDF_of_sigmaFinite_fst ρ) x _ hs]

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal
      (@condCDF _ _ ρ (hasUniqueCondCDF_of_sigmaFinite_fst ρ) a x) ∂ρ.fst =
        ρ (s ×ˢ Iic x) := by
  rw [setLIntegral_condCDF ρ x hs]

-- A conditional cdf of a finite measure is a conditional kernel CDF.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  isCondKernelCDF_condCDF ρ

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Disintegration.CondCDF

/-!
# The conditional cumulative distribution function as an almost-everywhere class

These tests check that `ProbabilityTheory.condCDF ρ` requires `HasUniqueCondCDF ρ`, that is, that a
conditional cdf of `ρ` exists and is unique almost everywhere; that instance search derives this
from `SigmaFinite ρ.fst`, in particular for finite measures; that the domain includes infinite
measures with a σ-finite first marginal, such as `volume.prod (gaussianReal 0 1)`, once that
instance is supplied; that neither s-finiteness nor σ-finiteness of `ρ` itself is enough; that
`condCDF ρ` is the `ρ.fst`-almost-everywhere class of the conditional cdfs, which every conditional
cdf represents, while no conditional cdf is chosen; that its representatives are determined only up
to null sets of the first marginal and need not be conditional cdfs there; and that statements
about Bochner integrals, stated for every conditional cdf, assume `IsFiniteMeasure ρ`.
-/

open MeasureTheory Measure Set Filter
open ProbabilityTheory (condCDF IsCondCDF HasUniqueCondCDF IsCondKernelCDF Kernel IsFiniteKernel cdf
  gaussianReal exists_isCondCDF_mem_condCDF isCondCDF_of_mem_condCDF
  hasUniqueCondCDF_of_sigmaFinite_fst tendsto_cdf_atBot tendsto_cdf_atTop ofReal_cdf)
open scoped Topology ENNReal

noncomputable section

/-! ### No conditional cdf is chosen -/

/-- error: Unknown identifier `ProbabilityTheory.isCondCDF_condCDF` -/
#guard_msgs in
#check ProbabilityTheory.isCondCDF_condCDF

/-- error: Unknown constant `ProbabilityTheory.IsCondCDF.ae_eq_condCDF` -/
#guard_msgs in
#check ProbabilityTheory.IsCondCDF.ae_eq_condCDF

/-- error: Unknown identifier `ProbabilityTheory.condCDF_le_one` -/
#guard_msgs in
#check ProbabilityTheory.condCDF_le_one

/-- error: Unknown identifier `ProbabilityTheory.setLIntegral_condCDF` -/
#guard_msgs in
#check ProbabilityTheory.setLIntegral_condCDF

/-- error: Unknown identifier `ProbabilityTheory.isCondKernelCDF_condCDF` -/
#guard_msgs in
#check ProbabilityTheory.isCondKernelCDF_condCDF

/-- error: Unknown identifier `ProbabilityTheory.instIsProbabilityMeasureCondCDF` -/
#guard_msgs in
#check ProbabilityTheory.instIsProbabilityMeasureCondCDF

/-! ### The domain is enforced -/

-- Planar Lebesgue measure is σ-finite, but its first marginal is not.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF volume

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : (ae (volume : Measure (ℝ × ℝ)).fst).Germ (StieltjesFunction ℝ) :=
  condCDF (volume : Measure (ℝ × ℝ))

-- Neither s-finiteness nor σ-finiteness of `ρ` is the domain.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SFinite ρ] :
    (ae ρ.fst).Germ (StieltjesFunction ℝ) := condCDF ρ

/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ] :
    (ae ρ.fst).Germ (StieltjesFunction ℝ) := condCDF ρ

-- The class is not a family of functions: it cannot be evaluated at a point.
/--
error: Function expected at
  condCDF ρ
but this term has type
  (ae ρ.fst).Germ (StieltjesFunction ℝ)

Note: Expected a function because this term is being applied to the argument
  a
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (a : α) :
    StieltjesFunction ℝ := condCDF ρ a

-- Membership in the class needs the same evidence.
/--
error: failed to synthesize instance of type class
  HasUniqueCondCDF ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) (F : α → StieltjesFunction ℝ) : Prop :=
  F ∈ condCDF ρ

-- Statements about Bochner integrals assume `IsFiniteMeasure ρ`, which a σ-finite marginal does
-- not supply.
/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (x : ℝ) :
    Integrable (fun a ↦ F a x) ρ.fst :=
  hF.integrable x

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ρ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) :
    IsCondKernelCDF (fun p : Unit × α ↦ F p.2) (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  hF.isCondKernelCDF

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

/-! ### The class and its representatives -/

section Class

variable {α : Type*} [SigmaAlgebra α] {ρ : Measure (α × ℝ)} {F G : α → StieltjesFunction ℝ}

-- Every conditional cdf represents `condCDF ρ`, and some conditional cdf does.
example [HasUniqueCondCDF ρ] (hF : IsCondCDF ρ F) : F ∈ condCDF ρ :=
  hF.mem_condCDF

example [SigmaFinite ρ.fst] : ∃ F, IsCondCDF ρ F ∧ F ∈ condCDF ρ :=
  exists_isCondCDF_mem_condCDF ρ

-- Two representatives agree `ρ.fst`-almost everywhere, and given a conditional cdf, the
-- representatives are exactly the families that agree with it almost everywhere.
example [HasUniqueCondCDF ρ] (hF : F ∈ condCDF ρ) (hG : G ∈ condCDF ρ) :
    ∀ᵐ a ∂ρ.fst, F a = G a :=
  Filter.Germ.eventuallyEq_of_mem hF hG

example [HasUniqueCondCDF ρ] (hF : IsCondCDF ρ F) : G ∈ condCDF ρ ↔ ∀ᵐ a ∂ρ.fst, G a = F a :=
  hF.mem_condCDF_iff

-- A representative that is measurable and consists of probability cdfs is a conditional cdf.
example [HasUniqueCondCDF ρ] (hG : G ∈ condCDF ρ) (hG_meas : ∀ x, Measurable fun a ↦ G a x)
    (hG_atBot : ∀ a, Tendsto (G a) atBot (𝓝 0)) (hG_atTop : ∀ a, Tendsto (G a) atTop (𝓝 1)) :
    IsCondCDF ρ G :=
  isCondCDF_of_mem_condCDF hG hG_meas hG_atBot hG_atTop

-- The statements about a conditional cdf hold for every conditional cdf.
example (hF : IsCondCDF ρ F) (a : α) (x : ℝ) : 0 ≤ F a x ∧ F a x ≤ 1 :=
  ⟨hF.nonneg a x, hF.le_one a x⟩

example (hF : IsCondCDF ρ F) (x : ℝ) :
    ρ.fst.withDensity (fun a ↦ ENNReal.ofReal (F a x)) = ρ.IicSnd x :=
  hF.withDensity_eq x

example (hF : IsCondCDF ρ F) (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  hF.lintegral x

example [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) : Integrable (fun a ↦ F a x) ρ.fst :=
  hF.integrable x

example [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ∫ a in s, F a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  hF.setIntegral x hs

example [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) :
    ∫ a, F a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  hF.integral x

example [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) :
    IsCondKernelCDF (fun p : Unit × α ↦ F p.2) (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  hF.isCondKernelCDF

example [SigmaFinite ρ.fst] (hF : IsCondCDF ρ F) (x : ℝ) :
    (fun a ↦ ENNReal.ofReal (F a x)) =ᵐ[ρ.fst] (ρ.IicSnd x).rnDeriv ρ.fst :=
  hF.ofReal_ae_eq_rnDeriv x

example (hF : IsCondCDF ρ F) (a : α) : IsProbabilityMeasure (F a).measure :=
  hF.isProbabilityMeasure a

example (hF : IsCondCDF ρ F) : Measurable fun a ↦ (F a).measure :=
  hF.measurable_measure

end Class

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

-- The conditional cdf of `volume.prod γ` is the class of the constant cdf of `γ`.
example : (fun _ ↦ cdf (gaussianReal 0 1)) ∈ condCDF ρ₀ :=
  (isCondCDF_prod_cdf volume (gaussianReal 0 1)).mem_condCDF

example : condCDF ρ₀ = ((fun _ ↦ cdf (gaussianReal 0 1) : ℝ → StieltjesFunction ℝ) :
    (ae ρ₀.fst).Germ (StieltjesFunction ℝ)) :=
  (isCondCDF_prod_cdf volume (gaussianReal 0 1)).mem_condCDF.symm

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

-- Every family represents the conditional cdf of the zero measure, whose first marginal is zero,
-- including a family that is not a conditional cdf: a representative is determined only up to null
-- sets of the first marginal.
example {α : Type*} [SigmaAlgebra α] (F : α → StieltjesFunction ℝ) :
    F ∈ condCDF (0 : Measure (α × ℝ)) := by
  obtain ⟨G, -, hG⟩ := exists_isCondCDF_mem_condCDF (0 : Measure (α × ℝ))
  exact Filter.Germ.mem_of_eventuallyEq hG (by simp [EventuallyEq])

example {α : Type*} [SigmaAlgebra α] [Nonempty α] :
    ¬ IsCondCDF (0 : Measure (α × ℝ)) fun _ ↦ StieltjesFunction.const ℝ 0 := by
  intro h
  have h₁ := h.tendsto_atTop_one (Classical.arbitrary α)
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h₁)

-- A conditional cdf can be modified on a null set of the first marginal.
open scoped Classical in
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) {s : Set α} (hs : MeasurableSet s)
    (hρs : ρ.fst s = 0) (G : StieltjesFunction ℝ) (hG₀ : Tendsto G atBot (𝓝 0))
    (hG₁ : Tendsto G atTop (𝓝 1)) :
    IsCondCDF ρ fun a ↦ if a ∈ s then G else F a := by
  refine hF.congr (fun x ↦ ?_) (fun a ↦ ?_) (fun a ↦ ?_) ?_
  · have h_eq : (fun a ↦ (if a ∈ s then G else F a) x) =
        fun a ↦ if a ∈ s then G x else F a x := by
      ext a
      split_ifs <;> rfl
    rw [h_eq]
    exact Measurable.ite hs measurable_const (hF.measurable x)
  · split_ifs
    exacts [hG₀, hF.tendsto_atBot_zero a]
  · split_ifs
    exacts [hG₁, hF.tendsto_atTop_one a]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρs] with a ha
    simp [ha]

-- For a probability measure on `Unit × ℝ`, every representative of the conditional cdf is the cdf
-- of the second marginal at the atom `()`.
example (ρ : Measure (Unit × ℝ)) [IsProbabilityMeasure ρ] {F : Unit → StieltjesFunction ℝ}
    (hF : F ∈ condCDF ρ) : F () = cdf ρ.snd := by
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
  obtain ⟨a, ha⟩ := (h.mem_condCDF_iff.1 hF).exists
  rw [Subsingleton.elim a ()] at ha
  exact ha

/-! ### Proof independence and rewriting -/

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) (h₁ h₂ : HasUniqueCondCDF ρ) :
    @condCDF _ _ ρ h₁ = @condCDF _ _ ρ h₂ :=
  rfl

-- The instance derived from finiteness agrees with any other proof.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (h : HasUniqueCondCDF ρ) : condCDF ρ = @condCDF _ _ ρ h :=
  rfl

-- `subst` replaces `ρ` below its instance argument.
example {α : Type*} [SigmaAlgebra α] (ρ ν : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    [SigmaFinite ν.fst] (h : ρ = ν) {F : α → StieltjesFunction ℝ} (hF : F ∈ condCDF ρ) :
    F ∈ condCDF ν := by
  subst h
  exact hF

-- A lemma proved from σ-finiteness of the first marginal applies to evidence from finiteness of
-- the measure, and conversely.
example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) : F ∈ condCDF ρ :=
  @ProbabilityTheory.IsCondCDF.mem_condCDF _ _ ρ F (hasUniqueCondCDF_of_sigmaFinite_fst ρ) hF

example {α : Type*} [SigmaAlgebra α] (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) :
    F ∈ @condCDF _ _ ρ (hasUniqueCondCDF_of_sigmaFinite_fst ρ) :=
  hF.mem_condCDF

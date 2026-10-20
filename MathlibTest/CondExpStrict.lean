import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Martingale.Basic

/-!
# Strict conditional expectation

These tests ensure that the conditional expectation `μ[f | m]` is the almost everywhere class of the
versions of the conditional expectation, defined exactly on its domain `HasUniqueCondExp m μ f`,
that the default tactic finds the domain from the routine sufficient conditions and fails with a
clear message otherwise, that the domain is strictly larger than the sufficient condition, and that
the fallback API is gone.
-/

open MeasureTheory Filter Set

/-! The fallback API is gone. -/

/-- info: Unknown identifier `MeasureTheory.condExp_of_not_le` -/
#guard_msgs in
#check_failure MeasureTheory.condExp_of_not_le

/-- info: Unknown identifier `MeasureTheory.condExp_of_not_integrable` -/
#guard_msgs in
#check_failure MeasureTheory.condExp_of_not_integrable

/-- info: Unknown identifier `MeasureTheory.condExp_of_not_sigmaFinite` -/
#guard_msgs in
#check_failure MeasureTheory.condExp_of_not_sigmaFinite

/-- info: Unknown identifier `MeasureTheory.integrable_condExp` -/
#guard_msgs in
#check_failure MeasureTheory.integrable_condExp

/-- info: Unknown identifier `MeasureTheory.stronglyMeasurable_condExp` -/
#guard_msgs in
#check_failure MeasureTheory.stronglyMeasurable_condExp

/-- info: Unknown identifier `MeasureTheory.condExpL1` -/
#guard_msgs in
#check_failure MeasureTheory.condExpL1

/-- info: Unknown identifier `MeasureTheory.condExpIndL1` -/
#guard_msgs in
#check_failure MeasureTheory.condExpIndL1

/-- info: Unknown identifier `MeasureTheory.martingale_condExp` -/
#guard_msgs in
#check_failure MeasureTheory.martingale_condExp

variable {α : Type*} {m m0 : SigmaAlgebra α} {μ : Measure[m0] α} {f g : α → ℝ}

/-! The class of the versions and its domain. -/

/-- info: fun h => μ[f | m] : HasUniqueCondExp m μ f → (ae μ).Germ ℝ -/
#guard_msgs in
#check fun h : HasUniqueCondExp m μ f ↦ μ[f | m]

/-- The default tactic finds the domain from a sub-σ-algebra on which the measure is σ-finite and
an integrable function. -/
noncomputable example (hm : m ≤ m0) [IsFiniteMeasure μ] (hf : Integrable f μ) : (ae μ).Germ ℝ :=
  μ[f | m]

example (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    HasUniqueCondExp m μ f := by
  has_unique_cond_exp

/-- A version represents the class. -/
example (hm : m ≤ m0) [IsFiniteMeasure μ] (hf : Integrable f μ) (hg : IsCondExp m μ f g) :
    μ[f | m] = g :=
  hg.condExp_eq _

/-- A version from a hypothesis gives the domain without σ-finiteness. -/
noncomputable example (hm : m ≤ m0) (hf : Integrable f μ) (hg : IsCondExp m μ f g) :
    (ae μ).Germ ℝ :=
  μ[f | m]

-- Without integrability, the domain is not found.
/--
error: this function needs a proof `HasUniqueCondExp m μ f` that it has a conditional expectation given `m`, unique almost everywhere, for example from its integrability and the σ-finiteness of `μ` on `m`
-/
#guard_msgs (substring := true) in
noncomputable example (hm : m ≤ m0) [IsFiniteMeasure μ] : (ae μ).Germ ℝ := μ[f | m]

-- Without a proof that `m` is a sub-σ-algebra, the domain is not found.
/--
error: this function needs a proof `HasUniqueCondExp m μ f` that it has a conditional expectation given `m`, unique almost everywhere, for example from its integrability and the σ-finiteness of `μ` on `m`
-/
#guard_msgs (substring := true) in
noncomputable example [IsFiniteMeasure μ] (hf : Integrable f μ) : (ae μ).Germ ℝ := μ[f | m]

/-! The tactic `sub_sigma_algebra` proves the routine sub-σ-algebra facts. -/

example (hm : m ≤ m0) : m ≤ m0 := by sub_sigma_algebra

example : (⊥ : SigmaAlgebra α) ≤ m0 := by sub_sigma_algebra

example {ι : Type*} [Preorder ι] (ℱ : Filtration ι m0) (i : ι) : ℱ i ≤ m0 := by sub_sigma_algebra

example {ι : Type*} [Preorder ι] (ℱ : Filtration ι m0) : ⨆ i, ℱ i ≤ m0 := by sub_sigma_algebra

example {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0} {τ : α → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) : hτ.sigmaAlgebra ≤ m0 := by
  sub_sigma_algebra

-- The chain of two hypotheses is searched with backtracking.
example {m₁ m₂ : SigmaAlgebra α} (h₂ : m ≤ m₂) (h₃ : m₂ ≤ m0) (_h₁ : m ≤ m₁) : m ≤ m0 := by
  sub_sigma_algebra

/-- error: this σ-algebra needs a proof that it is a sub-σ-algebra of the ambient one -/
#guard_msgs (substring := true) in
example : m ≤ m0 := by sub_sigma_algebra

/-! Uniqueness of the versions of an integrable function needs no σ-finiteness, so a version gives
the domain. The domain is therefore strictly larger than the sufficient condition: counting measure
on `ℝ` is not σ-finite, but every integrable function is its own conditional expectation given the
whole σ-algebra. -/

example (hm : m ≤ m0) (hf : Integrable f μ) {g' : α → ℝ} (hg : IsCondExp m μ f g)
    (hg' : IsCondExp m μ f g') : g =ᵐ[μ] g' :=
  hg.ae_eq hm hf hg'

example {f : ℝ → ℝ} (hf : Integrable f Measure.count) :
    HasUniqueCondExp (inferInstance : SigmaAlgebra ℝ) Measure.count f :=
  .of_isCondExp le_rfl hf (isCondExp_self hf.aestronglyMeasurable)

/-! Given the trivial σ-algebra, Lebesgue measure on `ℝ` is not σ-finite, and the indicator of
`[0, 1]` has no conditional expectation: a version is almost everywhere constant, integrable, hence
zero, but its integral must be `1`. -/

example : ¬∃ g, IsCondExp ⊥ (volume : Measure ℝ) ((Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) g := by
  rintro ⟨g, hg⟩
  have hf : Integrable ((Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  obtain ⟨g', hg'm, hgg'⟩ := hg.aestronglyMeasurable
  obtain ⟨c, rfl⟩ := stronglyMeasurable_bot_iff.1 hg'm
  have hc : c = 0 := by
    have hint : Integrable (fun _ : ℝ ↦ c) volume := (hg.integrable hf).congr hgg'
    by_contra hc
    exact (integrable_const_iff.1 hint).resolve_left hc |>.measure_univ_lt_top.ne (by simp)
  have h := hg.integral_eq hf
  rw [integral_congr_ae hgg', hc, integral_zero, integral_indicator measurableSet_Icc] at h
  simp at h

/-! Martingales. -/

variable {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0} {F : ι → α → ℝ}

/-- A martingale is its own conditional expectation, without σ-finiteness. -/
example (hF : Martingale F ℱ μ) {i j : ι} (hij : i ≤ j) : IsCondExp (ℱ i) μ (F j) (F i) :=
  hF.isCondExp hij

example (hF : Martingale F ℱ μ) {i j : ι} (hij : i ≤ j) {s : Set α} (hs : s ∈ ℱ i) :
    ∫ x in s, F i x ∂μ = ∫ x in s, F j x ∂μ :=
  hF.setIntegral_eq hij hs

/-- Every version of the conditional expectation of a submartingale dominates it. -/
example (hF : Submartingale F ℱ μ) {i j : ι} (hij : i ≤ j) (hg : IsCondExp (ℱ i) μ (F j) g) :
    F i ≤ᵐ[μ] g :=
  hF.ae_le_isCondExp hij hg

import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Kernel.WithDensity

/-!
# Kernel density changes on their exact domain

These tests ensure that `Kernel.withDensity` requires exactly the measurability of its
measure-valued output.  The usual s-finite and jointly measurable case remains automatic, while
special cases whose output is manifestly measurable work without s-finiteness or measurability of
the density.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β]

/-! ### The exact domain -/

example (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) : Kernel α β :=
  κ.withDensity f

example (κ : Kernel α β) (w : α → ℝ≥0∞) (hw : Measurable w) : Kernel α β :=
  κ.withDensity fun a _ ↦ w a

example (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) : IsSFiniteKernel (κ.withDensity f) :=
  Kernel.IsSFiniteKernel.withDensity κ hf

example :
    IsSFiniteKernel
      ((Kernel.const Unit (Measure.dirac ())).withDensity (fun _ _ ↦ (∞ : ℝ≥0∞))) :=
  Kernel.IsSFiniteKernel.withDensity _ measurable_const

example :
    ((Kernel.const Unit (Measure.dirac ())).withDensity (fun _ _ ↦ (∞ : ℝ≥0∞))) () Set.univ =
      ∞ := by
  simp

example (κ : Kernel α β) (f : α → β → ℝ≥0∞)
    (h : Measurable fun a ↦ (κ a).withDensity (f a)) : Kernel α β :=
  κ.withDensity f h

example (κ : Kernel α β) (f : α → β → ℝ≥0∞)
    (h₁ h₂ : Measurable fun a ↦ (κ a).withDensity (f a)) :
    κ.withDensity f h₁ = κ.withDensity f h₂ := rfl

example (κ : Kernel α β) (f : α → β → ℝ≥0∞)
    (h : Measurable fun a ↦ (κ a).withDensity (f a)) (a : α) :
    κ.withDensity f h a = (κ a).withDensity (f a) := rfl

example (κ : Kernel α β) [IsFiniteKernel κ] (f : α → β → ℝ≥0∞)
    (h : Measurable fun a ↦ (κ a).withDensity (f a)) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hfB : ∀ a b, f a b ≤ B) : IsFiniteKernel (κ.withDensity f h) :=
  Kernel.isFiniteKernel_withDensity_of_bounded κ hB hfB

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: provide a proof that the weighted measures depend measurably on the parameter
α : Type u_1
β : Type u_2
inst✝¹ : SigmaAlgebra α
inst✝ : SigmaAlgebra β
κ : Kernel α β
f : α → β → ℝ≥0∞
⊢ Measurable fun a => (κ a).withDensity (f a)
-/
#guard_msgs in
example (κ : Kernel α β) (f : α → β → ℝ≥0∞) : Kernel α β :=
  κ.withDensity f

/-! ### Exact-domain automation beyond s-finite kernels -/

-- The constant kernel of counting measure on `ℝ` is not s-finite.
example : ¬ IsSFiniteKernel (Kernel.const Unit (Measure.count : Measure ℝ)) := by
  rw [Kernel.isSFiniteKernel_const]
  intro h
  have h_countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := (Measure.count : Measure ℝ)) (As := fun a : ℝ ↦ ({a} : Set ℝ))
    (fun a ↦ measurableSet_singleton a) (fun a b hab ↦ Set.disjoint_singleton.2 hab)
  have h_eq : {a : ℝ | 0 < (Measure.count : Measure ℝ) {a}} = Set.univ := by
    ext a
    simp
  rw [h_eq] at h_countable
  exact Cardinal.not_countable_real h_countable

example :
    (Kernel.const Unit (Measure.count : Measure ℝ)).withDensity (fun _ _ ↦ 1) =
      Kernel.const Unit Measure.count := by
  simp

example (κ : Kernel α β) : κ.withDensity (fun _ _ ↦ 0) = 0 := by
  simp

-- A zero kernel has measurable zero output for every density, including nonmeasurable ones.
example (f : α → β → ℝ≥0∞) : (0 : Kernel α β).withDensity f = 0 := by
  simp

/-! ### Sectionwise algebra on exact-domain kernels -/

variable {ι : Type*}

example (κ : Kernel α β) {f g : α → β → ℝ≥0∞}
    {hf : Measurable fun a ↦ (κ a).withDensity (f a)}
    {hg : Measurable fun a ↦ (κ a).withDensity (g a)}
    (hg' : ∀ a, Measurable (g a)) :
    κ.withDensity (f + g) (Kernel.measurable_withDensity_add_right hf hg hg') =
      κ.withDensity f hf + κ.withDensity g hg :=
  Kernel.withDensity_add_right hg'

example (κ : Kernel α β) {f g : α → β → ℝ≥0∞}
    {hf : Measurable fun a ↦ (κ a).withDensity (f a)}
    {hg : Measurable fun a ↦ (κ.withDensity f hf a).withDensity (g a)}
    (hf' : ∀ a, Measurable (f a)) (hg' : ∀ a, Measurable (g a)) :
    κ.withDensity (fun a b ↦ f a b * g a b)
        (Kernel.measurable_withDensity_mul hf' hg' hg) =
      (κ.withDensity f hf).withDensity g hg :=
  Kernel.withDensity_mul hf' hg'

example [Countable ι] (κ : Kernel α β) {f : ι → α → β → ℝ≥0∞}
    {hf : ∀ i, Measurable fun a ↦ (κ a).withDensity (f i a)}
    (hf' : ∀ i a, Measurable (f i a)) :
    κ.withDensity (∑' i, f i) (Kernel.measurable_withDensity_tsum hf hf') =
      Kernel.sum fun i ↦ κ.withDensity (f i) (hf i) :=
  Kernel.withDensity_tsum κ hf'

/-! ### A genuinely nonmeasurable output -/

section TrivialSource

local instance : SigmaAlgebra Bool := ⊥

private lemma not_measurable_variable_dirac_weight :
    ¬Measurable fun a : Bool ↦
      (Measure.dirac ()).withDensity (fun _ : Unit ↦ if a then 1 else 0) := by
  intro h
  have hmass : Measurable fun a : Bool ↦
      ((Measure.dirac ()).withDensity (fun _ : Unit ↦ if a then 1 else 0)) Set.univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp h
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot hmass
  have h_eq := (congrFun hc true).trans (congrFun hc false).symm
  simp at h_eq

example :
    ¬ ∃ η : Kernel Bool Unit, ∀ a,
      η a = (Measure.dirac ()).withDensity (fun _ : Unit ↦ if a then 1 else 0) :=
  (Kernel.exists_withDensity_iff
    (κ := Kernel.const Bool (Measure.dirac ()))
    (f := fun (a : Bool) (_ : Unit) ↦ if a then 1 else 0)).not.mpr
      not_measurable_variable_dirac_weight

end TrivialSource

/-! ### Removed fallback -/

/-- error: Unknown constant `ProbabilityTheory.Kernel.withDensity_of_not_measurable` -/
#guard_msgs in
#check ProbabilityTheory.Kernel.withDensity_of_not_measurable

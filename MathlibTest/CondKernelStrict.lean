import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Conditional kernels without a public arbitrary point

These tests check that the construction with an arbitrary point, `borelMarkovFromReal`, and the
kernels, lemmas, instances, and equations that exposed it are not public; that finite measures and
finite kernels are disintegrated by Markov kernels; that `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.Kernel.condKernel` are chosen among those kernels, so that every finite kernel
that disintegrates agrees with them almost everywhere, and `MeasureTheory.Measure.condKernel` is
determined at atoms; that a conditional kernel is determined only up to null sets, while the
specification rejects a kernel that is wrong on a set of positive measure; and that the conditional
kernels still require a finite measure or a finite kernel.
-/

open MeasureTheory ProbabilityTheory SigmaAlgebra

noncomputable section

/-! ### The construction with an arbitrary point is private -/

/-- error: Unknown constant `ProbabilityTheory.Kernel.borelMarkovFromReal` -/
#guard_msgs in
#check Kernel.borelMarkovFromReal

/-- error: Unknown constant `ProbabilityTheory.Kernel.borelMarkovFromReal_apply` -/
#guard_msgs in
#check Kernel.borelMarkovFromReal_apply

/-- error: Unknown constant `ProbabilityTheory.Kernel.borelMarkovFromReal_apply'` -/
#guard_msgs in
#check Kernel.borelMarkovFromReal_apply'

/-- error: Unknown constant `ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal` -/
#guard_msgs in
#check Kernel.compProd_fst_borelMarkovFromReal

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsSFiniteKernelBorelMarkovFromReal` -/
#guard_msgs in
#check Kernel.instIsSFiniteKernelBorelMarkovFromReal

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsFiniteKernelBorelMarkovFromReal` -/
#guard_msgs in
#check Kernel.instIsFiniteKernelBorelMarkovFromReal

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsMarkovKernelBorelMarkovFromReal` -/
#guard_msgs in
#check Kernel.instIsMarkovKernelBorelMarkovFromReal

/-! ### The kernels and equations built from it are removed -/

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernelBorel` -/
#guard_msgs in
#check Kernel.condKernelBorel

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelBorel` -/
#guard_msgs in
#check Kernel.instIsMarkovKernelCondKernelBorel

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernelBorel.instIsCondKernel` -/
#guard_msgs in
#check Kernel.condKernelBorel.instIsCondKernel

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernelUnitBorel` -/
#guard_msgs in
#check Kernel.condKernelUnitBorel

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelUnitBorel` -/
#guard_msgs in
#check Kernel.instIsMarkovKernelCondKernelUnitBorel

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernelUnitBorel.instIsCondKernel` -/
#guard_msgs in
#check Kernel.condKernelUnitBorel.instIsCondKernel

/-- error: Unknown constant `MeasureTheory.Measure.condKernel_apply` -/
#guard_msgs in
#check Measure.condKernel_apply

/-- error: Unknown constant `MeasureTheory.Measure.condKernel_def` -/
#guard_msgs in
#check Measure.condKernel_def

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernel_def` -/
#guard_msgs in
#check Kernel.condKernel_def

/-! ### Existence and uniqueness -/

section General

variable {α β Ω : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra Ω]
  [StandardBorelSpace Ω] [Nonempty Ω]

-- A finite measure on `α × Ω` is disintegrated by a Markov kernel, for every measurable space `α`.
example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η :=
  ρ.exists_isMarkovKernel_isCondKernel

-- `ρ.condKernel` is such a kernel, and every finite kernel that disintegrates `ρ` agrees with it
-- `ρ.fst`-almost everywhere.
example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : IsMarkovKernel ρ.condKernel :=
  inferInstance

example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : ρ.fst ⊗ₘ ρ.condKernel = ρ :=
  ρ.disintegrate ρ.condKernel

example {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] (η : Kernel α Ω) [IsFiniteKernel η]
    (hη : ρ = ρ.fst ⊗ₘ η) : ∀ᵐ a ∂ρ.fst, η a = ρ.condKernel a :=
  eq_condKernel_of_measure_eq_compProd η hη

-- A finite kernel `κ : Kernel α (β × Ω)` is disintegrated by a Markov kernel when `α` is countable
-- or `β` is countably generated, `Kernel.condKernel κ` is such a kernel, and every finite kernel
-- that disintegrates `κ` agrees with it at `(a, b)` for `fst κ a`-almost every `b`.
example [CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η :=
  κ.exists_isMarkovKernel_isCondKernel

example [CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (Kernel.condKernel κ) :=
  inferInstance

example [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
    {η : Kernel (α × β) Ω} [IsFiniteKernel η] (hη : Kernel.fst κ ⊗ₖ η = κ) (a : α) :
    ∀ᵐ b ∂(Kernel.fst κ a), η (a, b) = Kernel.condKernel κ (a, b) :=
  eq_condKernel_of_kernel_eq_compProd hη a

-- `Kernel.condKernel` for a countable `α`, with no assumption on `β`, and for a countably generated
-- `β`, with no assumption on `α`.
example (κ : Kernel ℕ (β × Ω)) [IsFiniteKernel κ] : Kernel.fst κ ⊗ₖ Kernel.condKernel κ = κ :=
  κ.disintegrate _

example (κ : Kernel α (ℝ × Ω)) [IsFiniteKernel κ] : Kernel.fst κ ⊗ₖ Kernel.condKernel κ = κ :=
  κ.disintegrate _

end General

/-! ### Determined at atoms, and only almost everywhere -/

/-- The point mass at `(0, 1)`: its first marginal is `dirac 0`. -/
abbrev ρ₀₁ : Measure (ℝ × ℝ) := Measure.dirac ((0 : ℝ), (1 : ℝ))

theorem fst_ρ₀₁ : ρ₀₁.fst = Measure.dirac 0 := by
  ext s hs
  rw [Measure.fst_apply hs]
  change Measure.dirac ((0 : ℝ), (1 : ℝ)) (Prod.fst ⁻¹' s) = Measure.dirac 0 s
  rw [Measure.dirac_apply' _ (measurable_fst hs), Measure.dirac_apply' _ hs]
  by_cases h : (0 : ℝ) ∈ s <;> simp [h]

-- At the atom `0` of the first marginal the conditional kernel is determined: `ρ₀₁.condKernel 0`
-- is `dirac 1`, whatever choice `ρ₀₁.condKernel` makes on null sets.
example : ρ₀₁.condKernel 0 = Measure.dirac 1 := by
  ext s hs
  rw [Measure.condKernel_apply_of_ne_zero (by simp [fst_ρ₀₁]) s, fst_ρ₀₁,
    Measure.dirac_apply' _ ((measurableSet_singleton _).prod hs), Measure.dirac_apply' _ hs]
  by_cases h : (1 : ℝ) ∈ s <;> simp [h]

-- The specification rejects a kernel that is wrong at the atom, a set of positive measure: the
-- constant kernel `dirac 0` does not disintegrate `ρ₀₁`.
example : ¬ ρ₀₁.IsCondKernel (Kernel.const ℝ (Measure.dirac 0)) := by
  intro h
  have h1 := Measure.IsCondKernel.apply_of_ne_zero ρ₀₁ (Kernel.const ℝ (Measure.dirac 0)) (x := 0)
    (by simp [fst_ρ₀₁]) {1}
  rw [fst_ρ₀₁, Kernel.const_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ ((measurableSet_singleton _).prod (measurableSet_singleton _))] at h1
  simp at h1

open scoped Classical in
-- Every Markov kernel that agrees with `ρ₀₁.condKernel` at the atom `0` disintegrates `ρ₀₁`,
-- whatever its values on the complement of `{0}`, a null set of the first marginal.
theorem isCondKernel_piecewise (ξ : Kernel ℝ ℝ) [IsMarkovKernel ξ] :
    ρ₀₁.IsCondKernel (Kernel.piecewise (measurableSet_singleton (0 : ℝ)) ρ₀₁.condKernel ξ) := by
  constructor
  conv_rhs => rw [← ρ₀₁.disintegrate ρ₀₁.condKernel]
  refine Measure.compProd_congr ?_
  rw [fst_ρ₀₁, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
  simp [Kernel.piecewise_apply]

open scoped Classical in
-- So a conditional kernel is determined only almost everywhere: two Markov kernels that
-- disintegrate `ρ₀₁` differ at `5`.
example : ∃ η η' : Kernel ℝ ℝ, IsMarkovKernel η ∧ IsMarkovKernel η' ∧ ρ₀₁.IsCondKernel η ∧
    ρ₀₁.IsCondKernel η' ∧ η 5 ≠ η' 5 := by
  refine ⟨Kernel.piecewise (measurableSet_singleton (0 : ℝ)) ρ₀₁.condKernel
      (Kernel.const ℝ (Measure.dirac 5)),
    Kernel.piecewise (measurableSet_singleton (0 : ℝ)) ρ₀₁.condKernel
      (Kernel.const ℝ (Measure.dirac 6)),
    inferInstance, inferInstance, isCondKernel_piecewise _, isCondKernel_piecewise _, ?_⟩
  intro h
  have h5 := congrArg (fun μ : Measure ℝ ↦ μ {5}) h
  norm_num [Kernel.piecewise_apply, Measure.dirac_apply' _ (measurableSet_singleton _)] at h5

/-! ### The conditional kernels require a finite measure or a finite kernel -/

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure Measure.count

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Kernel ℝ ℝ :=
  (Measure.count : Measure (ℝ × ℝ)).condKernel

/--
error: failed to synthesize instance of type class
  IsFiniteKernel (Kernel.const Unit Measure.count)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Kernel (Unit × ℝ) ℝ :=
  Kernel.condKernel (Kernel.const Unit (Measure.count : Measure (ℝ × ℝ)))

end

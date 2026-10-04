import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Conditional kernels as almost-everywhere classes

These tests check that the construction with an arbitrary point, `borelMarkovFromReal`, and the
kernels, lemmas, instances, and equations that exposed it are not public; that
`MeasureTheory.Measure.condKernel` and `ProbabilityTheory.Kernel.condKernel` are classes of kernels
modulo null sets, so that no chosen conditional kernel, with its instances and equations, is public;
that finite measures and finite kernels are disintegrated by Markov kernels, that a finite kernel
represents the conditional kernel exactly when it disintegrates, and that a Markov representative
exists; that every representative is determined at atoms, while two representatives may differ on a
null set and the classes reject a kernel that is wrong on a set of positive measure; and that the
conditional kernels still require a finite measure or a finite kernel.
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

/-! ### No chosen conditional kernel is public -/

/-- error: Unknown constant `MeasureTheory.Measure.instIsMarkovKernelCondKernel` -/
#guard_msgs in
#check Measure.instIsMarkovKernelCondKernel

/-- error: Unknown constant `MeasureTheory.Measure.condKernel.instIsCondKernel` -/
#guard_msgs in
#check Measure.condKernel.instIsCondKernel

/-- error: Unknown constant `MeasureTheory.Measure.condKernel_apply_of_ne_zero` -/
#guard_msgs in
#check Measure.condKernel_apply_of_ne_zero

/-- error: Unknown constant `ProbabilityTheory.Kernel.instIsMarkovKernelCondKernel` -/
#guard_msgs in
#check Kernel.instIsMarkovKernelCondKernel

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernel.instIsCondKernel` -/
#guard_msgs in
#check Kernel.condKernel.instIsCondKernel

/-- error: Unknown identifier `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` -/
#guard_msgs in
#check ProbabilityTheory.eq_condKernel_of_measure_eq_compProd

/-- error: Unknown identifier `ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd` -/
#guard_msgs in
#check ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd

/-- error: Unknown identifier `ProbabilityTheory.condKernel_compProd` -/
#guard_msgs in
#check ProbabilityTheory.condKernel_compProd

/-- error: Unknown identifier `ProbabilityTheory.condKernel_const` -/
#guard_msgs in
#check ProbabilityTheory.condKernel_const

/-- error: Unknown constant `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel` -/
#guard_msgs in
#check Kernel.condKernel_apply_eq_condKernel

/-- error: Unknown constant `ProbabilityTheory.Kernel.apply_eq_measure_condKernel_of_compProd_eq` -/
#guard_msgs in
#check Kernel.apply_eq_measure_condKernel_of_compProd_eq

/-- error: Unknown constant `MeasureTheory.Measure.IsCondKernel.ae_eq_real` -/
#guard_msgs in
#check Measure.IsCondKernel.ae_eq_real

/-! ### Classes of disintegrating kernels -/

section General

variable {α β Ω : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra Ω]
  [StandardBorelSpace Ω] [Nonempty Ω]

-- A finite measure on `α × Ω` is disintegrated by a Markov kernel, for every measurable space `α`.
example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η :=
  ρ.exists_isMarkovKernel_isCondKernel

-- `ρ.condKernel` is a class of kernels modulo `ρ.fst`-null sets, and it is represented by such a
-- Markov kernel.
example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : Kernel.AEClass (ae ρ.fst) Ω :=
  ρ.condKernel

example (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ∃ η : Kernel α Ω, IsMarkovKernel η ∧ ρ.IsCondKernel η ∧ η ∈ ρ.condKernel :=
  ρ.exists_isMarkovKernel_mem_condKernel

-- A finite kernel represents `ρ.condKernel` exactly when it disintegrates `ρ`.
example {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] (η : Kernel α Ω) [IsFiniteKernel η] :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η :=
  Measure.mem_condKernel_iff

-- Two representatives agree `ρ.fst`-almost everywhere, and so do two finite kernels that
-- disintegrate `ρ`.
example {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {η η' : Kernel α Ω} (hη : η ∈ ρ.condKernel)
    (hη' : η' ∈ ρ.condKernel) : ∀ᵐ a ∂ρ.fst, η a = η' a :=
  Kernel.AEClass.eventuallyEq_of_mem hη hη'

example {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] (η η' : Kernel α Ω) [IsFiniteKernel η]
    [IsFiniteKernel η'] [ρ.IsCondKernel η] [ρ.IsCondKernel η'] : ∀ᵐ a ∂ρ.fst, η a = η' a :=
  Measure.IsCondKernel.ae_eq η η'

-- Uniqueness needs only a countably generated space of values, not a standard Borel one.
example {γ : Type*} [SigmaAlgebra γ] [SigmaAlgebra.CountablyGenerated γ] {ρ : Measure (α × γ)}
    [IsFiniteMeasure ρ] (η η' : Kernel α γ) [IsFiniteKernel η] [IsFiniteKernel η']
    [ρ.IsCondKernel η] [ρ.IsCondKernel η'] : ∀ᵐ a ∂ρ.fst, η a = η' a :=
  Measure.IsCondKernel.ae_eq η η'

-- A finite kernel `κ : Kernel α (β × Ω)` is disintegrated by a Markov kernel when `α` is countable
-- or `β` is countably generated, and `Kernel.condKernel κ` is the class of these kernels modulo
-- `fst κ a`-null sets in the fiber over every `a`.
example [CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η :=
  κ.exists_isMarkovKernel_isCondKernel

example [CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    Kernel.AEClass (Kernel.fst κ).fiberwiseAE Ω :=
  Kernel.condKernel κ

example [CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    ∃ η : Kernel (α × β) Ω, IsMarkovKernel η ∧ κ.IsCondKernel η ∧ η ∈ Kernel.condKernel κ :=
  Kernel.exists_isMarkovKernel_mem_condKernel κ

example [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
    (η : Kernel (α × β) Ω) [IsFiniteKernel η] : η ∈ Kernel.condKernel κ ↔ κ.IsCondKernel η :=
  Kernel.mem_condKernel_iff

-- The restriction of a representative of `Kernel.condKernel κ` to the fiber over `a` represents
-- the conditional kernel of the measure `κ a`.
example [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
    {η : Kernel (α × β) Ω} (hη : η ∈ Kernel.condKernel κ) (a : α) :
    Kernel.comap η (fun b ↦ (a, b)) measurable_prodMk_left ∈ (κ a).condKernel :=
  Kernel.comap_mem_condKernel_of_mem hη a

-- Two representatives of `Kernel.condKernel κ` agree at `(a, b)` for `fst κ a`-almost every `b`,
-- for every `a`.
example [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
    {η η' : Kernel (α × β) Ω} (hη : η ∈ Kernel.condKernel κ) (hη' : η' ∈ Kernel.condKernel κ)
    (a : α) : ∀ᵐ b ∂(Kernel.fst κ a), η (a, b) = η' (a, b) :=
  Kernel.eventuallyEq_fiberwiseAE_iff.1 (Kernel.AEClass.eventuallyEq_of_mem hη hη') a

-- `Kernel.condKernel` for a countable `α`, with no assumption on `β`, and for a countably generated
-- `β`, with no assumption on `α`.
example (κ : Kernel ℕ (β × Ω)) [IsFiniteKernel κ] : Kernel.AEClass (Kernel.fst κ).fiberwiseAE Ω :=
  Kernel.condKernel κ

example (κ : Kernel α (ℝ × Ω)) [IsFiniteKernel κ] : Kernel.AEClass (Kernel.fst κ).fiberwiseAE Ω :=
  Kernel.condKernel κ

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

-- At the atom `0` of the first marginal every representative of `ρ₀₁.condKernel` is `dirac 1`.
example {η : Kernel ℝ ℝ} (hη : η ∈ ρ₀₁.condKernel) : η 0 = Measure.dirac 1 := by
  obtain ⟨η₀, _, _, hη₀⟩ := ρ₀₁.exists_isMarkovKernel_mem_condKernel
  have h := Kernel.AEClass.eventuallyEq_of_mem hη hη₀
  rw [fst_ρ₀₁, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure] at h
  rw [h]
  ext s hs
  rw [Measure.IsCondKernel.apply_of_ne_zero ρ₀₁ η₀ (x := 0) (by simp [fst_ρ₀₁]) s, fst_ρ₀₁,
    Measure.dirac_apply' _ ((measurableSet_singleton _).prod hs), Measure.dirac_apply' _ hs]
  by_cases h : (1 : ℝ) ∈ s <;> simp [h]

-- The class rejects a kernel that is wrong at the atom, a set of positive measure: the constant
-- kernel `dirac 0` does not represent `ρ₀₁.condKernel`.
theorem const_dirac_zero_not_mem_condKernel :
    Kernel.const ℝ (Measure.dirac 0) ∉ ρ₀₁.condKernel := by
  rw [Measure.mem_condKernel_iff]
  intro h
  have h1 := Measure.IsCondKernel.apply_of_ne_zero ρ₀₁ (Kernel.const ℝ (Measure.dirac 0)) (x := 0)
    (by simp [fst_ρ₀₁]) {1}
  rw [fst_ρ₀₁, Kernel.const_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ ((measurableSet_singleton _).prod (measurableSet_singleton _))] at h1
  simp at h1

open scoped Classical in
-- Every kernel that agrees with a representative of `ρ₀₁.condKernel` at the atom `0` represents
-- it, whatever its values on the complement of `{0}`, a null set of the first marginal.
theorem piecewise_mem_condKernel {η : Kernel ℝ ℝ} (hη : η ∈ ρ₀₁.condKernel) (ξ : Kernel ℝ ℝ) :
    Kernel.piecewise (measurableSet_singleton (0 : ℝ)) η ξ ∈ ρ₀₁.condKernel := by
  refine Kernel.AEClass.mem_of_eventuallyEq hη ?_
  rw [fst_ρ₀₁, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
  simp [Kernel.piecewise_apply]

open scoped Classical in
-- So a conditional kernel is determined only almost everywhere: two Markov representatives of
-- `ρ₀₁.condKernel` differ at `5`.
example : ∃ η η' : Kernel ℝ ℝ, IsMarkovKernel η ∧ IsMarkovKernel η' ∧ η ∈ ρ₀₁.condKernel ∧
    η' ∈ ρ₀₁.condKernel ∧ η 5 ≠ η' 5 := by
  obtain ⟨η, _, -, hη⟩ := ρ₀₁.exists_isMarkovKernel_mem_condKernel
  refine ⟨Kernel.piecewise (measurableSet_singleton (0 : ℝ)) η (Kernel.const ℝ (Measure.dirac 5)),
    Kernel.piecewise (measurableSet_singleton (0 : ℝ)) η (Kernel.const ℝ (Measure.dirac 6)),
    inferInstance, inferInstance, piecewise_mem_condKernel hη _, piecewise_mem_condKernel hη _, ?_⟩
  intro h
  have h5 := congrArg (fun μ : Measure ℝ ↦ μ {5}) h
  norm_num [Kernel.piecewise_apply, Measure.dirac_apply' _ (measurableSet_singleton _)] at h5

-- The same holds in every fiber of the conditional kernel of a kernel: the constant kernel
-- `dirac 0` does not represent the conditional kernel of `Kernel.const Unit ρ₀₁`.
example :
    Kernel.const (Unit × ℝ) (Measure.dirac 0) ∉ Kernel.condKernel (Kernel.const Unit ρ₀₁) :=
  fun h ↦ const_dirac_zero_not_mem_condKernel (Kernel.comap_mem_condKernel_of_mem h ())

/-! ### The conditional kernels require a finite measure or a finite kernel -/

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure Measure.count

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Kernel.AEClass (ae (Measure.count : Measure (ℝ × ℝ)).fst) ℝ :=
  (Measure.count : Measure (ℝ × ℝ)).condKernel

/--
error: failed to synthesize instance of type class
  IsFiniteKernel (Kernel.const Unit Measure.count)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :
    Kernel.AEClass (Kernel.fst (Kernel.const Unit (Measure.count : Measure (ℝ × ℝ)))).fiberwiseAE
      ℝ :=
  Kernel.condKernel (Kernel.const Unit (Measure.count : Measure (ℝ × ℝ)))

end

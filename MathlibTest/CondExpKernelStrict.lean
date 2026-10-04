import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Moments.SubGaussian

/-!
# The conditional expectation kernel as an almost-everywhere class

These tests check that `ProbabilityTheory.condExpKernel μ hm` is the `μ.trim hm`-almost-everywhere
class of the kernels that disintegrate the diagonal law, so that no chosen kernel, with its Markov
instance, measurability lemmas, and defining equations, is public; that a finite kernel represents
it exactly when it disintegrates the diagonal law, that a Markov representative exists, and that
every Markov representative computes conditional probabilities; that conditional independence and
the conditionally sub-Gaussian property are decided by any single representative; that, given the
full σ-algebra, the identity kernel represents the class while a kernel that is wrong at an atom
does not; and that the class requires the proof that `m` is a sub-σ-algebra and a finite measure.
-/

open MeasureTheory ProbabilityTheory SigmaAlgebra

noncomputable section

/-! ### No chosen conditional expectation kernel is public -/

/-- error: Unknown identifier `ProbabilityTheory.instIsMarkovKernelCondExpKernel` -/
#guard_msgs in
#check ProbabilityTheory.instIsMarkovKernelCondExpKernel

/-- error: Unknown identifier `ProbabilityTheory.condExpKernel_eq` -/
#guard_msgs in
#check ProbabilityTheory.condExpKernel_eq

/-- error: Unknown identifier `ProbabilityTheory.condExpKernel_apply_eq_condDistrib` -/
#guard_msgs in
#check ProbabilityTheory.condExpKernel_apply_eq_condDistrib

/-- error: Unknown identifier `ProbabilityTheory.measurable_condExpKernel` -/
#guard_msgs in
#check ProbabilityTheory.measurable_condExpKernel

/-- error: Unknown identifier `ProbabilityTheory.stronglyMeasurable_condExpKernel` -/
#guard_msgs in
#check ProbabilityTheory.stronglyMeasurable_condExpKernel

/-- error: Unknown identifier `ProbabilityTheory.condExpKernel_ae_eq_condExp'` -/
#guard_msgs in
#check ProbabilityTheory.condExpKernel_ae_eq_condExp'

/-- error: Unknown identifier `ProbabilityTheory.integrable_toReal_condExpKernel` -/
#guard_msgs in
#check ProbabilityTheory.integrable_toReal_condExpKernel

/-- error: Unknown identifier `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel'` -/
#guard_msgs in
#check ProbabilityTheory.condExp_ae_eq_integral_condExpKernel'

/-- error: Unknown constant `MeasureTheory.StronglyMeasurable.integral_condExpKernel` -/
#guard_msgs in
#check MeasureTheory.StronglyMeasurable.integral_condExpKernel

/-- error: Unknown constant `MeasureTheory.StronglyMeasurable.integral_condExpKernel'` -/
#guard_msgs in
#check MeasureTheory.StronglyMeasurable.integral_condExpKernel'

/--
error: Unknown identifier `ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`
-/
#guard_msgs in
#check ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight

/-! ### Representatives of the class -/

section Class

variable {Ω : Type*} {m m₁ m₂ : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

example (hm : m ≤ mΩ) : @Kernel.AEClass Ω (ae (μ.trim hm)) Ω m mΩ :=
  condExpKernel μ hm

example (hm : m ≤ mΩ) : ∃ η : @Kernel Ω Ω m mΩ, IsMarkovKernel η ∧ η ∈ condExpKernel μ hm :=
  exists_isMarkovKernel_mem_condExpKernel μ hm

-- A finite kernel represents the class exactly when it disintegrates the diagonal law.
example (hm : m ≤ mΩ) (η : @Kernel Ω Ω m mΩ) [IsFiniteKernel η] :
    η ∈ condExpKernel μ hm ↔
      (μ.trim hm) ⊗ₘ η
        = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ (aemeasurable_diag_of_le μ hm) :=
  mem_condExpKernel_iff

-- Every Markov representative computes conditional probabilities and integrates back to `μ`.
example (hm : m ≤ mΩ) {η : @Kernel Ω Ω m mΩ} [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm)
    {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω ↦ (η ω).real s) =ᵐ[μ] μ⟦s | m⟧ :=
  condExpKernel_ae_eq_condExp hη hs

example (hm : m ≤ mΩ) {η : @Kernel Ω Ω m mΩ} [IsMarkovKernel η] (hη : η ∈ condExpKernel μ hm) :
    η ∘ₘ μ.trim hm = μ :=
  condExpKernel_comp_trim hη

-- Conditional independence and the conditionally sub-Gaussian property are decided by any single
-- representative.
example (hm : m ≤ mΩ) {η : @Kernel Ω Ω m mΩ}
    (hη : η ∈ condExpKernel μ hm) :
    CondIndep m m₁ m₂ hm μ ↔ Kernel.Indep m₁ m₂ η (μ.trim hm) :=
  condIndep_iff_of_mem hη

example (hm : m ≤ mΩ) {η η' : @Kernel Ω Ω m mΩ}
    (hη : η ∈ condExpKernel μ hm) (hη' : η' ∈ condExpKernel μ hm) :
    Kernel.Indep m₁ m₂ η (μ.trim hm) ↔ Kernel.Indep m₁ m₂ η' (μ.trim hm) :=
  (condIndep_iff_of_mem hη).symm.trans (condIndep_iff_of_mem hη')

example (hm : m ≤ mΩ) {X : Ω → ℝ} {c : NNReal} {η : @Kernel Ω Ω m mΩ}
    (hη : η ∈ condExpKernel μ hm) :
    HasCondSubgaussianMGF m hm X c μ ↔ Kernel.HasSubgaussianMGF X c η (μ.trim hm) :=
  hasCondSubgaussianMGF_iff_of_mem hη

end Class

/-! ### Conditional independence and conditional distributions -/

section CondDistrib

variable {Ω β β' γ : Type*} [SigmaAlgebra Ω] [StandardBorelSpace Ω] [SigmaAlgebra β]
  [StandardBorelSpace β] [Nonempty β] [SigmaAlgebra β'] [StandardBorelSpace β'] [Nonempty β']
  [SigmaAlgebra γ] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → β'} {k : Ω → γ}

-- `g` is conditionally independent of `f` given `k` exactly when a Markov representative of the
-- conditional distribution of `f` given `k`, viewed as a kernel that ignores `g`, represents the
-- conditional distribution of `f` given `(k, g)`.
example (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) {η : Kernel γ β}
    [IsMarkovKernel η] (hη : η ∈ condDistrib f k μ) :
    g ⟂ᵢ[k, hk; μ] f ↔ η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ :=
  condIndepFun_iff_prodMkRight_mem_condDistrib hf hg hk hη

end CondDistrib

/-! ### Conditioning on the full σ-algebra -/

-- Given the full σ-algebra, the identity kernel represents the class, and the constant kernel
-- `dirac 1`, which is wrong at the atom of `dirac 0`, does not.
theorem id_mem_condExpKernel_dirac : Kernel.id ∈ condExpKernel (Measure.dirac (0 : ℝ)) le_rfl := by
  rw [mem_condExpKernel_iff, trim_eq_self, Measure.compProd_id_eq_copy_comp]
  exact Measure.deterministic_comp_eq_map _

example : Kernel.const ℝ (Measure.dirac 1) ∉ condExpKernel (Measure.dirac (0 : ℝ)) le_rfl := by
  intro h
  have h' := Kernel.AEClass.eventuallyEq_of_mem h id_mem_condExpKernel_dirac
  rw [trim_eq_self, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure] at h'
  have h1 := congrArg (fun ν : Measure ℝ ↦ ν {0}) h'
  simp [Kernel.const_apply, Kernel.id_apply, Measure.dirac_apply'] at h1

/-! ### The class requires a sub-σ-algebra and a finite measure -/

-- The sub-σ-algebra is given by the proof that it is one: the former call with the σ-algebra
-- itself is rejected.
set_option pp.mvars false in
/--
error: Application type mismatch: The argument
  ⊥
has type
  SigmaAlgebra ℝ
of sort `Type` but is expected to have type
  ?_ ≤ Real.sigmaAlgebra
of sort `Prop` in the application
  condExpKernel (Measure.dirac 0) ⊥
-/
#guard_msgs in
example : True :=
  let _c := condExpKernel (Measure.dirac (0 : ℝ)) (⊥ : SigmaAlgebra ℝ)
  trivial

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure Measure.count

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Kernel.AEClass (ae ((Measure.count : Measure ℝ).trim le_rfl)) ℝ :=
  condExpKernel Measure.count le_rfl

end

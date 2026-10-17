import Mathlib.Probability.Independence.ConditionalKernel
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional independence on its domain

These tests check that conditional independence and the conditionally sub-Gaussian property are
stated with conditional expectations, for every finite measure on every measurable space, without a
standard Borel space or a conditional expectation kernel; that conditional independence carries the
null-measurability of the sets whose conditional probabilities it compares and needs a finite
measure; that the π-system lemmas, Kolmogorov's zero-one law, and the sum of conditionally
sub-Gaussian variables hold on every space; and that the characterizations through the conditional
expectation kernel hold under the class of the joint law of `(ω, ω)`.
-/

open MeasureTheory ProbabilityTheory SigmaAlgebra

noncomputable section

/-! ### Every finite measure on every measurable space -/

section AnySpace

variable {Ω β β' : Type*} {m' m₁ m₂ : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] {hm' : m' ≤ mΩ}
  [SigmaAlgebra β] [SigmaAlgebra β'] {μ : Measure Ω} [IsFiniteMeasure μ]

-- The definition is the factorization of the conditional probabilities.
example (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ) (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ t₁ t₂, t₁ ∈ m₁ → t₂ ∈ m₂ →
      μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧ :=
  condIndep_iff m' m₁ m₂ hm' μ hm₁ hm₂

-- Conditional independence carries the null-measurability of its sets and functions.
example (h : CondIndep m' m₁ m₂ hm' μ) : ∀ s ∈ m₁, NullMeasurableSet s μ :=
  h.nullMeasurableSet_left

example {X : Ω → β} {Y : Ω → β'} (h : CondIndepFun m' hm' X Y μ) : NullMeasurable Y μ :=
  h.nullMeasurable_right

example {s t : Set Ω} (h : CondIndepSet m' hm' s t μ) : NullMeasurableSet s μ :=
  h.nullMeasurableSet_left

-- An `m'`-measurable random variable is conditionally independent of every null-measurable one.
example {X : Ω → β} {Y : Ω → β'} (hX : Measurable[m'] X) (hY : NullMeasurable Y μ) :
    CondIndepFun m' hm' X Y μ :=
  condIndepFun_of_measurable_left hX hY

-- A constant is conditionally independent of every null-measurable random variable.
example (c : β) {Y : Ω → β'} (hY : NullMeasurable Y μ) :
    CondIndepFun m' hm' (fun _ ↦ c) Y μ :=
  condIndepFun_const_left c hY

-- The π-system lemmas need no measurability beyond the domain of their premises.
example {p₁ p₂ : Set (Set Ω)} (hp₁ : IsPiSystem p₁) (hp₂ : IsPiSystem p₂)
    (h : CondIndepSets m' hm' p₁ p₂ μ) :
    CondIndep m' (generateFrom p₁) (generateFrom p₂) hm' μ :=
  h.condIndep' hp₁ hp₂

example {ι : Type*} {m : ι → SigmaAlgebra Ω} (π : ι → Set (Set Ω))
    (h_pi : ∀ i, IsPiSystem (π i)) (h_gen : ∀ i, m i = generateFrom (π i))
    (h : iCondIndepSets m' hm' π μ) :
    iCondIndep m' hm' m μ :=
  h.iCondIndep m π h_pi h_gen

-- Families of sets are conditionally independent exactly when their singletons are.
example {ι : Type*} (s : ι → Set Ω) :
    iCondIndepSet m' hm' s μ ↔ iCondIndepSets m' hm' (fun i ↦ {s i}) μ :=
  iCondIndepSet_iff_iCondIndepSets_singleton m' hm' s μ

-- Kolmogorov's zero-one law given a σ-algebra.
example {s : ℕ → SigmaAlgebra Ω} (h : iCondIndep m' hm' s μ) {t : Set Ω}
    (ht : t ∈ Filter.limsup s Filter.atTop) :
    ∀ᵐ ω ∂μ, (μ⟦t | m'⟧) ω = 0 ∨ (μ⟦t | m'⟧) ω = 1 :=
  condExp_zero_or_one_of_measurableSet_limsup_atTop hm' h ht

-- A sub-Gaussian `m'`-measurable variable plus a conditionally sub-Gaussian one is sub-Gaussian.
example {X Y : Ω → ℝ} {cX cY : NNReal} (hX : HasSubgaussianMGF X cX (μ.trim hm'))
    (hY : HasCondSubgaussianMGF m' hm' Y cY μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ :=
  hX.add_of_hasCondSubgaussianMGF hm' hY

-- The conditionally sub-Gaussian property is stated with conditional expectations.
example {X : Ω → ℝ} {c : NNReal} (h : HasCondSubgaussianMGF m' hm' X c μ) (t : ℝ) :
    ∀ᵐ ω ∂μ, (μ[fun ω ↦ Real.exp (t * X ω) | m']) ω ≤ Real.exp (c * t ^ 2 / 2) :=
  h.ae_condExp_le t

end AnySpace

-- The integrability of `exp (0 * X) = 1` makes the measure of a conditionally sub-Gaussian
-- variable finite, so the property and the sum lemma need no finiteness assumption.
example {Ω : Type*} {m' : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] {hm' : m' ≤ mΩ} {μ : Measure Ω}
    {X : Ω → ℝ} {c : NNReal} (h : HasCondSubgaussianMGF m' hm' X c μ) : IsFiniteMeasure μ :=
  h.isFiniteMeasure

example {Ω : Type*} {m' : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] {hm' : m' ≤ mΩ} {μ : Measure Ω}
    {X Y : Ω → ℝ} {cX cY : NNReal} (hX : HasSubgaussianMGF X cX (μ.trim hm'))
    (hY : HasCondSubgaussianMGF m' hm' Y cY μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ :=
  hX.add_of_hasCondSubgaussianMGF hm' hY

/-! ### Conditional independence needs a finite measure -/

/--
error: failed to synthesize instance of type class
  IsFiniteMeasure ℙ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Prop := CondIndep (⊥ : SigmaAlgebra ℝ) ⊥ ⊥ bot_le (volume : Measure ℝ)

/-! ### Characterizations through the conditional expectation kernel -/

section Kernel

variable {Ω : Type*} {m' m₁ m₂ : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω] {hm' : m' ≤ mΩ}
  {μ : Measure Ω} [IsFiniteMeasure μ] [(condExpJointLaw μ hm').HasUniqueCondKernel]

-- With the class of the joint law, conditional independence of σ-algebras of null-measurable
-- sets is independence with respect to any representative of the conditional expectation kernel.
example {η : @Kernel Ω Ω m' mΩ} (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) (hη : η ∈ condExpKernel μ hm') :
    CondIndep m' m₁ m₂ hm' μ ↔ Kernel.Indep m₁ m₂ η (μ.trim hm') :=
  condIndep_iff_of_mem hm₁ hm₂ hη

-- The conditionally sub-Gaussian bound then holds almost surely for all `t` at once.
example {X : Ω → ℝ} {c : NNReal} (h : HasCondSubgaussianMGF m' hm' X c μ)
    {η : @Kernel Ω Ω m' mΩ} (hη : η ∈ condExpKernel μ hm') :
    ∀ᵐ ω' ∂(μ.trim hm'), ∀ t, mgf X (η ω') t ≤ Real.exp (c * t ^ 2 / 2) :=
  h.mgf_le hη

end Kernel

-- For a finite measure and the σ-algebra generated by one set, instance search supplies the class
-- on every space, and conditional independence of null-measurable sets is kernel independence.
example {Ω : Type*} [mΩ : SigmaAlgebra Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {t u : Set Ω} (ht : NullMeasurableSet t μ)
    (hu : NullMeasurableSet u μ) {η : @Kernel Ω Ω (generateFrom {s}) mΩ}
    (hη : η ∈ condExpKernel μ (generateFrom_singleton_le hs)) :
    CondIndepSet (generateFrom {s}) (generateFrom_singleton_le hs) t u μ ↔
      Kernel.IndepSet t u η (μ.trim (generateFrom_singleton_le hs)) :=
  condIndepSet_iff_of_mem ht hu hη

end

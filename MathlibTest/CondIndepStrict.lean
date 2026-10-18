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
sub-Gaussian variables hold on every space; that the characterizations through the conditional
expectation kernel hold under the class of the joint law of `(ω, ω)`; and that those through the
conditional distributions given a random variable hold on every space for almost everywhere
measurable random variables under the classes of the joint laws they involve, which instance search
supplies for nonempty standard Borel value spaces. They also check that exactly the sub-σ-algebras
of `eventuallySigmaAlgebra m' (ae μ)`, whose sets are almost everywhere equal to sets of `m'`, and
exactly the random variables that are `EventuallyMeasurable m' (ae μ)` are conditionally independent
given `m'` of every σ-algebra of null-measurable sets and every null-measurable random variable, a
class that can be strictly larger than that of sub-σ-algebras of `m'`.
-/

open MeasureTheory ProbabilityTheory SigmaAlgebra

noncomputable section

/-! ### Every finite measure on every measurable space -/

section AnySpace

variable {Ω β β' : Type*} {m' m₁ m₂ m₃ m₄ : SigmaAlgebra Ω} [mΩ : SigmaAlgebra Ω]
  {hm' : m' ≤ mΩ} [SigmaAlgebra β] [SigmaAlgebra β'] {μ : Measure Ω} [IsFiniteMeasure μ]

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

-- So is one almost everywhere equal to an `m'`-measurable random variable, and exactly the random
-- variables that are `EventuallyMeasurable m' (ae μ)` are conditionally independent given `m'` of
-- every null-measurable one.
example {X X' : Ω → β} {Y : Ω → β'} (hX' : Measurable[m'] X') (hXX' : X =ᵐ[μ] X')
    (hY : NullMeasurable Y μ) : CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_measurable_left hX' hY).congr hXX'.symm .rfl

example {X : Ω → β} {Y : Ω → β'} (hX : EventuallyMeasurable m' (ae μ) X)
    (hY : NullMeasurable Y μ) : CondIndepFun m' hm' X Y μ :=
  condIndepFun_of_eventuallyMeasurable_left hX hY

example {X : Ω → β} {Y : Ω → β'} (hX : NullMeasurable X μ)
    (hY : EventuallyMeasurable m' (ae μ) Y) : CondIndepFun m' hm' X Y μ :=
  condIndepFun_of_eventuallyMeasurable_right hX hY

example {X : Ω → β} (h : CondIndepFun m' hm' X X μ) : EventuallyMeasurable m' (ae μ) X :=
  fun _ hB ↦ condIndep_self_iff.1 h ⟨_, hB, rfl⟩

-- A σ-algebra whose sets are almost everywhere equal to sets of `m'` is conditionally independent
-- given `m'` of every σ-algebra of null-measurable sets, and this condition is exact.
example (hm₁ : m₁ ≤ eventuallySigmaAlgebra m' (ae μ)) (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ :=
  condIndep_of_le_eventuallySigmaAlgebra_left hm₁ hm₂

example (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ) (hm₂ : m₂ ≤ eventuallySigmaAlgebra m' (ae μ)) :
    CondIndep m' m₁ m₂ hm' μ :=
  condIndep_of_le_eventuallySigmaAlgebra_right hm₁ hm₂

example : CondIndep m' m₁ m₁ hm' μ ↔ m₁ ≤ eventuallySigmaAlgebra m' (ae μ) :=
  condIndep_self_iff

-- Conditional independence passes to σ-algebras whose sets are almost everywhere equal to sets of
-- conditionally independent ones.
example (h : CondIndep m' m₁ m₂ hm' μ) (h₃ : m₃ ≤ eventuallySigmaAlgebra m₁ (ae μ))
    (h₄ : m₄ ≤ eventuallySigmaAlgebra m₂ (ae μ)) : CondIndep m' m₃ m₄ hm' μ :=
  h.of_le_eventuallySigmaAlgebra h₃ h₄

-- A null-measurable set has conditional probability `0` or `1` almost everywhere exactly when it is
-- almost everywhere equal to a set of `m'`.
example {t : Set Ω} (ht : NullMeasurableSet t μ) :
    (∀ᵐ ω ∂μ, (μ⟦t | m'⟧) ω = 0 ∨ (μ⟦t | m'⟧) ω = 1) ↔ t ∈ eventuallySigmaAlgebra m' (ae μ) :=
  ae_condExp_eq_zero_or_one_iff hm' ht

-- The σ-algebra generated by a null set is conditionally independent given the trivial σ-algebra
-- of every σ-algebra of null-measurable sets, although it need not be contained in it.
example {N : Set Ω} (hN : μ N = 0) (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep ⊥ (generateFrom {N}) m₂ bot_le μ :=
  condIndep_of_le_eventuallySigmaAlgebra_left (generateFrom_le fun _ ht ↦
    (Set.mem_singleton_iff.1 ht) ▸ ⟨∅, (⊥ : SigmaAlgebra Ω).empty_mem, ae_eq_empty.2 hN⟩) hm₂

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

-- Kolmogorov's zero-one law given a σ-algebra, set by set and for the tail σ-algebra itself.
example {s : ℕ → SigmaAlgebra Ω} (h : iCondIndep m' hm' s μ) {t : Set Ω}
    (ht : t ∈ Filter.limsup s Filter.atTop) :
    ∀ᵐ ω ∂μ, (μ⟦t | m'⟧) ω = 0 ∨ (μ⟦t | m'⟧) ω = 1 :=
  condExp_zero_or_one_of_measurableSet_limsup_atTop hm' h ht

example {s : ℕ → SigmaAlgebra Ω} (h : iCondIndep m' hm' s μ) :
    Filter.limsup s Filter.atTop ≤ eventuallySigmaAlgebra m' (ae μ) :=
  limsup_atTop_le_eventuallySigmaAlgebra_of_iCondIndep hm' h

example {s : ℤ → SigmaAlgebra Ω} (h : iCondIndep m' hm' s μ) :
    Filter.limsup s Filter.atBot ≤ eventuallySigmaAlgebra m' (ae μ) :=
  limsup_atBot_le_eventuallySigmaAlgebra_of_iCondIndep hm' h

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

/-! ### Sub-σ-algebras of the conditioning σ-algebra up to null sets -/

-- On `Bool` with the Dirac mass at `true`, the null set `{false}` generates a σ-algebra that is not
-- contained in the trivial σ-algebra, but is conditionally independent given it of every σ-algebra.
example : ¬ generateFrom {({false} : Set Bool)} ≤ ⊥ := by
  intro h
  rcases mem_bot_iff.1 (h (mem_generateFrom (Set.mem_singleton _))) with h' | h'
  · exact absurd (h' ▸ Set.mem_singleton false) (Set.notMem_empty false)
  · have : true ∈ ({false} : Set Bool) := h' ▸ Set.mem_univ true
    simp at this

example : CondIndep ⊥ (generateFrom {({false} : Set Bool)}) ⊤ bot_le (Measure.dirac true) := by
  refine condIndep_of_le_eventuallySigmaAlgebra_left (generateFrom_le fun _ ht ↦
    (Set.mem_singleton_iff.1 ht) ▸ ⟨∅, (⊥ : SigmaAlgebra Bool).empty_mem, ae_eq_empty.2 ?_⟩) ?_
  · simp
  · exact fun s _ ↦ (Set.toFinite s).measurableSet.nullMeasurableSet

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

/-! ### Characterizations through conditional distributions -/

section CondDistrib

variable {Ω β β' γ : Type*} [SigmaAlgebra Ω] [SigmaAlgebra β] [SigmaAlgebra β'] [SigmaAlgebra γ]
  {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → β'} {k : Ω → γ}

-- On every space, almost everywhere measurable `f` and `g` are conditionally independent given `k`
-- exactly when the joint law of `(k, f, g)` factors through their conditional distributions given
-- `k`, which need only the classes of the joint laws of `(k, f)` and `(k, g)`.
example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : Measurable k)
    [(μ.map (fun ω ↦ (k ω, f ω)) (hk.aemeasurable.prodMk hf)).HasUniqueCondKernel]
    [(μ.map (fun ω ↦ (k ω, g ω)) (hk.aemeasurable.prodMk hg)).HasUniqueCondKernel]
    {η₁ : Kernel γ β} [IsMarkovKernel η₁] (hη₁ : η₁ ∈ condDistrib f k μ) {η₂ : Kernel γ β'}
    [IsMarkovKernel η₂] (hη₂ : η₂ ∈ condDistrib g k μ) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.aemeasurable.prodMk (hf.prodMk hg)) =
        (Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable :=
  condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hf hg hk hη₁ hη₂

-- `g` is conditionally independent of `f` given `k` exactly when a Markov representative of the
-- conditional distribution of `f` given `k`, viewed as a kernel that ignores `g`, represents the
-- conditional distribution of `f` given `(k, g)`; only the classes of the joint laws of `(k, f)`
-- and `((k, g), f)` are needed.
example (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : Measurable k)
    [(μ.map (fun ω ↦ (k ω, f ω)) (hk.aemeasurable.prodMk hf)).HasUniqueCondKernel]
    [(μ.map (fun ω ↦ ((k ω, g ω), f ω))
      ((hk.aemeasurable.prodMk hg).prodMk hf)).HasUniqueCondKernel]
    {η : Kernel γ β} [IsMarkovKernel η] (hη : η ∈ condDistrib f k μ) :
    g ⟂ᵢ[k, hk; μ] f ↔ η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ :=
  condIndepFun_iff_prodMkRight_mem_condDistrib hf hg hk hη

-- For nonempty standard Borel value spaces, instance search supplies the classes, and measurable
-- random variables apply through `Measurable.aemeasurable`.
example [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) {η₁ : Kernel γ β}
    [IsMarkovKernel η₁] (hη₁ : η₁ ∈ condDistrib f k μ) {η₂ : Kernel γ β'} [IsMarkovKernel η₂]
    (hη₂ : η₂ ∈ condDistrib g k μ) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω ↦ (k ω, f ω, g ω)) (hk.prodMk (hf.prodMk hg)).aemeasurable =
        (Kernel.id ×ₖ (η₁ ×ₖ η₂)) ∘ₘ μ.map k hk.aemeasurable :=
  condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hf.aemeasurable hg.aemeasurable
    hk hη₁ hη₂

example [StandardBorelSpace β] [Nonempty β] (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) {η : Kernel γ β} [IsMarkovKernel η] (hη : η ∈ condDistrib f k μ) :
    g ⟂ᵢ[k, hk; μ] f ↔ η.prodMkRight β' ∈ condDistrib f (fun ω ↦ (k ω, g ω)) μ :=
  condIndepFun_iff_prodMkRight_mem_condDistrib hf.aemeasurable hg.aemeasurable hk hη

end CondDistrib

end

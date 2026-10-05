import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Moments.SubGaussian

/-!
# Tonelli's theorem on the exact domain of the composition-product

These tests check that Tonelli's theorem for `μ ⊗ₘ κ`, `κ ⊗ₖ η`, `κ ∥ₖ η` and `κ ×ₖ η` holds on
the domains `μ.HasCompProd κ`, `κ.HasCompProd η`, `κ.HasParallelComp η` and
`κ.HasCompProd (prodMkRight β η)`, not only for s-finite inputs, with examples against counting
measure on `ℝ` and the constant kernel of counting measure, which are not s-finite. The section
integrals of a measurable function have a measurable majorant with the same integral, and a
function that need not be measurable integrates against `μ ⊗ₘ κ` to at most its iterated
integral. Instance search closes the domain of `μ ⊗ₘ κ` under finite and countable sums and
multiples of the measure and under finite and countable sums of the kernel; the domain is not closed
under uncountable sums, whose domain is an assumption of `compProd_sum_left`. The additivity,
associativity, and rectangle lemmas hold on the domains, the rectangle lemmas also for sets that are
not measurable, as do consumers such as `comp_compProd_comm` and the Lebesgue integrals against a
conditional kernel.
-/

open MeasureTheory Measure Set
open ProbabilityTheory (Kernel IsSFiniteKernel IsMarkovKernel)
open scoped ProbabilityTheory ENNReal

noncomputable section

variable {α β γ δ : Type*} [SigmaAlgebra α] [SigmaAlgebra β] [SigmaAlgebra γ] [SigmaAlgebra δ]

/-! ### Tonelli's theorem on the domain -/

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ :=
  lintegral_compProd hf

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ (fun a ↦ ∫⁻ b, f (a, b) ∂κ a) ≤ g ∧
      ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ = ∫⁻ a, g a ∂μ :=
  HasCompProd.exists_measurable_ge_lintegral_lintegral_eq hf

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {f : α × β → ℝ≥0∞}
    (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂κ a ∂μ :=
  setLIntegral_compProd hf hs ht

-- Functions that need not be measurable.
example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] (f : α × β → ℝ≥0∞) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) ≤ ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ :=
  lintegral_compProd_le f

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] {f g : α × β → ℝ≥0∞}
    (hg : Measurable g) (hfg : f ≤ g) (h_eq : ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ x, g x ∂(μ ⊗ₘ κ)) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ :=
  lintegral_compProd_of_exists_measurable_ge ⟨g, hg, hfg, h_eq⟩

-- Counting measure on `ℝ` is not s-finite.
example {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂((count : Measure ℝ) ⊗ₘ Kernel.const ℝ (dirac 0)) = ∑' a, f (a, 0) := by
  rw [lintegral_compProd hf, lintegral_count]
  simp

-- The constant kernel of counting measure on `ℝ` is not s-finite.
example {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(dirac (0 : ℝ) ⊗ₘ Kernel.const ℝ (count : Measure ℝ)) = ∑' b, f (0, b) := by
  rw [lintegral_compProd hf, lintegral_dirac]
  simp [lintegral_count]

example (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α) {f : β × γ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a :=
  Kernel.lintegral_compProd κ η a hf

example (κ : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] (a : α) {f : β × γ → ℝ≥0∞}
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) {t : Set γ} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(κ ⊗ₖ η) a = ∫⁻ b in s, ∫⁻ c in t, f (b, c) ∂η (a, b) ∂κ a :=
  Kernel.setLIntegral_compProd κ η a hf hs ht

example (κ : Kernel α β) (η : Kernel γ δ) [κ.HasParallelComp η] (x : α × γ)
    {f : β × δ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(κ ∥ₖ η) x = ∫⁻ b, ∫⁻ d, f (b, d) ∂η x.2 ∂κ x.1 :=
  Kernel.lintegral_parallelComp x hf

example (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (Kernel.prodMkRight β η)] (a : α)
    {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η a ∂κ a :=
  Kernel.lintegral_prod κ η a hf

/-! ### Rectangles, also when the sides are not measurable -/

example (μ : Measure α) (ν : Measure β) [μ.HasCompProd (Kernel.const α ν)] (s : Set α)
    (t : Set β) :
    (μ ⊗ₘ Kernel.const α ν) (s ×ˢ t) = μ s * ν t :=
  compProd_const_apply_prod s t

example (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (Kernel.prodMkRight β η)] (a : α)
    (s : Set β) (t : Set γ) :
    (κ ×ₖ η) a (s ×ˢ t) = κ a s * η a t :=
  Kernel.prod_apply_prod

example (κ : Kernel α β) (η : Kernel γ δ) [κ.HasParallelComp η] (x : α × γ) (s : Set β)
    (t : Set δ) :
    (κ ∥ₖ η) x (s ×ˢ t) = κ x.1 s * η x.2 t :=
  Kernel.parallelComp_apply_prod s t

-- The constant kernel of counting measure on `ℝ` is not s-finite.
example :
    (dirac (0 : ℝ) ⊗ₘ Kernel.const ℝ (count : Measure ℝ)) ({0} ×ˢ {1}) = 1 := by
  rw [compProd_const_apply_prod]
  simp

example (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (Kernel.prodMkRight β η)]
    [IsMarkovKernel η] :
    Kernel.fst (κ ×ₖ η) = κ := by
  simp

example (κ : Kernel α β) (η : Kernel α γ) [κ.HasCompProd (Kernel.prodMkRight β η)]
    [IsMarkovKernel κ] :
    Kernel.snd (κ ×ₖ η) = η := by
  simp

/-! ### Closure of the domain -/

example (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd κ] :
    (μ + ν).HasCompProd κ := inferInstance

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] (c : ℝ≥0∞) :
    (c • μ).HasCompProd κ := inferInstance

example (μ : ℕ → Measure α) (κ : Kernel α β) [∀ n, (μ n).HasCompProd κ] :
    (sum μ).HasCompProd κ := inferInstance

example (μ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [μ.HasCompProd η] :
    μ.HasCompProd (κ + η) := inferInstance

example (μ : Measure α) (κ : ℕ → Kernel α β) [∀ n, μ.HasCompProd (κ n)] :
    μ.HasCompProd (Kernel.sum κ) := inferInstance

example (κ κ' : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] [κ'.HasCompProd η] :
    (κ + κ').HasCompProd η := inferInstance

example (κ : ℕ → Kernel α β) (η : Kernel (α × β) γ) [∀ n, (κ n).HasCompProd η] :
    (Kernel.sum κ).HasCompProd η := inferInstance

-- The sums need the domains of both summands.
/--
error: failed to synthesize instance of type class
  (μ + ν).HasCompProd κ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] :
    (μ + ν).HasCompProd κ := inferInstance

/--
error: failed to synthesize instance of type class
  μ.HasCompProd (κ + η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] :
    μ.HasCompProd (κ + η) := inferInstance

/--
error: failed to synthesize instance of type class
  (κ + κ').HasCompProd η

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (κ κ' : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] :
    (κ + κ').HasCompProd η := inferInstance

example (μ : Measure α) (κ : Kernel α β) (η : Kernel (α × β) γ) [μ.HasCompProd κ]
    [κ.HasCompProd η] [(μ ⊗ₘ κ).HasCompProd η] :
    μ.HasCompProd (κ ⊗ₖ η) := inferInstance

example (μ : Measure α) (κ : Kernel α β) (η : Kernel (α × β) γ) [μ.HasCompProd κ]
    [κ.HasCompProd η] [IsSFiniteKernel η] :
    μ.HasCompProd (κ ⊗ₖ η) := inferInstance

-- The domain is not closed under uncountable sums (paper proof): for a set `T ⊆ ℝ` that is not
-- Borel, every `dirac t` has a composition-product with the constant kernel of
-- `Σ_{u ∉ T} dirac u`, but against `Σ_{t ∈ T} dirac t` the measures of the sections of the diagonal
-- form the indicator of `Tᶜ`, whose integral is `0` while a measurable majorant vanishing on `T`
-- would make `T` Borel.
/--
error: failed to synthesize instance of type class
  (sum μ).HasCompProd κ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {ι : Type*} (μ : ι → Measure α) (κ : Kernel α β) [∀ i, (μ i).HasCompProd κ] :
    (sum μ).HasCompProd κ := inferInstance

-- The instance for `μ.HasCompProd (κ ⊗ₖ η)` needs the domain of `(μ ⊗ₘ κ) ⊗ₘ η`, without which the
-- conclusion can fail (`MeasureTheory.Measure.hasCompProd_compProd`).
/--
error: failed to synthesize instance of type class
  μ.HasCompProd (κ ⊗ₖ η)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (μ : Measure α) (κ : Kernel α β) (η : Kernel (α × β) γ) [μ.HasCompProd κ]
    [κ.HasCompProd η] :
    μ.HasCompProd (κ ⊗ₖ η) := inferInstance

/-! ### Additivity and associativity on the domain -/

example (μ ν : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] [ν.HasCompProd κ] :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ :=
  compProd_add_left μ ν κ

example (μ : Measure α) (κ η : Kernel α β) [μ.HasCompProd κ] [μ.HasCompProd η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η :=
  compProd_add_right μ κ η

example (μ : Measure α) (κ : Kernel α β) [μ.HasCompProd κ] (c : ℝ≥0∞) :
    (c • μ) ⊗ₘ κ = c • (μ ⊗ₘ κ) :=
  compProd_smul_left c

example {ι : Type*} (μ : ι → Measure α) (κ : Kernel α β) [∀ i, (μ i).HasCompProd κ]
    [(sum μ).HasCompProd κ] :
    (sum μ) ⊗ₘ κ = sum fun i ↦ μ i ⊗ₘ κ :=
  compProd_sum_left

example (μ : Measure α) (κ : ℕ → Kernel α β) [∀ n, μ.HasCompProd (κ n)] :
    μ ⊗ₘ Kernel.sum κ = sum fun n ↦ μ ⊗ₘ κ n :=
  compProd_sum_right

example (κ κ' : Kernel α β) (η : Kernel (α × β) γ) [κ.HasCompProd η] [κ'.HasCompProd η] :
    (κ + κ') ⊗ₖ η = κ ⊗ₖ η + κ' ⊗ₖ η :=
  Kernel.compProd_add_left κ κ' η

example (κ : ℕ → Kernel α β) (η : Kernel (α × β) γ) [∀ n, (κ n).HasCompProd η] :
    Kernel.sum κ ⊗ₖ η = Kernel.sum fun n ↦ κ n ⊗ₖ η :=
  Kernel.compProd_sum_left

-- Neither counting measure on `ℝ` nor the constant kernel of counting measure is s-finite.
example :
    ((count : Measure ℝ) + dirac 0) ⊗ₘ Kernel.const ℝ (count : Measure ℝ) =
      count ⊗ₘ Kernel.const ℝ count + dirac 0 ⊗ₘ Kernel.const ℝ count :=
  compProd_add_left _ _ _

example (μ : Measure α) (κ : Kernel α β) (η : Kernel (α × β) γ) [μ.HasCompProd κ]
    [κ.HasCompProd η] [(μ ⊗ₘ κ).HasCompProd η] :
    (μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm = μ ⊗ₘ κ ⊗ₘ η :=
  compProd_assoc

-- Counting measure on `ℝ` is not s-finite.
example (κ : Kernel ℝ β) [IsSFiniteKernel κ] (η : Kernel (ℝ × β) γ) [IsSFiniteKernel η] :
    ((count : Measure ℝ) ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm =
      count ⊗ₘ κ ⊗ₘ η :=
  compProd_assoc

-- The simp lemmas apply on the domains.
example (κ : Kernel ℝ β) [IsSFiniteKernel κ] (η : Kernel (ℝ × β) γ) [IsSFiniteKernel η] :
    ((count : Measure ℝ) ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm =
      count ⊗ₘ κ ⊗ₘ η := by
  simp

example (κ : Kernel α β) (η : Kernel γ δ) [κ.HasParallelComp η] (x : α × γ) :
    (κ ∥ₖ η) x univ = κ x.1 univ * η x.2 univ := by
  simp

/-! ### Consumers on the domains -/

example (μ : Measure α) (κ : Kernel α β) (η : Kernel (α × β) γ) [μ.HasCompProd κ]
    [κ.HasCompProd η] :
    η ∘ₘ (μ ⊗ₘ κ) = ((κ ⊗ₖ η) ∘ₘ μ).snd :=
  comp_compProd_comm

-- Counting measure on `ℝ` is not s-finite.
example (κ : Kernel ℝ β) [IsSFiniteKernel κ] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ((count : Measure ℝ).withDensity f) ⊗ₘ κ = (count ⊗ₘ κ).withDensity (fun p ↦ f p.1) :=
  withDensity_compProd hf

example (κ : Kernel ℝ β) [IsSFiniteKernel κ] {g : ℝ → β → ℝ≥0∞}
    [IsSFiniteKernel (κ.withDensity g)] (hg : Measurable (Function.uncurry g)) :
    (count : Measure ℝ) ⊗ₘ (κ.withDensity g) = (count ⊗ₘ κ).withDensity (fun p ↦ g p.1 p.2) :=
  compProd_withDensity hg

-- No s-finiteness of the measure `ν`.
example (ν : Measure α) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [ProbabilityTheory.IsZeroOrMarkovKernel η] {X : β → ℝ} {Y : γ → ℝ} {c cY : NNReal}
    (hX : ProbabilityTheory.Kernel.HasSubgaussianMGF X c κ ν)
    (hY : ProbabilityTheory.Kernel.HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) :
    ProbabilityTheory.Kernel.HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ η) ν :=
  hX.add_compProd hY

-- A conditional kernel need not be finite or s-finite for the Lebesgue integrals.
example (κ : Kernel α (β × γ)) (η : Kernel (α × β) γ) [κ.IsCondKernel η] {f : β × γ → ℝ≥0∞}
    (hf : Measurable f) (a : α) :
    ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂Kernel.fst κ a = ∫⁻ x, f x ∂κ a :=
  ProbabilityTheory.lintegral_condKernel hf a

example (ρ : Measure (β × γ)) (η : Kernel β γ) [ρ.IsCondKernel η] {f : β × γ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ b, ∫⁻ c, f (b, c) ∂η b ∂ρ.fst = ∫⁻ x, f x ∂ρ :=
  lintegral_condKernel hf

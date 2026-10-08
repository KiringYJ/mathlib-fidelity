/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
* the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
  distribution (a.k.a. convergence in law, weak convergence of measures);
* `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
  a finite measure;
* `MeasureTheory.FiniteMeasure.normalize`: Normalize a nonzero finite measure to a probability
  measure.
* `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
  `μ` on `Ω` along an almost everywhere measurable function `f : Ω → Ω'`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
  probability measures is characterized by the convergence of expected values of all bounded
  continuous random variables. This shows that the chosen definition of topology coincides with
  the common textbook definition of convergence in distribution, i.e., weak convergence of
  measures. A similar characterization by the convergence of expected values (in the
  `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
  measures to a nonzero limit is characterized by the convergence of the total masses and of the
  probability-normalized versions, taken along the indices where the finite measures are nonzero.
* `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
  continuous.
* `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
  Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
  approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
* Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

@[expose] public section


noncomputable section

open Set Filter BoundedContinuousFunction Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensSigmaAlgebra Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/


/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (Ω : Type*) [SigmaAlgebra Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }

variable {Ω : Type*} [SigmaAlgebra Ω]

/-- Type conversion from `Measure` to `ProbabilityMeasure`. -/
def Measure.toProbabilityMeasure (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ProbabilityMeasure Ω := ⟨μ, inferInstance⟩

theorem Measure.toProbabilityMeasure_inj (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.toProbabilityMeasure = ν.toProbabilityMeasure ↔ μ = ν :=
  ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

namespace ProbabilityMeasure

instance [Inhabited Ω] : Inhabited (ProbabilityMeasure Ω) :=
  ⟨⟨Measure.dirac default, Measure.dirac.isProbabilityMeasure⟩⟩

/-- Coercion from `MeasureTheory.ProbabilityMeasure Ω` to `MeasureTheory.Measure Ω`. -/
@[coe]
def toMeasure : ProbabilityMeasure Ω → Measure Ω := Subtype.val

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (ProbabilityMeasure Ω) (MeasureTheory.Measure Ω) := { coe := toMeasure }

instance (μ : ProbabilityMeasure Ω) : IsProbabilityMeasure (μ : Measure Ω) :=
  μ.prop

@[simp, norm_cast] lemma coe_mk (μ : Measure Ω) (hμ) : toMeasure ⟨μ, hμ⟩ = μ := rfl

@[simp]
theorem val_eq_to_measure (ν : ProbabilityMeasure Ω) : ν.val = (ν : Measure Ω) := rfl

@[simp]
theorem _root_.MeasureTheory.Measure.coe_toProbabilityMeasure (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
  μ.toProbabilityMeasure = μ := rfl

@[simp]
theorem toProbabilityMeasure_coe (ν : ProbabilityMeasure Ω) :
    (↑ν : Measure Ω).toProbabilityMeasure = ν := rfl

theorem toMeasure_injective : Function.Injective ((↑) : ProbabilityMeasure Ω → Measure Ω) :=
  Subtype.coe_injective

@[macro_inline]
instance instFunLike : FunLike (ProbabilityMeasure Ω) (Set Ω) ℝ≥0 where
  coe μ s := ((μ : Measure Ω) s).toNNReal
  coe_injective μ ν h := toMeasure_injective <| Measure.ext fun s _ ↦ by
    simpa [ENNReal.toNNReal_eq_toNNReal_iff, measure_ne_top] using congr_fun h s

lemma coeFn_def (μ : ProbabilityMeasure Ω) : μ = fun s ↦ ((μ : Measure Ω) s).toNNReal := rfl

lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ (μ s).toNNReal := rfl

@[simp, norm_cast]
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := ProbabilityMeasure Ω) ⟨μ, hμ⟩ s = (μ s).toNNReal := rfl

@[simp, norm_cast]
theorem coeFn_univ (ν : ProbabilityMeasure Ω) : ν univ = 1 :=
  congr_arg ENNReal.toNNReal ν.prop.measure_univ

@[simp]
theorem coeFn_empty (ν : ProbabilityMeasure Ω) : ν ∅ = 0 := by simp [coeFn_def]

theorem coeFn_univ_ne_zero (ν : ProbabilityMeasure Ω) : ν univ ≠ 0 := by
  simp only [coeFn_univ, Ne, one_ne_zero, not_false_iff]

@[simp] theorem measureReal_eq_coe_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν : Measure Ω).real s = ν s := by
  simp [coeFn_def, Measure.real, ENNReal.toReal]

theorem toNNReal_measureReal_eq_coeFn (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ((ν : Measure Ω).real s).toNNReal = ν s := by
  simp

/-- A probability measure can be interpreted as a finite measure. -/
def toFiniteMeasure (μ : ProbabilityMeasure Ω) : FiniteMeasure Ω := ⟨μ, inferInstance⟩

@[simp] lemma coeFn_toFiniteMeasure (μ : ProbabilityMeasure Ω) : ⇑μ.toFiniteMeasure = μ := rfl
lemma toFiniteMeasure_apply (μ : ProbabilityMeasure Ω) (s : Set Ω) :
    μ.toFiniteMeasure s = μ s := rfl

@[simp]
theorem toMeasure_comp_toFiniteMeasure_eq_toMeasure (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Measure Ω) = (ν : Measure Ω) := rfl

@[simp]
theorem coeFn_comp_toFiniteMeasure_eq_coeFn (ν : ProbabilityMeasure Ω) :
    (ν.toFiniteMeasure : Set Ω → ℝ≥0) = (ν : Set Ω → ℝ≥0) := rfl

@[simp]
theorem toFiniteMeasure_apply_eq_apply (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν.toFiniteMeasure s = ν s := rfl

theorem toFiniteMeasure_injective :
    Function.Injective (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  fun _ _ h ↦ Subtype.ext <| congr_arg FiniteMeasure.toMeasure h

@[simp]
theorem ennreal_coeFn_eq_coeFn_toMeasure (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    (ν s : ℝ≥0∞) = (ν : Measure Ω) s := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    toMeasure_comp_toFiniteMeasure_eq_toMeasure]

@[simp]
theorem null_iff_toMeasure_null (ν : ProbabilityMeasure Ω) (s : Set Ω) :
    ν s = 0 ↔ (ν : Measure Ω) s = 0 :=
  ⟨fun h ↦ by rw [← ennreal_coeFn_eq_coeFn_toMeasure, h, ENNReal.coe_zero],
   fun h ↦ congrArg ENNReal.toNNReal h⟩

@[gcongr]
theorem apply_mono (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_mono _ h

theorem apply_union_le (μ : ProbabilityMeasure Ω) {s₁ s₂ : Set Ω} : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ := by
  rw [← coeFn_comp_toFiniteMeasure_eq_coeFn]
  exact FiniteMeasure.apply_union_le _

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
protected lemma tendsto_measure_iUnion_accumulate {ι : Type*} [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {μ : ProbabilityMeasure Ω} {f : ι → Set Ω} :
    Tendsto (fun i ↦ μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  simpa [← ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.tendsto_coe]
    using tendsto_measure_iUnion_accumulate (μ := μ.toMeasure)

@[simp] theorem apply_le_one (μ : ProbabilityMeasure Ω) (s : Set Ω) : μ s ≤ 1 := by
  simpa using apply_mono μ (subset_univ s)

theorem nonempty (μ : ProbabilityMeasure Ω) : Nonempty Ω :=
  nonempty_of_isProbabilityMeasure μ

@[ext]
theorem eq_of_forall_toMeasure_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply toMeasure_injective
  ext1 s s_mble
  exact h s s_mble

theorem eq_of_forall_apply_eq (μ ν : ProbabilityMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1 s s_mble
  simpa [ennreal_coeFn_eq_coeFn_toMeasure] using congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (h s s_mble)

@[simp]
theorem mass_toFiniteMeasure (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.mass = 1 :=
  μ.coeFn_univ

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma range_toFiniteMeasure :
    range toFiniteMeasure = {μ : FiniteMeasure Ω | μ.mass = 1} := by
  ext μ
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨fun ⟨ν, hν⟩ ↦ by simp [← hν], fun h ↦ ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using! h)⟩, ?_⟩
  ext s hs
  simp

theorem toFiniteMeasure_nonzero (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure ≠ 0 := by
  simp [← FiniteMeasure.mass_nonzero_iff]

instance (μ : ProbabilityMeasure Ω) : NeZero μ.toFiniteMeasure := ⟨μ.toFiniteMeasure_nonzero⟩

/-- The type of probability measures is a measurable space when equipped with the Giry monad. -/
instance : SigmaAlgebra (ProbabilityMeasure Ω) :=
  inferInstanceAs <| SigmaAlgebra (Subtype _)

lemma measurableSet_isProbabilityMeasure :
    MeasurableSet { μ : Measure Ω | IsProbabilityMeasure μ } := by
  suffices { μ : Measure Ω | IsProbabilityMeasure μ } = (fun μ => μ univ) ⁻¹' {1} by
    rw [this]
    exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  ext _
  apply isProbabilityMeasure_iff

/-- The monoidal product is a measurable function from the product of probability spaces over
`α` and `β` into the type of probability spaces over `α × β`. Lemma 4.1 of [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]. -/
theorem measurable_fun_prod {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β] :
    Measurable (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β)
      ↦ μ.1.toMeasure.prod μ.2.toMeasure) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod _
  simp only [mem_image2, forall_exists_index, and_imp]
  intro _ u Hu v Hv Heq
  simp_rw [← Heq, Measure.prod_prod_of_sigmaFinite]
  apply Measurable.mul
  · exact (Measure.measurable_coe Hu).comp (measurable_subtype_coe.comp measurable_fst)
  · exact (Measure.measurable_coe Hv).comp (measurable_subtype_coe.comp measurable_snd)

lemma apply_iUnion_le {μ : ProbabilityMeasure Ω} {f : ℕ → Set Ω}
    (hf : Summable fun n ↦ μ (f n)) :
    μ (⋃ n, f n) ≤ ∑' n, μ (f n) := by
  simpa [← ENNReal.coe_le_coe, ENNReal.coe_tsum hf] using MeasureTheory.measure_iUnion_le f

section convergence_in_distribution

variable [TopologicalSpace Ω] [OpensSigmaAlgebra Ω]

theorem testAgainstNN_lipschitz (μ : ProbabilityMeasure Ω) :
    LipschitzWith 1 fun f : Ω →ᵇ ℝ≥0 ↦ μ.toFiniteMeasure.testAgainstNN f :=
  μ.mass_toFiniteMeasure ▸ μ.toFiniteMeasure.testAgainstNN_lipschitz

/-- The topology of weak convergence on `MeasureTheory.ProbabilityMeasure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`. -/
instance : TopologicalSpace (ProbabilityMeasure Ω) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

theorem toFiniteMeasure_continuous :
    Continuous (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) :=
  continuous_induced_dom

/-- Probability measures yield elements of the `WeakDual` of bounded continuous nonnegative
functions via `MeasureTheory.FiniteMeasure.testAgainstNN`, i.e., integration. -/
def toWeakDualBCNN : ProbabilityMeasure Ω → WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
  FiniteMeasure.toWeakDualBCNN ∘ toFiniteMeasure

@[simp]
theorem coe_toWeakDualBCNN (μ : ProbabilityMeasure Ω) :
    ⇑μ.toWeakDualBCNN = μ.toFiniteMeasure.testAgainstNN := rfl

@[simp]
theorem toWeakDualBCNN_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBCNN f = (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNNReal := rfl

theorem toWeakDualBCNN_continuous : Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toWeakDualBCNN :=
  FiniteMeasure.toWeakDualBCNN_continuous.comp toFiniteMeasure_continuous

/-- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
theorem continuous_testAgainstNN_eval (f : Ω →ᵇ ℝ≥0) :
    Continuous fun μ : ProbabilityMeasure Ω ↦ μ.toFiniteMeasure.testAgainstNN f :=
  (FiniteMeasure.continuous_testAgainstNN_eval f).comp toFiniteMeasure_continuous

/-- The canonical mapping from probability measures to finite measures is an embedding. -/
theorem toFiniteMeasure_isEmbedding (Ω : Type*) [SigmaAlgebra Ω] [TopologicalSpace Ω]
    [OpensSigmaAlgebra Ω] :
    IsEmbedding (toFiniteMeasure : ProbabilityMeasure Ω → FiniteMeasure Ω) where
  eq_induced := rfl
  injective _μ _ν h := Subtype.ext <| congr_arg FiniteMeasure.toMeasure h

instance R1Space : R1Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).r1Space

theorem tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds {δ : Type*} (F : Filter δ)
    {μs : δ → ProbabilityMeasure Ω} {μ₀ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ₀) ↔ Tendsto (toFiniteMeasure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  (toFiniteMeasure_isEmbedding Ω).tendsto_nhds_iff

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0,
        Tendsto (fun i ↦ ∫⁻ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) := by
  rw [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact FiniteMeasure.tendsto_iff_forall_lintegral_tendsto

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_tendsto]

theorem tendsto_iff_forall_integral_rclike_tendsto {γ : Type*} (𝕜 : Type*) [RCLike 𝕜]
    {F : Filter γ} {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f ω ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, f ω ∂(μ : Measure Ω))) := by
  simp [tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds,
    FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]

variable {X : Type*} [TopologicalSpace X] {μs : X → ProbabilityMeasure Ω}

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
lemma continuous_iff_forall_continuous_lintegral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ≥0, Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_lintegral_tendsto,
    forall_comm (α := X)]

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
lemma continuous_iff_forall_continuous_integral :
    Continuous μs ↔ ∀ f : Ω →ᵇ ℝ, Continuous fun x ↦ ∫ ω, f ω ∂(μs x) := by
  simp [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_integral_tendsto,
    forall_comm (α := X)]

lemma continuous_lintegral_boundedContinuousFunction [SigmaAlgebra X] [OpensSigmaAlgebra X]
    (f : X →ᵇ ℝ≥0) : Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuous_lintegral.1 continuous_id _

lemma continuous_integral_boundedContinuousFunction [SigmaAlgebra X] [OpensSigmaAlgebra X]
    (f : X →ᵇ ℝ) : Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuous_integral.1 continuous_id _

variable [CompactSpace Ω]

/-- The characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ≥0), Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ), Continuous fun x ↦ ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [SigmaAlgebra X] [OpensSigmaAlgebra X] {F : Type*}

lemma continuous_lintegral_continuousMap [FunLike F X ℝ≥0] [ContinuousMapClass F X ℝ≥0] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

lemma continuous_integral_continuousMap [FunLike F X ℝ] [ContinuousMapClass F X ℝ] (f : F) :
    Continuous fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

end convergence_in_distribution -- section

section Hausdorff

variable [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω]
variable (Ω)

/-- On topological spaces where indicators of closed sets have decreasing approximating sequences of
continuous functions (`HasOuterApproxClosed`), the topology of convergence in distribution of Borel
probability measures is Hausdorff (`T2Space`). -/
instance t2Space : T2Space (ProbabilityMeasure Ω) := (toFiniteMeasure_isEmbedding Ω).t2Space

end Hausdorff -- section

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section NormalizeFiniteMeasure

/-! ### Normalization of finite measures to probability measures

This section is about normalizing nonzero finite measures to probability measures, i.e., dividing
them by their total mass. Normalization is defined exactly on the nonzero finite measures:
`MeasureTheory.FiniteMeasure.normalize μ hμ` takes a proof `hμ : μ ≠ 0`. The proof may be omitted
when the tactic `finite_measure_ne_zero` finds it, for example as a local hypothesis, as a
hypothesis about all members of a family, or through a `NeZero` instance such as the one for
probability measures.

The weak convergence of finite measures to a nonzero limit measure is characterized by the
convergence of the total masses and the convergence of the normalized probability measures along
the indices where the finite measures are nonzero.
-/

open Lean Elab Tactic in
/-- The default discharger for the hypothesis `μ ≠ 0` of `MeasureTheory.FiniteMeasure.normalize`.

It closes the goal with a local hypothesis `μ ≠ 0`, with a `NeZero μ` instance (for example for
`μ = P.toFiniteMeasure` with `P` a probability measure), or by applying a local hypothesis about a
family, such as `∀ i, μs i ≠ 0` or `∀ ν ∈ S, ν ≠ 0`. Other evidence, such as `μ.mass ≠ 0`, the
property of an element of `{ν : FiniteMeasure Ω // ν ≠ 0}`, or `smul_ne_zero hc hμ`, is passed
explicitly. Otherwise the tactic fails with an explanation.

It never chooses the finite measure itself: if the measure is not determined when the tactic runs,
it fails instead of assigning it from a hypothesis. -/
elab (name := finiteMeasureNeZero) "finite_measure_ne_zero" : tactic => do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "FiniteMeasure.normalize: the measure to normalize is not determined; \
      pass it explicitly"
  -- The bounded search only applies quantified hypotheses; without `intro` and `exfalso` it
  -- fails quickly in large contexts.
  evalTactic (← `(tactic|
    first
      | assumption
      | exact NeZero.ne _
      | solve_by_elim (maxDepth := 3) -intro -exfalso
      | fail "FiniteMeasure.normalize needs a proof that the finite measure is nonzero"))

namespace FiniteMeasure

variable {Ω : Type*} {m0 : SigmaAlgebra Ω}

/-- Normalize a nonzero finite measure so that it becomes a probability measure, i.e., divide it by
its total mass. The proof `hμ : μ ≠ 0` can usually be omitted; see `finite_measure_ne_zero`.

Since `hμ` is an explicit argument, write `(μ.normalize) s` or `μ.normalize hμ s` to evaluate the
normalized measure on a set `s`. -/
def normalize (μ : FiniteMeasure Ω) (hμ : μ ≠ 0 := by finite_measure_ne_zero) :
    ProbabilityMeasure Ω where
  val := μ.mass⁻¹ • (μ : Measure Ω)
  property := by
    have hm : μ.mass ≠ 0 := (mass_nonzero_iff μ).mpr hμ
    refine ⟨?_⟩
    simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
      ENNReal.coe_inv hm, ennreal_mass]
    rw [← ENNReal.coe_ne_zero, ennreal_mass] at hm
    exact ENNReal.inv_mul_cancel hm (measure_lt_top _ _).ne

variable {μ : FiniteMeasure Ω}

@[simp]
theorem toMeasure_normalize (hμ : μ ≠ 0) :
    (μ.normalize hμ : Measure Ω) = μ.mass⁻¹ • (μ : Measure Ω) := rfl

@[simp]
theorem toFiniteMeasure_normalize (hμ : μ ≠ 0) :
    (μ.normalize hμ).toFiniteMeasure = μ.mass⁻¹ • μ := rfl

@[simp]
theorem normalize_apply (hμ : μ ≠ 0) (s : Set Ω) : μ.normalize hμ s = μ.mass⁻¹ * μ s := by
  rw [← ProbabilityMeasure.toFiniteMeasure_apply_eq_apply, toFiniteMeasure_normalize,
    smul_apply, smul_eq_mul]

theorem mass_mul_normalize_apply (hμ : μ ≠ 0) (s : Set Ω) : μ.mass * μ.normalize hμ s = μ s := by
  rw [normalize_apply, ← mul_assoc, mul_inv_cancel₀ ((mass_nonzero_iff μ).mpr hμ), one_mul]

theorem mass_smul_normalize (hμ : μ ≠ 0) : μ.mass • (μ.normalize hμ).toFiniteMeasure = μ := by
  rw [toFiniteMeasure_normalize, smul_smul, mul_inv_cancel₀ ((mass_nonzero_iff μ).mpr hμ),
    one_smul]

/-- The normalization of a nonzero finite measure `μ` is the unique probability measure whose
multiple by the total mass of `μ` is `μ`. -/
theorem eq_normalize_iff {P : ProbabilityMeasure Ω} (hμ : μ ≠ 0) :
    P = μ.normalize hμ ↔ μ.mass • P.toFiniteMeasure = μ := by
  refine ⟨fun h ↦ h ▸ mass_smul_normalize hμ, fun h ↦ ?_⟩
  apply ProbabilityMeasure.toFiniteMeasure_injective
  rw [toFiniteMeasure_normalize, eq_inv_smul_iff₀ ((mass_nonzero_iff μ).mpr hμ), h]

/-- Normalization is invariant under multiplication by a nonzero scalar. -/
theorem normalize_smul {c : ℝ≥0} (hc : c ≠ 0) (hμ : μ ≠ 0) :
    (c • μ).normalize (smul_ne_zero hc hμ) = μ.normalize hμ := by
  apply Subtype.ext
  change (c • μ).mass⁻¹ • ((c • μ : FiniteMeasure Ω) : Measure Ω) = μ.mass⁻¹ • (μ : Measure Ω)
  have hcm : (c • μ).mass = c * μ.mass := by simp [mass]
  rw [hcm, toMeasure_smul, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.toFiniteMeasure_normalize_eq_self
    (μ : ProbabilityMeasure Ω) : μ.toFiniteMeasure.normalize = μ := by
  rw [eq_comm, eq_normalize_iff, ProbabilityMeasure.mass_toFiniteMeasure, one_smul]

/-- Averaging with respect to a nonzero finite measure is the same as integrating against
`MeasureTheory.FiniteMeasure.normalize`. -/
theorem average_eq_integral_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hμ : μ ≠ 0) (f : Ω → E) :
    average (μ : Measure Ω) f = ∫ ω, f ω ∂(μ.normalize hμ : Measure Ω) := by
  rw [toMeasure_normalize, average]
  congr
  simp [ENNReal.coe_inv ((mass_nonzero_iff μ).mpr hμ), ennreal_mass]

variable {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure Ω}

/-- Finite measures whose total masses converge to a nonzero limit are eventually nonzero. -/
theorem eventually_ne_zero_of_tendsto_mass {m : ℝ≥0}
    (h : Tendsto (fun i ↦ (μs i).mass) F (𝓝 m)) (hm : m ≠ 0) : ∀ᶠ i in F, μs i ≠ 0 := by
  filter_upwards [h.eventually_ne hm] with i hi
  exact (mass_nonzero_iff _).mp hi

variable [TopologicalSpace Ω]

theorem testAgainstNN_normalize (hμ : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
    (μ.normalize hμ).toFiniteMeasure.testAgainstNN f = μ.mass⁻¹ * μ.testAgainstNN f := by
  rw [toFiniteMeasure_normalize, smul_testAgainstNN_apply, smul_eq_mul]

variable [OpensSigmaAlgebra Ω]

/-- Normalization is continuous on the nonzero finite measures. -/
theorem continuous_normalize :
    Continuous fun ν : {ν : FiniteMeasure Ω // ν ≠ 0} ↦ ν.1.normalize ν.2 := by
  rw [(ProbabilityMeasure.toFiniteMeasure_isEmbedding Ω).continuous_iff]
  simp only [Function.comp_def, toFiniteMeasure_normalize]
  exact ((continuous_mass.comp continuous_subtype_val).inv₀
    fun ν ↦ (mass_nonzero_iff _).mpr ν.2).smul continuous_subtype_val

/-- Finite measures converging to a nonzero limit are eventually nonzero. -/
theorem eventually_ne_zero_of_tendsto (h : Tendsto μs F (𝓝 μ)) (hμ : μ ≠ 0) :
    ∀ᶠ i in F, μs i ≠ 0 :=
  eventually_ne_zero_of_tendsto_mass h.mass ((mass_nonzero_iff μ).mpr hμ)

/-- If finite measures converge to a nonzero limit, then their normalizations converge to the
normalization of the limit, along the indices where the finite measures are nonzero. -/
theorem tendsto_normalize_of_tendsto (h : Tendsto μs F (𝓝 μ)) (hμ : μ ≠ 0) :
    Tendsto (fun i : {i // μs i ≠ 0} ↦ (μs i).normalize i.2) (F.comap (↑))
      (𝓝 (μ.normalize hμ)) := by
  have hsub : Tendsto (fun i : {i // μs i ≠ 0} ↦ (⟨μs i, i.2⟩ : {ν : FiniteMeasure Ω // ν ≠ 0}))
      (F.comap (↑)) (𝓝 ⟨μ, hμ⟩) := tendsto_subtype_rng.mpr (h.comp tendsto_comap)
  simpa only [Function.comp_def] using (continuous_normalize.tendsto _).comp hsub

/-- Version of `MeasureTheory.FiniteMeasure.tendsto_normalize_of_tendsto` for families of nonzero
finite measures. -/
theorem tendsto_normalize_of_tendsto_of_forall_ne_zero (h : Tendsto μs F (𝓝 μ)) (hμ : μ ≠ 0)
    (hμs : ∀ i, μs i ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize (hμs i)) F (𝓝 (μ.normalize hμ)) := by
  have hsub : Tendsto (fun i ↦ (⟨μs i, hμs i⟩ : {ν : FiniteMeasure Ω // ν ≠ 0})) F
      (𝓝 ⟨μ, hμ⟩) := tendsto_subtype_rng.mpr h
  simpa only [Function.comp_def] using (continuous_normalize.tendsto _).comp hsub

/-- The weak convergence of finite measures to a nonzero limit is characterized by the convergence
of their total masses and of their normalizations, the latter along the indices where the finite
measures are nonzero. -/
theorem tendsto_normalize_iff_tendsto (hμ : μ ≠ 0) :
    Tendsto (fun i : {i // μs i ≠ 0} ↦ (μs i).normalize i.2) (F.comap (↑))
        (𝓝 (μ.normalize hμ)) ∧ Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) := by
  refine ⟨fun ⟨h_norm, h_mass⟩ ↦ ?_, fun h ↦ ⟨tendsto_normalize_of_tendsto h hμ, h.mass⟩⟩
  rw [← tendsto_comap'_iff (i := ((↑) : {i // μs i ≠ 0} → γ)) (by
    rw [Subtype.range_coe_subtype]
    exact eventually_ne_zero_of_tendsto_mass h_mass ((mass_nonzero_iff μ).mpr hμ))]
  have := (h_mass.comp tendsto_comap).smul
    ((ProbabilityMeasure.toFiniteMeasure_continuous.tendsto _).comp h_norm)
  simpa only [Function.comp_def, mass_smul_normalize] using this

/-- Version of `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto` for families of nonzero
finite measures. -/
theorem tendsto_normalize_iff_tendsto_of_forall_ne_zero (hμ : μ ≠ 0) (hμs : ∀ i, μs i ≠ 0) :
    Tendsto (fun i ↦ (μs i).normalize (hμs i)) F (𝓝 (μ.normalize hμ)) ∧
        Tendsto (fun i ↦ (μs i).mass) F (𝓝 μ.mass) ↔
      Tendsto μs F (𝓝 μ) :=
  ⟨fun ⟨h_norm, h_mass⟩ ↦
      (tendsto_normalize_iff_tendsto hμ).1 ⟨h_norm.comp tendsto_comap, h_mass⟩,
    fun h ↦ ⟨tendsto_normalize_of_tendsto_of_forall_ne_zero h hμ hμs, h.mass⟩⟩

end FiniteMeasure --namespace

end NormalizeFiniteMeasure -- section

section map

variable {Ω Ω' : Type*} [SigmaAlgebra Ω] [SigmaAlgebra Ω']

namespace ProbabilityMeasure

/-- The push-forward of a probability measure by an almost everywhere measurable function. -/
noncomputable def map (ν : ProbabilityMeasure Ω) (f : Ω → Ω')
    (hf : AEMeasurable f ν := by fun_prop_default) : ProbabilityMeasure Ω' :=
  ⟨(ν : Measure Ω).map f hf, inferInstance⟩

@[simp] lemma toMeasure_map (ν : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (hf : AEMeasurable f ν := by fun_prop) :
    (ν.map f hf).toMeasure = ν.toMeasure.map f hf := rfl

/-- Note that this is an equality of elements of `ℝ≥0∞`. See also
`MeasureTheory.ProbabilityMeasure.map_apply` for the corresponding equality as elements of `ℝ≥0`. -/
lemma map_apply' (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} {A : Set Ω'}
    (A_mble : MeasurableSet A) (f_aemble : AEMeasurable f ν := by fun_prop) :
    (ν.map f f_aemble : Measure Ω') A = (ν : Measure Ω) (f ⁻¹' A) :=
  Measure.map_apply A_mble f_aemble

@[simp]
lemma map_apply (ν : ProbabilityMeasure Ω) {f : Ω → Ω'} {A : Set Ω'}
    (A_mble : MeasurableSet A) (f_aemble : AEMeasurable f ν := by fun_prop) :
    (ν.map f f_aemble) A = ν (f ⁻¹' A) := by
  exact (ENNReal.toNNReal_eq_toNNReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mpr <|
    ν.map_apply' A_mble f_aemble

variable [TopologicalSpace Ω] [OpensSigmaAlgebra Ω]
variable [TopologicalSpace Ω'] [BorelSpace Ω']

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
convergence (in distribution) of `ProbabilityMeasure`s on `X` implies convergence (in
distribution) of the push-forwards of these measures by `f`. -/
lemma tendsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι}
    (νs : ι → ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto νs L (𝓝 ν))
    {f : Ω → Ω'} (f_cont : Continuous f) :
    Tendsto (fun i ↦ (νs i).map f) L (𝓝 (ν.map f)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at lim ⊢
  intro g
  convert! lim (g.compContinuous ⟨f, f_cont⟩) <;>
  · simp only [map, compContinuous_apply, ContinuousMap.coe_mk]
    refine lintegral_map ?_ f_cont.measurable
    exact (ENNReal.continuous_coe.comp g.continuous).measurable

/-- If `f : X → Y` is continuous and `Y` is equipped with the Borel sigma algebra, then
the push-forward of probability measures `f* : ProbabilityMeasure X → ProbabilityMeasure Y`
is continuous (in the topologies of convergence in distribution). -/
lemma continuous_map {f : Ω → Ω'} (f_cont : Continuous f) :
    Continuous (fun ν ↦ ProbabilityMeasure.map ν f) := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ tendsto_map_of_tendsto_of_continuous _ _ continuous_id.continuousAt f_cont

end ProbabilityMeasure -- namespace

end map -- section

section join_bind

theorem isProbabilityMeasure_join {α : Type*} [SigmaAlgebra α] {m : Measure (Measure α)}
    [IsProbabilityMeasure m] (hm : ∀ᵐ μ ∂m, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

theorem isProbabilityMeasure_bind {α : Type*} {β : Type*} [SigmaAlgebra α] [SigmaAlgebra β]
    {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β} (hf₀ : AEMeasurable f m)
    (hf₁ : ∀ᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, Measure.bind_apply _ hf₀]
  simp_rw [isProbabilityMeasure_iff] at hf₁
  exact lintegral_eq_const hf₁

end join_bind

end MeasureTheory -- namespace

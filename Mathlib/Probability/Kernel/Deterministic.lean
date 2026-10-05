/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Class `IsDeterministic` of deterministic kernels

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `Kernel.IsDeterministic`: a kernel is deterministic if copying then applying the kernel to the
  two copies is the same as first applying the kernel then copying.

## Main statements

* `isDeterministic_iff_isZeroOneMeasure`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.
* `IsDeterministic.isSFiniteKernel`: a deterministic kernel is s-finite, since each of its values
  is a zero-one measure, possibly zero, or `∞` times a zero-one probability measure.
* `IsDeterministic.exists_eq_deterministic`: in a standard Borel space, a deterministic Markov
  kernel is a Dirac kernel of some measurable function.
* `comp_parallelComp_comp_copy`: if the composition of two Markov kernels `η ∘ₖ κ` is
  deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
  and `κ` independently. This corresponds to the equation of a Positive Markov category.
  See Example 11.25 of [fritz2020].

## Implementation notes

`comp_parallelComp_comp_copy` is true only when considering Markov kernels. To see why, consider
the counterexample with $X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_
{\varnothing}$ and $\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their
composition is deterministic, the equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
* [Moss and Perrone, *A category-theoretic proof of the ergodic decomposition theorem*][moss2023]
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}

namespace ProbabilityTheory

/-- A kernel is deterministic if the parallel composition of the kernel with itself exists and
copying then applying the kernel to the two copies is the same as first applying the kernel then
copying. -/
class IsDeterministic (κ : Kernel α β) : Prop where
  /-- The parallel composition of the kernel with itself exists. -/
  hasParallelComp_self : κ.HasParallelComp κ
  parallelComp_self_comp_copy' :
    haveI := hasParallelComp_self
    (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ

attribute [instance] IsDeterministic.hasParallelComp_self

namespace Kernel

lemma parallelComp_self_comp_copy {κ : Kernel α β} [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ :=
  IsDeterministic.parallelComp_self_comp_copy'

instance {f : α → β} (hf : Measurable f) : IsDeterministic (deterministic f hf) where
  hasParallelComp_self := inferInstance
  parallelComp_self_comp_copy' := by
    simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
      deterministic_comp_deterministic, Function.comp_def, Function.diag_def]

instance : IsDeterministic (mβ := mα) (Kernel.id (α := α)) := by unfold Kernel.id; infer_instance

instance : IsDeterministic (copy α) := by unfold copy; infer_instance

instance : IsDeterministic (discard α) := by unfold discard; infer_instance

instance : IsDeterministic (swap α β) := by unfold swap; infer_instance

open IsZeroOneMeasure

/-- A deterministic kernel is multiplicative on intersections: evaluating
`(κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ` at `a` on `s ×ˢ t` gives `κ a s * κ a t = κ a (s ∩ t)`. -/
lemma IsDeterministic.measure_inter_eq_mul (κ : Kernel α β) [IsDeterministic κ] (a : α)
    {s t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    κ a (s ∩ t) = κ a s * κ a t := by
  have h := DFunLike.congr_fun (DFunLike.congr_fun κ.parallelComp_self_comp_copy a) (s ×ˢ t)
  rw [copy_comp_apply_prod κ a hs ht, comp_apply' _ _ _ (hs.prod ht), copy_apply,
    lintegral_dirac' _ ((κ ∥ₖ κ).measurable_coe (hs.prod ht)), parallelComp_apply' (hs.prod ht)]
    at h
  have h_eq (b : β) : κ a (Prod.mk b ⁻¹' s ×ˢ t) = s.indicator (fun _ ↦ κ a t) b := by
    by_cases hb : b ∈ s
    · simp [hb, mk_preimage_prod_right hb]
    · simp [hb, mk_preimage_prod_right_eq_empty hb]
  simp_rw [h_eq, lintegral_indicator_const hs] at h
  rw [← h, mul_comm]

lemma isDeterministic_iff_isZeroOneMeasure (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ ∀ a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs ↦ ?_⟩
    have := IsDeterministic.measure_inter_eq_mul κ a hs hs
    rw [inter_self] at this
    by_cases hκ : κ a s = 0
    · simp [hκ]
    · exact Or.inr <| (ENNReal.mul_eq_left hκ (by simp)).mp this.symm
  · intro _
    refine ⟨inferInstance, ?_⟩
    ext : 1
    rw [parallelComp_comp_copy, prod_apply]
    refine Measure.productBySections_eq fun s t hs ht ↦ ?_
    rw [copy_comp_apply_prod _ _ hs ht]
    exact measure_inter_eq_prod hs ht

instance (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] : ∀ a, IsZeroOneMeasure (κ a) :=
  (isDeterministic_iff_isZeroOneMeasure κ).mp ‹_›

/-- A deterministic kernel gives a measurable set either no mass or its full mass. -/
lemma IsDeterministic.measure_eq_zero_or_eq_measure_univ (κ : Kernel α β) [IsDeterministic κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    κ a s = 0 ∨ κ a s = κ a univ := by
  have h := IsDeterministic.measure_inter_eq_mul κ a hs hs.compl
  rw [inter_compl_self, measure_empty] at h
  refine (mul_eq_zero.mp h.symm).imp id fun h0 ↦ ?_
  rw [← measure_add_measure_compl hs, h0, add_zero]

/-- The total mass of a deterministic kernel at a point is `0`, `1`, or `∞`. -/
lemma IsDeterministic.measure_univ_eq_zero_or_one_or_top (κ : Kernel α β) [IsDeterministic κ]
    (a : α) :
    κ a univ = 0 ∨ κ a univ = 1 ∨ κ a univ = ∞ := by
  have h := IsDeterministic.measure_inter_eq_mul κ a .univ .univ
  rw [inter_self] at h
  by_cases h0 : κ a univ = 0
  · exact .inl h0
  by_cases htop : κ a univ = ∞
  · exact .inr (.inr htop)
  exact .inr (.inl ((ENNReal.mul_eq_left h0 htop).mp h.symm))

/-- The measure `s ↦ min (κ a s) 1` of a deterministic kernel `κ`. It is countably additive
because at most one of countably many disjoint measurable sets has positive mass. -/
private noncomputable def capOne (κ : Kernel α β) [IsDeterministic κ] (a : α) : Measure β :=
  Measure.ofMeasurable (fun s _ ↦ min (κ a s) 1) (by simp) fun f hf hd ↦ by
    by_cases h : ∃ i, κ a (f i) ≠ 0
    · obtain ⟨i, hi⟩ := h
      have hj (j : ℕ) (hji : j ≠ i) : κ a (f j) = 0 := by
        have := IsDeterministic.measure_inter_eq_mul κ a (hf i) (hf j)
        rw [(hd hji.symm : Disjoint (f i) (f j)).inter_eq, measure_empty] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hi
      rw [measure_iUnion hd hf, tsum_eq_single i hj,
        tsum_eq_single i fun j hji ↦ by simp [hj j hji]]
    · push Not at h
      simp [measure_iUnion hd hf, h]

private lemma capOne_apply (κ : Kernel α β) [IsDeterministic κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) : capOne κ a s = min (κ a s) 1 :=
  Measure.ofMeasurable_apply s hs

/-- The finite kernel `a ↦ capOne κ a`. -/
private noncomputable def capOneKernel (κ : Kernel α β) [IsDeterministic κ] : Kernel α β where
  toFun := capOne κ
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [capOne_apply κ _ hs]
    exact (κ.measurable_coe hs).min measurable_const

private lemma capOneKernel_apply (κ : Kernel α β) [IsDeterministic κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) : capOneKernel κ a s = min (κ a s) 1 :=
  capOne_apply κ a hs

private instance (κ : Kernel α β) [IsDeterministic κ] : IsFiniteKernel (capOneKernel κ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun a ↦ (capOneKernel_apply κ a .univ).trans_le (min_le_right _ _)⟩⟩

/-- A deterministic kernel is s-finite. Each of its values is a zero-one measure, possibly zero, or
`∞` times a zero-one probability measure (`IsDeterministic.measure_eq_zero_or_eq_measure_univ` and
`IsDeterministic.measure_univ_eq_zero_or_one_or_top`), so the kernel is the sum of the finite
kernel `s ↦ min (κ a s) 1` and countably many copies of it restricted to the points of infinite
total mass. -/
instance IsDeterministic.isSFiniteKernel (κ : Kernel α β) [IsDeterministic κ] :
    IsSFiniteKernel κ := by
  have hA : MeasurableSet {a | κ a univ = ∞} :=
    κ.measurable_coe .univ (measurableSet_singleton ∞)
  have h_eq : κ = capOneKernel κ + Kernel.sum fun _ : ℕ ↦ piecewise hA (capOneKernel κ) 0 := by
    ext a s hs
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add, sum_apply' _ _ hs, piecewise_apply',
      capOneKernel_apply κ a hs]
    rcases IsDeterministic.measure_eq_zero_or_eq_measure_univ κ a hs with h | h
    · simp [h]
    · rcases IsDeterministic.measure_univ_eq_zero_or_one_or_top κ a with h' | h' | h' <;>
        simp [h, h']
  rw [h_eq]
  infer_instance

/-- in a standard Borel space, a deterministic Markov kernel is a Dirac kernel of one measurable
function. -/
theorem IsDeterministic.exists_eq_deterministic [StandardBorelSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] [IsDeterministic κ] :
    ∃ (f : α → β) (hf : Measurable f), κ = deterministic f hf := by
  choose f hf using fun a ↦ exists_eq_dirac (μ := κ a)
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).symm
    rw [this]
    exact κ.measurable_coe hs <| measurableSet_singleton 1
  · ext a : 1
    exact hf a

/-- The equation of a Positive Markov category: if the composition of two Markov kernels `η ∘ₖ κ` is
deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
and `κ` independently. -/
lemma comp_parallelComp_comp_copy {γ : Type*} [SigmaAlgebra γ] {κ : Kernel α β}
    {η : Kernel β γ} [IsMarkovKernel κ] [IsMarkovKernel η] [IsDeterministic (η ∘ₖ κ)] :
    η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ := by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.productBySections_eq fun s t hs ht ↦ ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b ↦ η b s) b := by
    simp only [indicator]
    split_ifs
    all_goals simp_all
  simp_rw [this]
  rw [lintegral_indicator ht]
  rcases ((η ∘ₖ κ) a).zero_one s with (h₀ | h₁)
  · rw [h₀, zero_mul, setLIntegral_eq_zero_iff ht <| η.measurable_coe hs]
    rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff <| η.measurable_coe hs] at h₀
    filter_upwards [h₀] with x hx _ using hx
  · /- In Example 11.25 of [gritz2020], the case where `((η ∘ₖ κ) a) s = 1` is not explicitly
    treated. We prove it here by using the fact that the hypothesis implies that
    `((η ∘ₖ κ) a) sᶜ = 0`, and thus that the integral of `1 - (η b) s` over `κ a` is zero. -/
    rw [h₁, one_mul]
    have integral_le_kernel : ∫⁻ b in t, (η b) s ∂κ a ≤ κ a t := by
      calc
      _ ≤ ∫⁻ a in t, 1 ∂κ a := by
        refine lintegral_mono ?_
        intro b
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
      _ = κ a t := by rw [setLIntegral_one]
    refine le_antisymm integral_le_kernel <| tsub_eq_zero_iff_le.mp ?_
    rw [← nonpos_iff_eq_zero]
    calc
    _ = ∫⁻ b in t, 1 ∂κ a - ∫⁻ b in t, (η b) s ∂κ a := by
      rw [setLIntegral_one]
    _ = ∫⁻ b in t, 1 - (η b) s ∂κ a := by
      rw [lintegral_sub]
      · exact η.measurable_coe hs
      · exact ne_top_of_le_ne_top (by simp) integral_le_kernel
      · refine ae_of_all _ fun b ↦ ?_
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
    _ ≤ ∫⁻ b, 1 - (η b) s ∂κ a := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, (η x) sᶜ ∂κ a := by
        congr with x
        rw [measure_compl hs (by simp)]
        simp
    _ = (η ∘ₖ κ) a sᶜ := by
        rw [η.comp_apply' _ _ hs.compl]
    _ = 0 := by
      rw [measure_compl hs (by simp), measure_univ h₁, h₁, tsub_self]

end ProbabilityTheory.Kernel

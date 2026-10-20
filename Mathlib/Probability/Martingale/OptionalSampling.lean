/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Probability.Martingale.Basic

/-!
# Optional sampling theorem

If `τ` is a bounded stopping time and `σ` is another stopping time, then the value of a martingale
`f` at the stopping time `min σ τ` is a conditional expectation of `stoppedValue f τ` given the
σ-algebra of `σ`: `μ[stoppedValue f τ | hσ.sigmaAlgebra] = stoppedValue f (min σ τ)`.

None of these statements assumes that the measure is σ-finite on the σ-algebras involved. A
martingale supplies its own conditional expectations, and conditional expectations of integrable
functions given a sub-σ-algebra are unique almost everywhere without σ-finiteness.

## Main results

* `MeasureTheory.Martingale.isCondExp_stoppedValue_of_le_const`: the value of a martingale `f` at a
  stopping time `τ` bounded by `n` is a conditional expectation of `f n` given the σ-algebra of
  `τ`.
* `MeasureTheory.Martingale.isCondExp_stoppedValue_of_le`: if `τ` and `σ` are two stopping times
  with `σ ≤ τ` and `τ` is bounded, then the value of a martingale `f` at `σ` is a conditional
  expectation of its value at `τ` given the σ-algebra of `σ`.
* `MeasureTheory.Martingale.isCondExp_stoppedValue_min`: the optional sampling theorem. If `τ` is a
  bounded stopping time and `σ` is another stopping time, then the value of a martingale `f` at the
  stopping time `min σ τ` is a conditional expectation of `f` stopped at `τ` given the σ-algebra of
  `σ`.

The first two results hold for a countable index type, and their `…_of_countable_range` variants
for stopping times with countable range. The three results are stated for the conditional
expectations as almost everywhere classes by
`MeasureTheory.Martingale.condExp_eq_stoppedValue_of_le_const`,
`MeasureTheory.Martingale.condExp_stoppedValue_eq_stoppedValue_of_le` and
`MeasureTheory.Martingale.condExp_stoppedValue_eq_stoppedValue_min`.

-/

public section


open scoped MeasureTheory ENNReal

open TopologicalSpace

namespace MeasureTheory

namespace Martingale

variable {Ω E : Type*} {m : SigmaAlgebra Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

section FirstCountableTopology

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [FirstCountableTopology ι] {ℱ : Filtration ι m} {τ : Ω → WithTop ι} {f : ι → Ω → E}
  {g : Ω → E} {i n : ι}

/-- For a martingale `f`, a stopping time `τ` and `i ≤ n`, every conditional expectation of `f n`
given the σ-algebra of `τ` agrees almost everywhere with `f i` on `{τ = i}`. -/
theorem ae_eq_restrict_eq_of_isCondExp (h : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ)
    (hin : i ≤ n) (hg : IsCondExp hτ.sigmaAlgebra μ (f n) g) :
    g =ᵐ[μ.restrict {x | τ x = i}] f i :=
  hτ.ae_eq_restrict_eq_of_isCondExp i (h.integrable n) hg (h.isCondExp hin)

/-- For a martingale `f` and a stopping time `τ` bounded by `n`, every conditional expectation of
`f n` given the σ-algebra of `τ` agrees almost everywhere with `f i` on `{τ = i}`. -/
theorem ae_eq_restrict_eq_of_isCondExp_of_le_const (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι)
    (hg : IsCondExp hτ.sigmaAlgebra μ (f n) g) : g =ᵐ[μ.restrict {x | τ x = i}] f i := by
  by_cases hin : i ≤ n
  · exact h.ae_eq_restrict_eq_of_isCondExp hτ hin hg
  · suffices {x : Ω | τ x = i} = ∅ by simp [this, Filter.EventuallyEq]
    ext1 x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    contrapose hin
    exact_mod_cast hin ▸ hτ_le x

variable [Nonempty ι]

/-- For a martingale `f` and a stopping time `τ` bounded by `n`, `stoppedValue f τ` agrees almost
everywhere on `{τ = i}` with every conditional expectation of `f n` given the σ-algebra of `τ`. -/
theorem stoppedValue_ae_eq_restrict_eq_of_isCondExp (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι)
    (hg : IsCondExp hτ.sigmaAlgebra μ (f n) g) :
    stoppedValue f τ =ᵐ[μ.restrict {x | τ x = i}] g := by
  refine Filter.EventuallyEq.trans ?_
    (h.ae_eq_restrict_eq_of_isCondExp_of_le_const hτ hτ_le i hg).symm
  rw [Filter.EventuallyEq, ae_restrict_iff' (ℱ.le _ (hτ.measurableSet_eq i))]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Set.mem_ofPred_eq] at hx
  simp [stoppedValue, hx]

end FirstCountableTopology

section CountableRange

variable {ι : Type*} [LinearOrder ι] [Nonempty ι] {ℱ : Filtration ι m} {τ σ : Ω → WithTop ι}
  {f : ι → Ω → E} {n : ι}

open Function in
/-- The value of a martingale `f` at a stopping time `τ` with countable range bounded by `n` is a
conditional expectation of `f n` given the σ-algebra of `τ`.

The sets `{τ = i}` partition `Ω` into countably many sets of the σ-algebra of `τ`, on each of which
`stoppedValue f τ` is `f i`, a conditional expectation of `f n` given `ℱ i`. On `{τ = i}`, the
σ-algebra of `τ` agrees with `ℱ i`. No σ-finiteness is needed. -/
theorem isCondExp_stoppedValue_of_le_const_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) (h_countable : (Set.range τ).Countable) :
    IsCondExp hτ.sigmaAlgebra μ (f n) (stoppedValue f τ) := by
  -- the values of `τ` in `ι` form a countable set `S`, and the sets `{τ = i}` for `i ∈ S`
  -- partition `Ω`
  obtain ⟨S, hS_countable, hS⟩ : ∃ S : Set ι, S.Countable ∧ ∀ i, i ∈ S ↔ ∃ x, τ x = i :=
    ⟨_, h_countable.preimage WithTop.coe_injective, fun _ ↦ Iff.rfl⟩
  have : Countable S := hS_countable.to_subtype
  have h_le (i : S) : (i : ι) ≤ n := by
    obtain ⟨x, hx⟩ := (hS i).1 i.2
    rw [← WithTop.coe_le_coe, ← hx]
    exact hτ_le x
  have h_exists (x : Ω) : ∃ i : S, x ∈ {y | τ y = (i : ι)} := by
    obtain ⟨i, hi⟩ :=
      WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hτ_le x))
    exact ⟨⟨i, (hS i).2 ⟨x, hi.symm⟩⟩, hi.symm⟩
  have h_mem (i : S) : {x | τ x = (i : ι)} ∈ ℱ i :=
    hτ.measurableSet_eq_of_countable_range h_countable i
  have h_disj : Pairwise (Disjoint on fun i : S ↦ {x | τ x = (i : ι)}) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj ↦ hij (Subtype.ext ?_)
    rw [Set.mem_ofPred_eq] at hxi hxj
    exact WithTop.coe_injective (hxi.symm.trans hxj)
  have h_iUnion : ⋃ i : S, {x | τ x = (i : ι)} = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (h_exists x)
  have h_eq (i : S) {x : Ω} (hx : x ∈ {y | τ y = (i : ι)}) : stoppedValue f τ x = f i x := by
    rw [Set.mem_ofPred_eq] at hx
    simp [stoppedValue, hx]
  -- on `{τ = i}`, the σ-algebra of `τ` agrees with `ℱ i`
  have h_inter (i : S) {s : Set Ω} (hs : s ∈ hτ.sigmaAlgebra) :
      s ∩ {x | τ x = (i : ι)} ∈ ℱ i :=
    (hτ.measurableSet_inter_eq_iff s i).1
      (hτ.sigmaAlgebra.inter_mem hs (hτ.measurableSet_eq_of_countable_range' h_countable i))
  have h_meas : StronglyMeasurable[hτ.sigmaAlgebra] (stoppedValue f τ) := by
    have h_piece (i : S) :
        StronglyMeasurable[hτ.sigmaAlgebra] ({x | τ x = (i : ι)}.indicator (f i)) := by
      refine StronglyMeasurable.stronglyMeasurable_of_sigmaAlgebra_le_on (h_mem i)
        (fun t ht ↦ ?_) ((h.stronglyMeasurable i).indicator (h_mem i))
        fun x hx ↦ Set.indicator_of_notMem hx _
      rw [Set.inter_comm] at ht ⊢
      exact (hτ.measurableSet_inter_eq_iff t i).2 ht
    -- `stoppedValue f τ` is the limit of the finite partial sums of these pieces
    refine stronglyMeasurable_of_tendsto (m := hτ.sigmaAlgebra) (Filter.atTop : Filter (Finset S))
      (fun s ↦ s.stronglyMeasurable_sum fun i _ ↦ h_piece i) (tendsto_pi_nhds.2 fun x ↦ ?_)
    obtain ⟨i, hi⟩ := h_exists x
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨{i}, fun s hs ↦ ?_⟩)
    have h_single : ∀ j ∈ s, j ≠ i → {y | τ y = (j : ι)}.indicator (f j) x = 0 := by
      refine fun j _ hji ↦ Set.indicator_of_notMem (fun hj ↦ hji (Subtype.ext ?_)) _
      rw [Set.mem_ofPred_eq] at hi hj
      exact WithTop.coe_injective (hj.symm.trans hi)
    dsimp only
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem i (Finset.singleton_subset_iff.1 hs)
      h_single, Set.indicator_of_mem hi]
    exact h_eq i hi
  -- `‖f i‖` has at most the integral of `‖f n‖` on `{τ = i}`
  have h_int : Integrable (stoppedValue f τ) μ := by
    refine ⟨(h_meas.mono hτ.sigmaAlgebra_le).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 ?_⟩
    calc ∫⁻ x, ‖stoppedValue f τ x‖ₑ ∂μ
        = ∫⁻ x in ⋃ i : S, {y | τ y = (i : ι)}, ‖stoppedValue f τ x‖ₑ ∂μ := by
          rw [h_iUnion, setLIntegral_univ]
      _ = ∑' i : S, ∫⁻ x in {y | τ y = (i : ι)}, ‖f i x‖ₑ ∂μ := by
          rw [lintegral_iUnion (fun i : S ↦ ℱ.le i (h_mem i)) h_disj]
          exact tsum_congr fun i ↦ setLIntegral_congr_fun (ℱ.le i (h_mem i)) fun x hx ↦
            congrArg (‖·‖ₑ) (h_eq i hx)
      _ ≤ ∑' i : S, ∫⁻ x in {y | τ y = (i : ι)}, ‖f n x‖ₑ ∂μ := by
          refine ENNReal.tsum_le_tsum fun i ↦ ?_
          rw [← ofReal_integral_norm_eq_lintegral_enorm (h.integrable i).restrict,
            ← ofReal_integral_norm_eq_lintegral_enorm (h.integrable n).restrict]
          exact ENNReal.ofReal_le_ofReal <|
            (h.isCondExp (h_le i)).setIntegral_norm_le (ℱ.le i) (h.integrable n) (h_mem i)
      _ = ∫⁻ x, ‖f n x‖ₑ ∂μ := by
          rw [← lintegral_iUnion (fun i : S ↦ ℱ.le i (h_mem i)) h_disj, h_iUnion, setLIntegral_univ]
      _ < ∞ := hasFiniteIntegral_iff_enorm.1 (h.integrable n).2
  refine ⟨h_meas.aestronglyMeasurable, fun s _ _ ↦ h_int.integrableOn, fun s hs _ ↦ ?_⟩
  -- split the integrals along the sets `s ∩ {τ = i} ∈ ℱ i`
  have h_iUnion_s : ⋃ i : S, s ∩ {x | τ x = (i : ι)} = s := by
    rw [← Set.inter_iUnion, h_iUnion, Set.inter_univ]
  have h_meas_s (i : S) : MeasurableSet (s ∩ {x | τ x = (i : ι)}) := ℱ.le i (h_inter i hs)
  have h_disj_s : Pairwise (Disjoint on fun i : S ↦ s ∩ {x | τ x = (i : ι)}) :=
    fun i j hij ↦ (h_disj hij).mono Set.inter_subset_right Set.inter_subset_right
  rw [← h_iUnion_s, integral_iUnion h_meas_s h_disj_s h_int.integrableOn,
    integral_iUnion h_meas_s h_disj_s (h.integrable n).integrableOn]
  refine tsum_congr fun i ↦ ?_
  rw [setIntegral_congr_fun (h_meas_s i) fun x hx ↦ h_eq i hx.2]
  exact h.setIntegral_eq (h_le i) (h_inter i hs)

/-- The value of a martingale `f` at a stopping time `τ` bounded by `n` is a conditional
expectation of `f n` given the σ-algebra of `τ`, for a countable index type. -/
theorem isCondExp_stoppedValue_of_le_const [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) :
    IsCondExp hτ.sigmaAlgebra μ (f n) (stoppedValue f τ) :=
  h.isCondExp_stoppedValue_of_le_const_of_countable_range hτ hτ_le (Set.to_countable _)

/-- `μ[f n | hτ.sigmaAlgebra] = stoppedValue f τ` for a martingale `f`, a stopping time `τ` bounded
by `n` and a countable index type. -/
theorem condExp_eq_stoppedValue_of_le_const [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    (hu : HasUniqueCondExp hτ.sigmaAlgebra μ (f n)) :
    μ[f n | hτ.sigmaAlgebra] = stoppedValue f τ :=
  (h.isCondExp_stoppedValue_of_le_const hτ hτ_le).condExp_eq hu

/-- If `τ` and `σ` are two stopping times with countable range, `σ ≤ τ` and `τ` is bounded, then the
value of a martingale `f` at `σ` is a conditional expectation of its value at `τ` given the
σ-algebra of `σ`. -/
theorem isCondExp_stoppedValue_of_le_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    IsCondExp hσ.sigmaAlgebra μ (stoppedValue f τ) (stoppedValue f σ) := by
  -- both stopped values are conditional expectations of `f n`, and `hσ.sigmaAlgebra` is the
  -- smaller σ-algebra
  have hτ_ce := h.isCondExp_stoppedValue_of_le_const_of_countable_range hτ hτ_le hτ_countable_range
  have hσ_ce := h.isCondExp_stoppedValue_of_le_const_of_countable_range hσ
    (fun x ↦ (hσ_le_τ x).trans (hτ_le x)) hσ_countable_range
  refine ⟨hσ_ce.aestronglyMeasurable,
    fun s hs _ ↦ hσ_ce.integrableOn s hs (h.integrable n).integrableOn, fun s hs _ ↦ ?_⟩
  rw [hσ_ce.setIntegral_eq s hs (h.integrable n).integrableOn,
    hτ_ce.setIntegral_eq s (hσ.sigmaAlgebra_mono hτ hσ_le_τ hs) (h.integrable n).integrableOn]

/-- If `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is bounded, then the value of a
martingale `f` at `σ` is a conditional expectation of its value at `τ` given the σ-algebra of `σ`,
for a countable index type. -/
theorem isCondExp_stoppedValue_of_le [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n) :
    IsCondExp hσ.sigmaAlgebra μ (stoppedValue f τ) (stoppedValue f σ) :=
  h.isCondExp_stoppedValue_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le (Set.to_countable _)
    (Set.to_countable _)

/-- `μ[stoppedValue f τ | hσ.sigmaAlgebra] = stoppedValue f σ` for a martingale `f` and stopping
times `σ ≤ τ` with `τ` bounded, for a countable index type. -/
theorem condExp_stoppedValue_eq_stoppedValue_of_le [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    (hu : HasUniqueCondExp hσ.sigmaAlgebra μ (stoppedValue f τ)) :
    μ[stoppedValue f τ | hσ.sigmaAlgebra] = stoppedValue f σ :=
  (h.isCondExp_stoppedValue_of_le hτ hσ hσ_le_τ hτ_le).condExp_eq hu

end CountableRange

section SubsetOfNat

/-! In the following results the index set verifies
`[LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]`, which means that it is order-isomorphic to
a subset of `ℕ`. `ι` is equipped with the discrete topology, which is also the order topology. -/


variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] [TopologicalSpace ι]
  [DiscreteTopology ι] {ℱ : Filtration ι m} {τ σ : Ω → WithTop ι} {f : ι → Ω → E} {n : ι}

/-- **Optional sampling theorem**. If `τ` is a bounded stopping time and `σ` is another stopping
time, then the value of a martingale `f` at the stopping time `min σ τ` is a conditional
expectation of `f` stopped at `τ` given the σ-algebra of `σ`. -/
theorem isCondExp_stoppedValue_min (h : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ)
    (hσ : IsStoppingTime ℱ σ) (hτ_le : ∀ x, τ x ≤ n) :
    IsCondExp hσ.sigmaAlgebra μ (stoppedValue f τ) (stoppedValue f fun x ↦ min (σ x) (τ x)) := by
  have h_int : Integrable (stoppedValue f τ) μ := integrable_stoppedValue ι hτ h.integrable hτ_le
  -- `stoppedValue f (min σ τ)` is a conditional expectation of `stoppedValue f τ` given the
  -- σ-algebra of `min σ τ`, which is included in that of `σ`
  have h_min := h.isCondExp_stoppedValue_of_le hτ (hσ.min hτ) (fun x ↦ min_le_right _ _) hτ_le
  refine ⟨h_min.aestronglyMeasurable.mono ((hσ.min hτ).sigmaAlgebra_mono hσ
      fun x ↦ min_le_left _ _), fun s _ _ ↦ (h_min.integrable h_int).integrableOn,
    fun s hs _ ↦ ?_⟩
  -- on `s ∩ {σ ≤ τ}`, a set of the σ-algebra of `min σ τ`, use `h_min`; on `s \ {σ ≤ τ}`, the
  -- integrands agree
  have h_le : MeasurableSet {x | σ x ≤ τ x} :=
    hσ.sigmaAlgebra_le (hσ.measurableSet_le_stopping_time hτ)
  rw [← integral_inter_add_sdiff h_le (h_min.integrable h_int).integrableOn,
    ← integral_inter_add_sdiff h_le h_int.integrableOn,
    h_min.setIntegral_eq _ (hσ.measurableSet_inter_le hτ s hs) h_int.integrableOn]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.diff (hσ.sigmaAlgebra_le hs) h_le) fun x hx ↦ ?_
  have hx_lt : τ x < σ x := not_le.1 hx.2
  simp only [stoppedValue, min_eq_right hx_lt.le]

/-- The optional sampling theorem for the conditional expectation as an almost everywhere class:
`μ[stoppedValue f τ | hσ.sigmaAlgebra] = stoppedValue f (min σ τ)` for a martingale `f`, a bounded
stopping time `τ` and a stopping time `σ`. -/
theorem condExp_stoppedValue_eq_stoppedValue_min (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hτ_le : ∀ x, τ x ≤ n)
    (hu : HasUniqueCondExp hσ.sigmaAlgebra μ (stoppedValue f τ)) :
    μ[stoppedValue f τ | hσ.sigmaAlgebra] = stoppedValue f fun x ↦ min (σ x) (τ x) :=
  (h.isCondExp_stoppedValue_min hτ hσ hτ_le).condExp_eq hu

/-- For a martingale `f`, a stopping time `τ` bounded by `n` and a stopping time `σ`, every
conditional expectation of `stoppedValue f τ` given the σ-algebra of `σ` agrees almost everywhere
with `stoppedValue f τ` on `{τ ≤ σ}`. -/
theorem ae_eq_restrict_le_of_isCondExp_stoppedValue (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hτ_le : ∀ x, τ x ≤ n) {g : Ω → E}
    (hg : IsCondExp hσ.sigmaAlgebra μ (stoppedValue f τ) g) :
    g =ᵐ[μ.restrict {x | τ x ≤ σ x}] stoppedValue f τ := by
  have h_ae := hg.ae_eq hσ.sigmaAlgebra_le (integrable_stoppedValue ι hτ h.integrable hτ_le)
    (h.isCondExp_stoppedValue_min hτ hσ hτ_le)
  rw [Filter.EventuallyEq,
    ae_restrict_iff' (hσ.sigmaAlgebra_le (hτ.measurableSet_stopping_time_le hσ))]
  filter_upwards [h_ae] with x hx hx_le
  rw [hx]
  simp only [stoppedValue, min_eq_right hx_le]

end SubsetOfNat

end Martingale

end MeasureTheory

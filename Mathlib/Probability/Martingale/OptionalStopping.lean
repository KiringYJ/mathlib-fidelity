/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic

/-! # Optional stopping theorem (fair game theorem)

The optional stopping theorem states that a strongly adapted integrable process `f` is a
submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f * n ω = max_{k ≤ n}, f k ω`.

### Main results

* `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`: the optional stopping theorem.
* `MeasureTheory.Submartingale.stoppedProcess`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `MeasureTheory.maximal_ineq`: Doob's maximal inequality.

-/

public section


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : SigmaAlgebra Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
  {τ π : Ω → WithTop ℕ}

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stoppedValue f τ` is less than or equal to the expectation of `stoppedValue f π`.
This is the forward direction of the optional stopping theorem. -/
theorem Submartingale.expected_stoppedValue_mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] {f : ℕ → Ω → E}
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) : ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ := by
  rw [← sub_nonneg, ← integral_sub', stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have this i : {ω : Ω | τ ω ≤ i ∧ i < π ω} ∈ 𝒢 i := by
      simp_rw [Set.ofPred_and, ← not_le, ← Set.compl_ofPred]
      exact (𝒢 i).inter_mem (hτ i) ((𝒢 i).compl_mem (hπ i))
    rw [integral_finsetSum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ (this _)), integral_sub', sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (this _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    intro i _
    exact Integrable.indicator (Integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ (this _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ fun ω => le_trans (hle ω) (hbdd ω)

/-- The converse direction of the optional stopping theorem, i.e. a strongly adapted integrable
process `f` is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ τ π : Ω → WithTop ℕ, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) → ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ ↦ WithTop.some i) fun _ ↦ WithTop.some j) _
    (isStoppingTime_piecewise_const hij hs) (isStoppingTime_const 𝒢 j)
    (Set.piecewise_le (fun _ _ ↦ WithTop.coe_le_coe.mpr hij) fun _ _ ↦ le_rfl)
    ⟨j, fun _ => le_rfl⟩
  rwa [stoppedValue_const, stoppedValue_piecewise_const,
    integral_piecewise (𝒢.le _ hs) (hint _).integrableOn (hint _).integrableOn, ←
    integral_add_compl (𝒢.le _ hs) (hint j), add_le_add_iff_right] at hf

/-- **The optional stopping theorem** (fair game theorem): a strongly adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → WithTop ℕ, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

/-- The stopped process at time `n`, minus the initial value, is the sum of the increments of `u`
before the stopping time. -/
theorem stoppedProcess_sub_eq_sum {β : Type*} [AddCommGroup β] (u : ℕ → Ω → β) (n : ℕ) :
    stoppedProcess u τ n - u 0 =
      ∑ i ∈ Finset.range n, {ω | (i : WithTop ℕ) < τ ω}.indicator (u (i + 1) - u i) := by
  induction n with
  | zero => ext ω; simp [stoppedProcess]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h
    · have h' : WithTop.some (n + 1) ≤ τ ω := by
        induction hx : τ ω using WithTop.recTopCoe with
        | top => exact le_top
        | coe t =>
          rw [hx] at h
          simp only [Nat.cast_withTop, WithTop.coe_lt_coe] at h
          exact WithTop.coe_le_coe.2 h
      rw [stoppedProcess_eq_of_le (i := n + 1) h', stoppedProcess_eq_of_le (i := n) h.le]
      abel
    · have h' : τ ω ≤ n := not_lt.1 h
      rw [stoppedProcess_eq_of_ge (i := n + 1) (h'.trans (WithTop.coe_le_coe.2 n.le_succ)),
        stoppedProcess_eq_of_ge (i := n) h', add_zero]

/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. It is
the initial value plus the transform of the submartingale by the indicators of the events before
the stopping time (`MeasureTheory.stoppedProcess_sub_eq_sum`), so no σ-finiteness is needed. -/
protected theorem Submartingale.stoppedProcess {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] [ClosedIciTopology E] {f : ℕ → Ω → E} (h : Submartingale f 𝒢 μ)
    (hτ : IsStoppingTime 𝒢 τ) : Submartingale (stoppedProcess f τ) 𝒢 μ := by
  have hξ : StronglyAdapted 𝒢 fun k ↦ {ω | (k : WithTop ℕ) < τ ω}.indicator fun _ ↦ (1 : ℝ) :=
    fun k ↦ stronglyMeasurable_const.indicator (hτ.measurableSet_gt k)
  have h_sum := h.sum_smul_sub hξ (R := 1)
    (fun _ _ ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) _)
    fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have h_eq : stoppedProcess f τ = (fun _ ↦ f 0) + fun n ↦ ∑ k ∈ Finset.range n,
      {ω | (k : WithTop ℕ) < τ ω}.indicator (fun _ ↦ (1 : ℝ)) • (f (k + 1) - f k) := by
    funext n
    change stoppedProcess f τ n = f 0 + ∑ k ∈ Finset.range n, _
    rw [← sub_eq_iff_eq_add', stoppedProcess_sub_eq_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ext ω
    by_cases hω : (k : WithTop ℕ) < τ ω <;> simp [hω]
  rw [h_eq]
  exact (martingale_const_fun 𝒢 μ (h.stronglyAdapted 0) (h.integrable 0)).submartingale.add h_sum

section Maximal

open Finset

theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : ℝ≥0}
    (n : ℕ) : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
      (ε : ℝ) ≤ stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_ofPred_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ => (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (mod_cast hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcoming PR). -/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0}
    (n : ℕ) : ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) := by
  suffices ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) ≤
      ENNReal.ofReal (∫ ω, f n ω ∂μ) by
    have hadd : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ENNReal.ofReal
        (∫ ω in {ω | ε ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ]
        convert! rfl
        ext ω
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    _ ≤ ENNReal.ofReal
          (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (mod_cast hittingBtwn_le)
        exact hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      · exact nullMeasurableSet_lt (measurable_range_sup'' fun n _ ↦
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_ofPred_eq] at hω
      have : hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω = n := by
        simp only [hittingBtwn, Set.mem_ofPred_eq, ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add, ← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert! rfl
        ext ω
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ)
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (mod_cast hittingBtwn_le))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (mod_cast hittingBtwn_le))
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ ≤ ENNReal.ofReal (∫ ω, f n ω ∂μ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω ↦ ?_) (fun _ ↦ le_rfl)
      simp [hittingBtwn_le]

end Maximal

end MeasureTheory

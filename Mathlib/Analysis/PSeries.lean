/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SumOverResidueClass

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## Tags

p-series, Cauchy condensation test
-/

@[expose] public section

/-!
### Schlömilch's generalization of the Cauchy condensation test

In this section we prove the Schlömilch's generalization of the Cauchy condensation test:
for a strictly increasing `u : ℕ → ℕ` with ratio of successive differences bounded and an
antitone `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`, `∑ k, f k` converges if and only if
so does `∑ k, (u (k + 1) - u k) * f (u k)`. Instead of giving a monolithic proof, we split it
into a series of lemmas with explicit estimates of partial sums of each series in terms of the
partial sums of the other series.
-/

/--
A sequence `u` has the property that its ratio of successive differences is bounded
when there is a positive real number `C` such that, for all n ∈ ℕ,
(u (n + 2) - u (n + 1)) ≤ C * (u (n + 1) - u n)
-/
def SuccDiffBounded (C : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, u (n + 2) - u (n + 1) ≤ C • (u (n + 1) - u n)

namespace Finset

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {f : ℕ → M} {u : ℕ → ℕ}

theorem le_sum_schlomilch' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ Ico (u 0) (u n), f k) ≤ ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (∑ k ∈ Ico (u n) (u (n + 1)), f k) ≤ (u (n + 1) - u n) • f (u n) by
      rw [sum_range_succ, ← sum_Ico_consecutive]
      · exact add_le_add ihn this
      exacts [hu n.zero_le, hu n.le_succ]
    have : ∀ k ∈ Ico (u n) (u (n + 1)), f k ≤ f (u n) := fun k hk =>
      hf (Nat.succ_le_of_lt (h_pos n)) (mem_Ico.mp hk).1
    convert! sum_le_sum this
    simp

theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ Ico 1 (2 ^ n), f k) ≤ ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by
  convert!
    le_sum_schlomilch' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

theorem le_sum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range (u n), f k) ≤
      ∑ k ∈ range (u 0), f k + ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by
  grw [← le_sum_schlomilch' hf h_pos hu n, ← sum_range_add_sum_Ico _ (hu n.zero_le)]

theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (2 ^ n), f k) ≤ f 0 + ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by
  grw [← le_sum_condensed' hf n, ← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ,
    sum_range_zero, zero_add]

theorem sum_schlomilch_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range n, (u (k + 1) - u k) • f (u (k + 1))) ≤ ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (u (n + 1) - u n) • f (u (n + 1)) ≤ ∑ k ∈ Ico (u n + 1) (u (n + 1) + 1), f k by
      rw [sum_range_succ, ← sum_Ico_consecutive]
      exacts [add_le_add ihn this,
        (add_le_add_left (hu n.zero_le) _ : u 0 + 1 ≤ u n + 1),
        add_le_add_left (hu n.le_succ) _]
    have : ∀ k ∈ Ico (u n + 1) (u (n + 1) + 1), f (u (n + 1)) ≤ f k := fun k hk =>
      hf (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (h_pos n)) <| (Nat.lt_succ_of_le le_rfl).trans_le
        (mem_Ico.mp hk).1) (Nat.le_of_lt_succ <| (mem_Ico.mp hk).2)
    convert! sum_le_sum this
    simp

theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by
  convert!
    sum_schlomilch_le' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

theorem sum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) (n : ℕ) :
    ∑ k ∈ range (n + 1), (u (k + 1) - u k) • f (u k) ≤
    (u 1 - u 0) • f (u 0) + C • ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by
  rw [sum_range_succ', add_comm]
  gcongr
  suffices ∑ k ∈ range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
  C • ∑ k ∈ range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : ∀ k ∈ range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) ≤
    C • ((u (k + 1) - u k) • f (u (k + 1))) := by
    intro k _
    rw [smul_smul]
    gcongr
    · exact h_nonneg (u (k + 1))
    exact mod_cast h_succ_diff k
  convert! sum_le_sum this
  simp [smul_sum]

theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by
  grw [← sum_condensed_le' hf n]
  simp [sum_range_succ', add_comm, pow_succ', mul_nsmul', sum_nsmul]

end Finset

namespace ENNReal

open Filter Finset

variable {u : ℕ → ℕ} {f : ℕ → ℝ≥0∞}

theorem le_tsum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : StrictMono u) :
    ∑' k, f k ≤ ∑ k ∈ range (u 0), f k +
      ∑' k : ℕ, ((u (k + 1) - u k : ℕ) : ℝ≥0∞) * f (u k) := by
  rw [ENNReal.tsum_eq_iSup_nat' hu.tendsto_atTop]
  refine iSup_le fun n => ?_
  grw [Finset.le_sum_schlomilch hf h_pos hu.monotone n]
  gcongr
  simp only [nsmul_eq_mul]
  apply ENNReal.sum_le_tsum

theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    ∑' k, f k ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine iSup_le fun n => (Finset.le_sum_condensed hf n).trans ?_
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  grw [ENNReal.sum_le_tsum]

theorem tsum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) :
    ∑' k : ℕ, ((u (k + 1) - u k : ℕ) : ℝ≥0∞) * f (u k) ≤
      ((u 1 - u 0 : ℕ) : ℝ≥0∞) * f (u 0) + (C : ℝ≥0∞) * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)]
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu h_succ_diff n

theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id), two_mul, ← two_nsmul]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)]
  simpa using Finset.sum_condensed_le hf n

end ENNReal

namespace NNReal

open Finset

open ENNReal in
/-- for a series of `NNReal` version. -/
theorem summable_schlomilch_iff {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ≥0}
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m)
    (h_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ≥0)) * f (u k)) ↔ Summable f := by
  simp only [← tsum_coe_ne_top_iff_summable, Ne, not_iff_not, ENNReal.coe_mul,
    ← Nat.cast_tsub, ENNReal.coe_natCast]
  constructor <;> intro h
  · replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    have h_nonneg : ∀ n, 0 ≤ (f n : ℝ≥0∞) := fun n =>
      ENNReal.coe_le_coe.2 (f n).2
    obtain hC := tsum_schlomilch_le hf h_pos h_nonneg hu_strict.monotone h_succ_diff
    simpa [add_eq_top, mul_ne_top, mul_eq_top, hC_nonzero] using eq_top_mono hC h
  · replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf hm hmn)
    have : ∑ k ∈ range (u 0), (f k : ℝ≥0∞) ≠ ∞ := sum_ne_top.2 fun a _ => coe_ne_top
    simpa [h, add_eq_top, this] using le_tsum_schlomilch hf h_pos hu_strict

open ENNReal in
theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ≥0) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff hf (pow_pos zero_lt_two) (pow_right_strictMono₀ _root_.one_lt_two)
      two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

end NNReal

open NNReal in
/-- for series of nonnegative real numbers. -/
theorem summable_schlomilch_iff_of_nonneg {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ)) * f (u k)) ↔ Summable f := by
  lift f to ℕ → ℝ≥0 using h_nonneg
  simp only [NNReal.coe_le_coe] at *
  have (k : ℕ) : (u (k + 1) - (u k : ℝ)) = ((u (k + 1) : ℝ≥0) - (u k : ℝ≥0) : ℝ≥0) := by
    have := Nat.cast_le (α := ℝ≥0).mpr <| (hu_strict k.lt_succ_self).le
    simp [NNReal.coe_sub this]
  simp_rw [this]
  exact_mod_cast NNReal.summable_schlomilch_iff hf h_pos hu_strict hC_nonzero h_succ_diff

/-- Cauchy condensation test for antitone series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff_of_nonneg h_nonneg h_mono (pow_pos zero_lt_two)
      (pow_right_strictMono₀ one_lt_two) two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

/-- Cauchy condensation test for eventually antitone and nonnegative series of real numbers. -/
theorem summable_condensed_iff_of_eventually_nonneg {f : ℕ → ℝ} (h_nonneg : 0 ≤ᶠ[Filter.atTop] f)
    (h_mono : ∀ᶠ k in Filter.atTop, f (k + 1) ≤ f k) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by
  rw [Filter.EventuallyLE, Filter.eventually_atTop] at h_nonneg
  rw [Filter.eventually_atTop] at h_mono
  rcases h_nonneg with ⟨n, hn⟩
  rcases h_mono with ⟨m, hm⟩
  convert! summable_condensed_iff_of_nonneg (f := fun k ↦ f (max k (n + m))) _ _ using 1
  · rw [summable_congr_atTop]
    have h_pow := tendsto_pow_atTop_atTop_of_one_lt (r := 2) (by simp)
    filter_upwards [h_pow.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · rw [summable_congr_atTop]
    filter_upwards [Filter.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · simp_all
  · intro _ _ _ _
    exact antitoneOn_nat_Ici_of_succ_le (k := n + m) (by grind) (by simp) (by simp) (by grind)

section p_series

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

namespace Real

open Filter

/-- Cauchy condensation determines the summability of real powers. -/
@[simp]
theorem summable_nat_rpow {p : ℝ} : Summable (fun n => (n : ℝ) ^ p : ℕ → ℝ) ↔ p < -1 := by
  rcases le_or_gt p 0 with hp | hp
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_natCast, ← rpow_mul zero_lt_two.le,
        mul_comm _ p, rpow_mul zero_lt_two.le, rpow_natCast, ← mul_pow,
        summable_geometric_iff_norm_lt_one]
      rw [norm_eq_abs, abs_of_pos (mul_pos two_pos (rpow_pos_of_pos two_pos p))]
      nth_rw 1 [← rpow_one 2]
      rw [← rpow_add two_pos, rpow_lt_one_iff zero_lt_two.le]
      norm_num; constructor <;> intro h <;> linarith
    · intro n
      positivity
    · intro m n hm hmn
      exact rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmn) hp
  · have hnot : ¬Summable (fun n : ℕ ↦ (n : ℝ) ^ p) := by
      intro h
      obtain ⟨k, hk, hk0⟩ := ((h.tendsto_cofinite_zero.eventually
        (gt_mem_nhds zero_lt_one)).and (eventually_cofinite_ne (0 : ℕ))).exists
      exact (not_lt_of_ge (one_le_rpow
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0) hp.le)) hk
    simpa only [hnot, false_iff] using (not_lt_of_ge (by linarith : -1 ≤ p))

/-- The reciprocal real `p`-series is indexed by the positive integers. -/
@[simp]
theorem summable_nat_rpow_inv {p : ℝ} :
    Summable (fun n : ℕ+ ↦ Checked.inv (((n : ℕ) : ℝ) ^ p)
      (rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) p).isUnit) ↔ 1 < p := by
  rw [← Equiv.pnatEquivNat.symm.summable_iff]
  change Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ p)⁻¹) ↔ 1 < p
  have hterm (n : ℕ) : (((n + 1 : ℕ) : ℝ) ^ p)⁻¹ = ((n + 1 : ℕ) : ℝ) ^ (-p) :=
    (rpow_neg (by positivity) p).symm
  simp_rw [hterm]
  have hshift := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-p))).trans
    (summable_nat_rpow (p := -p))
  simpa only [Nat.cast_add, Nat.cast_one, neg_lt_neg_iff] using hshift

/-- The real reciprocal `p`-series converges exactly for `p > 1`. -/
theorem summable_one_div_nat_rpow {p : ℝ} :
    Summable (fun n : ℕ+ ↦ Checked.div 1 (((n : ℕ) : ℝ) ^ p)
      (rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) p).isUnit) ↔ 1 < p := by
  simpa only [one_div₀] using summable_nat_rpow_inv (p := p)

/-- The successor-indexed real reciprocal power series. -/
theorem summable_one_div_nat_add_one_rpow {p : ℝ} :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ p) ↔ 1 < p := by
  have he := Equiv.pnatEquivNat.symm.summable_iff
    (f := fun n : ℕ+ ↦ Checked.div 1 (((n : ℕ) : ℝ) ^ p)
      (rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) p).isUnit)
  have hshift : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ p) ↔
      Summable (fun n : ℕ+ ↦ Checked.div 1 (((n : ℕ) : ℝ) ^ p)
        (rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) p).isUnit) := by
    simpa only [Function.comp_def, Equiv.pnatEquivNat, Equiv.coe_fn_symm_mk,
      Nat.succPNat_coe, Nat.cast_succ] using he
  exact hshift.trans summable_one_div_nat_rpow

/-- The reciprocal natural-power series on the positive integers. -/
@[simp]
theorem summable_nat_pow_inv {p : ℕ} :
    Summable (fun n : ℕ+ ↦ (((n : ℕ) : ℝ) ^ p)⁻¹) ↔ 1 < p := by
  simpa only [rpow_natCast, Nat.one_lt_cast] using summable_nat_rpow_inv (p := (p : ℝ))

/-- The reciprocal natural-power series on the positive integers. -/
theorem summable_one_div_nat_pow {p : ℕ} :
    Summable (fun n : ℕ+ ↦ 1 / ((n : ℕ) : ℝ) ^ p) ↔ 1 < p := by
  simpa only [one_div₀] using summable_nat_pow_inv (p := p)

theorem summable_abs_int_rpow {b : ℝ} (hb : 1 < b) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (-b) := by
  apply Summable.of_nat_of_neg
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  all_goals
    simp_rw [Int.cast_natCast, fun n : ℕ => abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))]
    rwa [summable_nat_rpow, neg_lt_neg_iff]

/-- Harmonic series is not unconditionally summable. -/
theorem not_summable_natCast_inv : ¬Summable (fun n : ℕ+ => ((n : ℕ) : ℝ)⁻¹) := by
  have : ¬Summable (fun n : ℕ+ => (((n : ℕ) : ℝ) ^ 1)⁻¹) :=
    mt (summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa

/-- Harmonic series is not unconditionally summable. -/
theorem not_summable_one_div_natCast : ¬Summable (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ)) := by
  simpa only [inv_eq_one_div₀] using not_summable_natCast_inv

/-- **Divergence of the Harmonic Series** -/
theorem tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · simpa only [rpow_one] using
      (mt (summable_one_div_nat_add_one_rpow (p := 1)).mp (by norm_num : ¬(1 : ℝ) < 1))
  · exact fun i => by positivity

end Real

namespace NNReal

@[simp]
theorem summable_rpow_inv {p : ℝ} :
    Summable (fun n : ℕ+ => (((n : ℕ) : ℝ≥0) ^ p)⁻¹) ↔ 1 < p := by
  simp [← NNReal.summable_coe]

@[simp]
theorem summable_rpow {p : ℝ} : Summable (fun n => (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ p < -1 := by
  simp [← NNReal.summable_coe]

theorem summable_one_div_rpow {p : ℝ} :
    Summable (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ≥0) ^ p) ↔ 1 < p := by
  simp

end NNReal

end p_series

section

open Finset

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

private theorem sum_range_inv_sq_le_sub {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    (∑ i ∈ range m, (((k + i + 1 : ℕ) : α) ^ 2)⁻¹) ≤
      (k : α)⁻¹ - ((k + m : ℕ) : α)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hk' : (0 : α) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hm : (0 : α) < k + m := add_pos_of_pos_of_nonneg hk' (Nat.cast_nonneg m)
    have hdiff : (k + m : α)⁻¹ - (k + m + 1 : α)⁻¹ =
        ((k + m : α) * (k + m + 1))⁻¹ := by field
    have hstep : ((k + m + 1 : α) ^ 2)⁻¹ ≤
        (k + m : α)⁻¹ - (k + m + 1 : α)⁻¹ := by
      rw [hdiff]
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      nlinarith
    rw [sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    calc
      _ ≤ ((k : α)⁻¹ - (k + m : α)⁻¹) +
          ((k + m : α)⁻¹ - (k + m + 1 : α)⁻¹) := add_le_add ih hstep
      _ = _ := by simp only [add_assoc]; ring

theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (∑ i : Ioc k n, Checked.inv (((i : ℕ) : α) ^ 2)
      ((Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.zero_le k).trans_lt
        (Finset.mem_Ioc.mp i.2).1))).isUnit.pow 2)) ≤
      (k : α)⁻¹ - Checked.inv (n : α)
        (Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.pos_of_ne_zero hk).trans_le h))).isUnit := by
  let e : Ioc k n ≃ Fin (n - k) :=
    { toFun := fun i ↦ ⟨(i : ℕ) - k - 1, by have := i.2; simp only [mem_Ioc] at this; omega⟩
      invFun := fun j ↦ ⟨k + j + 1, by simp only [mem_Ioc]; have := j.2; omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        have hi := mem_Ioc.mp i.2
        dsimp
        omega
      right_inv := by intro j; apply Fin.ext; dsimp; omega }
  have heq : (∑ i : Ioc k n, Checked.inv (((i : ℕ) : α) ^ 2)
      ((Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.zero_le k).trans_lt
        (Finset.mem_Ioc.mp i.2).1))).isUnit.pow 2)) =
      ∑ j : Fin (n - k), (((k + (j : ℕ) + 1 : ℕ) : α) ^ 2)⁻¹ := by
    apply Fintype.sum_equiv e
    intro i
    have hi := i.2
    simp only [mem_Ioc] at hi
    have hval : k + (e i : ℕ) + 1 = (i : ℕ) := by dsimp [e]; omega
    simp only [hval]
  rw [heq]
  calc
    _ = ∑ j ∈ range (n - k), (((k + j + 1 : ℕ) : α) ^ 2)⁻¹ :=
      Fin.sum_univ_eq_sum_range _ _
    _ ≤ _ := by
      simpa only [Nat.add_sub_of_le h] using sum_range_inv_sq_le_sub (α := α) hk (n - k)

private theorem sum_range_inv_sq_le (k m : ℕ) :
    (∑ i ∈ range m, (((k + i + 1 : ℕ) : α) ^ 2)⁻¹) ≤ 2 / ((k : α) + 1) := by
  cases m with
  | zero =>
    simp only [range_zero, sum_empty]
    positivity
  | succ m =>
    rw [sum_range_succ']
    have htail := sum_range_inv_sq_le_sub (α := α) (k := k + 1) (by omega) m
    have hsum : (∑ i ∈ range m, (((k + (i + 1) + 1 : ℕ) : α) ^ 2)⁻¹) =
        ∑ i ∈ range m, ((((k + 1) + i + 1 : ℕ) : α) ^ 2)⁻¹ := by
      congr 1
      ext i
      congr 3
      omega
    rw [hsum]
    grw [htail]
    have hk : (1 : α) ≤ k + 1 := by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
    have hm : (0 : α) < k + 1 + m := by positivity
    push_cast
    have hsq : ((k + 1 : α) ^ 2)⁻¹ ≤ (k + 1 : α)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hnonneg : (0 : α) ≤ (k + 1 + m : α)⁻¹ := by positivity
    rw [div_eq_mul_inv₀]
    simp only [add_zero]
    linarith

theorem sum_Ioo_inv_sq_le (k n : ℕ) :
    (∑ i : Ioo k n, Checked.inv (((i : ℕ) : α) ^ 2)
      ((Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.zero_le k).trans_lt
        (Finset.mem_Ioo.mp i.2).1))).isUnit.pow 2)) ≤ 2 / ((k : α) + 1) := by
  let e : Ioo k n ≃ Fin (n - (k + 1)) :=
    { toFun := fun i ↦ ⟨(i : ℕ) - (k + 1), by have := i.2; simp only [mem_Ioo] at this; omega⟩
      invFun := fun j ↦ ⟨k + j + 1, by simp only [mem_Ioo]; have := j.2; omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        have hi := mem_Ioo.mp i.2
        dsimp
        omega
      right_inv := by intro j; apply Fin.ext; dsimp; omega }
  have heq : (∑ i : Ioo k n, Checked.inv (((i : ℕ) : α) ^ 2)
      ((Nat.cast_ne_zero.mpr (ne_of_gt ((Nat.zero_le k).trans_lt
        (Finset.mem_Ioo.mp i.2).1))).isUnit.pow 2)) =
      ∑ j : Fin (n - (k + 1)), (((k + (j : ℕ) + 1 : ℕ) : α) ^ 2)⁻¹ := by
    apply Fintype.sum_equiv e
    intro i
    have hi := i.2
    simp only [mem_Ioo] at hi
    have hval : k + (e i : ℕ) + 1 = (i : ℕ) := by dsimp [e]; omega
    simp only [hval]
  rw [heq]
  calc
    _ = ∑ j ∈ range (n - (k + 1)), (((k + j + 1 : ℕ) : α) ^ 2)⁻¹ :=
      Fin.sum_univ_eq_sum_range _ _
    _ ≤ _ := sum_range_inv_sq_le k (n - (k + 1))

end

open Set Nat in
/-- The harmonic series restricted to a residue class is not summable. -/
lemma Real.not_summable_one_div_natCast_residueClass {m : ℕ} (hm : m ≠ 0) (k : ZMod m) :
    ¬ Summable (fun n : {n : ℕ+ // ((n : ℕ) : ZMod m) = k} ↦
      1 / (((n : ℕ+) : ℕ) : ℝ)) := by
  let : NeZero m := ⟨hm⟩
  have hnot : ¬ Summable ({n : ℕ | (n : ZMod m) = k - 1}.indicator
      (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))) := by
    rw [summable_indicator_mod_iff (fun n₁ n₂ h ↦ by gcongr) (k - 1)]
    simpa only [Real.rpow_one] using
      (mt (Real.summable_one_div_nat_add_one_rpow (p := 1)).mp
        (by norm_num : ¬(1 : ℝ) < 1))
  intro h
  let toPositive : {n : ℕ // (n : ZMod m) = k - 1} →
      {n : ℕ+ // ((n : ℕ) : ZMod m) = k} := fun n ↦
    ⟨Nat.succPNat n, by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using (eq_sub_iff_add_eq.mp n.2)⟩
  have htoPositive : Function.Injective toPositive := by
    intro n₁ n₂ heq
    apply Subtype.ext
    have hv := congrArg
      (fun n : {n : ℕ+ // ((n : ℕ) : ZMod m) = k} ↦ ((n.1 : ℕ+) : ℕ)) heq
    dsimp only [toPositive] at hv
    exact Nat.succ.inj (by simpa only [Nat.succPNat_coe] using hv)
  have hsub : Summable (fun n : {n : ℕ // (n : ZMod m) = k - 1} ↦
      1 / (((n : ℕ) : ℝ) + 1)) := by
    convert h.comp_injective htoPositive using 1
    funext n
    simp only [toPositive, Function.comp_def, Nat.succPNat_coe, Nat.cast_succ]
  apply hnot
  exact (summable_subtype_iff_indicator
    (s := {n : ℕ | (n : ZMod m) = k - 1}) (f := fun n : ℕ ↦ 1 / ((n : ℝ) + 1))).mp hsub

/-!
## Translating the `p`-series by a real number
-/
section shifted

open Filter Asymptotics

lemma Real.summable_one_div_nat_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦ 1 / |(n : ℕ) + a| ^ s) ↔ 1 < s := by
  have hnorm : Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have h_abs : (fun n : ℕ ↦ |n + a|) ~[atTop] (·) := by
    refine (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm (c := a)).congr_left ?_
    filter_upwards [eventually_gt_atTop (Nat.ceil |a|)] with n hn
    have hna : |a| < (n : ℝ) := Nat.lt_of_ceil_lt hn
    have hpos : 0 < (n : ℝ) + a := by linarith only [hna, neg_le_abs a]
    rw [abs_of_pos hpos]
  have h_next : (fun n : ℕ ↦ (n : ℝ) + 1) ~[atTop] fun n ↦ (n : ℝ) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
  let D := {n : ℕ // (n : ℝ) + a ≠ 0}
  have hcoe : Tendsto (Subtype.val : D → ℕ) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Subtype.val_injective.tendsto_cofinite
  have hp : (fun n : D ↦ |(n : ℕ) + a| ^ (-s)) ~[cofinite]
      (fun n : D ↦ ((n : ℕ) + 1 : ℝ) ^ (-s)) :=
    IsEquivalent.rpow (fun n : D ↦ add_nonneg (Nat.cast_nonneg _) zero_le_one)
      ((h_abs.trans h_next.symm).comp_tendsto hcoe)
  have hquot : (fun n : D ↦ 1 / |(n : ℕ) + a| ^ s) ~[cofinite]
      (fun n : D ↦ ((n : ℕ) + 1 : ℝ) ^ (-s)) := by
    apply hp.congr_left
    filter_upwards [] with n
    have hu : IsUnit (|(n : ℕ) + a| ^ s) :=
      (rpow_ne_zero_of_pos (abs_pos.mpr n.2) s).isUnit
    rw [one_div₀, rpow_neg (abs_nonneg _)]
  have hfinite : Set.Finite {n : ℕ | (n : ℝ) + a = 0} := by
    apply Set.Subsingleton.finite
    intro n hn m hm
    exact Nat.cast_injective (add_right_cancel (hn.trans hm.symm))
  rw [hquot.summable_iff]
  have hrestrict : Summable (fun n : D ↦ ((n : ℕ) + 1 : ℝ) ^ (-s)) ↔
      Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-s)) :=
    hfinite.summable_compl_iff (f := fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-s))
  rw [hrestrict]
  have hshift := (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-s))).trans
    (Real.summable_nat_rpow (p := -s))
  simpa only [Nat.cast_add, Nat.cast_one, neg_lt_neg_iff] using hshift

lemma Real.summable_one_div_int_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦ 1 / |(n : ℤ) + a| ^ s) ↔ 1 < s := by
  let e : {n : ℤ // (n : ℝ) + a ≠ 0} ≃
      {n : ℕ // (n : ℝ) + a ≠ 0} ⊕ {n : ℕ // (n : ℝ) + (1 - a) ≠ 0} :=
    { toFun := fun n ↦ match n with
        | ⟨Int.ofNat m, hm⟩ => Sum.inl ⟨m, by
            simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hm⟩
        | ⟨Int.negSucc m, hm⟩ => Sum.inr ⟨m, by
            intro h
            apply hm
            push_cast
            linear_combination -h⟩
      invFun := fun n ↦ match n with
        | Sum.inl m => ⟨Int.ofNat m, by
            simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using m.2⟩
        | Sum.inr m => ⟨Int.negSucc m, by
            intro h
            apply m.2
            push_cast at h
            linear_combination -h⟩
      left_inv := by rintro ⟨n, hn⟩; cases n <;> rfl
      right_inv := by rintro (⟨n, hn⟩ | ⟨n, hn⟩) <;> rfl }
  have hneg (n : ℕ) : |(Int.negSucc n : ℝ) + a| = |(n : ℝ) + (1 - a)| := by
    rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one,
      show -((n : ℝ) + 1) + a = -((n : ℝ) + (1 - a)) by ring, abs_neg]
  rw [← e.symm.summable_iff]
  have hfun : ((fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      1 / |(n : ℤ) + a| ^ s) ∘ e.symm) = Sum.elim
      (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦ 1 / |(n : ℕ) + a| ^ s)
      (fun n : {n : ℕ // (n : ℝ) + (1 - a) ≠ 0} ↦
        1 / |(Int.negSucc (n : ℕ) : ℝ) + a| ^ s) := by
    funext n
    cases n <;> simp [e, Int.ofNat_eq_natCast]
  rw [hfun]
  simp_rw [hneg]
  constructor
  · intro h
    apply (summable_one_div_nat_add_rpow a s).mp
    exact h.comp_injective Sum.inl_injective
  · intro hs
    apply Summable.sum
    · exact (summable_one_div_nat_add_rpow a s).mpr hs
    · exact (summable_one_div_nat_add_rpow (1 - a) s).mpr hs

/-- The integer reciprocal power series omits its zero denominator. -/
theorem Real.summable_one_div_int_pow {p : ℕ} :
    (Summable fun n : {n : ℤ // n ≠ 0} ↦ 1 / ((n : ℤ) : ℝ) ^ p) ↔ 1 < p := by
  rw [← summable_norm_iff]
  let e : {n : ℤ // n ≠ 0} ≃ {n : ℤ // (n : ℝ) + 0 ≠ 0} :=
    Equiv.subtypeEquivRight (fun n ↦ by simp only [add_zero, Int.cast_ne_zero])
  have hseries : (Summable fun n : {n : ℤ // n ≠ 0} ↦
      1 / |((n : ℤ) : ℝ) + 0| ^ (p : ℝ)) ↔ 1 < (p : ℝ) :=
    e.summable_iff.trans (Real.summable_one_div_int_add_rpow 0 (p : ℝ))
  simpa only [Function.comp_def, e, add_zero, norm_div, norm_one, norm_pow,
    Real.norm_eq_abs, rpow_natCast, Nat.one_lt_cast] using hseries

theorem summable_pow_div_add {α : Type*} (x : α) [RCLike α] (q k : ℕ) (hq : 1 < q) :
    Summable fun n : {n : ℕ // n + k ≠ 0} ↦
      ‖Checked.div x (((n : ℕ) + k : α) ^ q)
        (pow_ne_zero q (by exact_mod_cast n.2)).isUnit‖ := by
  let e : {n : ℕ // n + k ≠ 0} ≃ {n : ℕ // (n : ℝ) + k ≠ 0} :=
    Equiv.subtypeEquivRight (fun n ↦ by
      rw [← Nat.cast_add, Nat.cast_ne_zero])
  have hsum := e.summable_iff.mpr
    ((Real.summable_one_div_nat_add_rpow (k : ℝ) (q : ℝ)).mpr (by exact_mod_cast hq))
  convert hsum.mul_left ‖x‖ using 1
  funext n
  have hbase : ((n : ℕ) : α) + k ≠ 0 := by exact_mod_cast n.2
  have hreal : ((n : ℕ) : ℝ) + k ≠ 0 := by exact_mod_cast n.2
  have hnonneg : (0 : ℝ) ≤ ((n : ℕ) : ℝ) + k :=
    add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hrpow : IsUnit (|((n : ℕ) : ℝ) + k| ^ (q : ℝ)) :=
    (Real.rpow_ne_zero_of_pos (abs_pos.mpr hreal) _).isUnit
  change ‖x / (((n : ℕ) : α) + k) ^ q‖ =
    ‖x‖ * (1 / |((n : ℕ) : ℝ) + k| ^ (q : ℝ))
  have hnorm : ‖((n : ℕ) : α) + k‖ = ((n : ℕ) : ℝ) + k := by
    rw [← Nat.cast_add, RCLike.norm_natCast, Nat.cast_add]
  simp only [norm_div, norm_pow, hnorm, Real.rpow_natCast, abs_of_nonneg hnonneg,
    mul_one_div₀]

end shifted

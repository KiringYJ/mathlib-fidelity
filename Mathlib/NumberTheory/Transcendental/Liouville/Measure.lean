/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Residual
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Analysis.PSeries

/-!
# Volume of the set of Liouville numbers

In this file we prove that the set of Liouville numbers with exponent (irrationality measure)
strictly greater than two is a set of Lebesgue measure zero, see
`volume_iUnion_setOfPred_liouvilleWith`.

Since this set is a residual set, we show that the filters `residual` and `ae volume` are disjoint.
These filters correspond to two common notions of genericity on `ℝ`: residual sets and sets of full
measure. The fact that the filters are disjoint means that two mutually exclusive properties can be
“generic” at the same time (in the sense of different “genericity” filters).

## Tags

Liouville number, Lebesgue measure, residual, generic property
-/

public section

open scoped Filter ENNReal Topology NNReal

open Filter Set Metric MeasureTheory Real

theorem setOfPred_liouvilleWith_subset_aux :
    { x : ℝ | ∃ p > 2, LiouvilleWith p x } ⊆
      ⋃ m : ℤ, (· + (m : ℝ)) ⁻¹' ⋃ n > (0 : ℕ),
        { x : ℝ | ∃ᶠ b : ℕ in atTop, ∃ (_ : 0 < b), ∃ a ∈ Finset.Icc (0 : ℤ) b,
          |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ (2 + 1 / (n : ℝ)) } := by
  rintro x ⟨p, hp, hxp⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hp) with ⟨n, hn⟩
  rw [lt_sub_iff_add_lt'] at hn
  suffices ∀ y : ℝ, LiouvilleWith p y → y ∈ Ico (0 : ℝ) 1 → ∃ᶠ b : ℕ in atTop,
      ∃ (_ : 0 < b), ∃ a ∈ Finset.Icc (0 : ℤ) b,
        |y - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ (2 + 1 / ((n + 1 : ℕ) : ℝ)) by
    simp only [mem_iUnion, mem_preimage]
    have hx : x + ↑(-⌊x⌋) ∈ Ico (0 : ℝ) 1 := by
      simp only [Int.floor_le, Int.lt_floor_add_one, add_neg_lt_iff_le_add', zero_add, and_self_iff,
        mem_Ico, Int.cast_neg, le_add_neg_iff_add_le]
    exact ⟨-⌊x⌋, n + 1, n.succ_pos, this _ (hxp.add_int _) hx⟩
  clear hxp x; intro x hxp hx01
  refine (hxp.frequently_lt_rpow_neg hn).mono ?_
  rintro b ⟨hb, a, -, hlt⟩
  have hb0 : (0 : ℝ) < b := Nat.cast_pos.2 hb
  rw [rpow_neg hb0.le _ (hxy := (rpow_pos_of_pos hb0 _).ne'.isUnit), ← one_div₀] at hlt
  simp only [← Nat.cast_succ] at hlt
  refine ⟨hb, a, ?_, hlt⟩
  have hb1 : (1 : ℝ) ≤ b := Nat.one_le_cast.2 hb
  replace hlt : |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) := by
    refine hlt.trans_le (one_div_le_one_div_of_le hb0 ?_)
    calc
      (b : ℝ) = (b : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ (b : ℝ) ^ (2 + 1 / ((n + 1 : ℕ) : ℝ)) :=
        rpow_le_rpow_of_exponent_le hb1 (one_le_two.trans ?_)
    simpa using n.cast_add_one_pos.le
  rw [sub_div', abs_div] at hlt
  simp only [abs_of_pos hb0] at hlt
  rw [div_lt_div_iff_of_pos_right hb0, abs_sub_lt_iff,
    sub_lt_iff_lt_add, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add'] at hlt
  rw [Finset.mem_Icc, ← Int.lt_add_one_iff, ← Int.lt_add_one_iff, ← neg_lt_iff_pos_add, add_comm, ←
    @Int.cast_lt ℝ, ← @Int.cast_lt ℝ]
  push_cast
  refine ⟨lt_of_le_of_lt ?_ hlt.1, hlt.2.trans_le ?_⟩
  · simp only [mul_nonneg hx01.left b.cast_nonneg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  · rw [add_le_add_iff_left]
    exact mul_le_of_le_one_left hb0.le hx01.2.le

@[deprecated (since := "2026-07-09")]
alias setOf_liouvilleWith_subset_aux := setOfPred_liouvilleWith_subset_aux

private theorem volume_frequently_rat_approx_eq_zero {r : ℝ} (hr : 2 < r) :
    volume {x : ℝ | ∃ᶠ b : ℕ in atTop, ∃ (_ : 0 < b), ∃ a ∈ Finset.Icc (0 : ℤ) b,
      |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ r} = 0 := by
  refine measure_setOfPred_frequently_eq_zero ?_
  let B (a : ℤ) (b : ℕ) (_ : 0 < b) : Set ℝ :=
    ball ((a : ℝ) / (b : ℝ)) (1 / (b : ℝ) ^ r)
  have hB (a : ℤ) (b : ℕ) (hb : 0 < b) :
      volume (B a b hb) = ↑((2 : ℝ≥0) / (b : ℝ≥0) ^ r) := by
    change volume (ball ((a : ℝ) / (b : ℝ)) (1 / (b : ℝ) ^ r)) = _
    rw [← ENNReal.ofReal_coe_nnreal, Real.volume_ball, mul_one_div₀]
    simp only [NNReal.coe_div, NNReal.coe_rpow, NNReal.coe_natCast, NNReal.coe_two]
  have hbound (b : ℕ) :
      volume {x : ℝ | ∃ (_ : 0 < b), ∃ a ∈ Finset.Icc (0 : ℤ) b,
        |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ r} ≤
      ↑(2 * ((b : ℝ≥0) ^ (1 - r) + (b : ℝ≥0) ^ (-r))) := by
    by_cases hb : 0 < b
    · have hset : {x : ℝ | ∃ (_ : 0 < b), ∃ a ∈ Finset.Icc (0 : ℤ) b,
          |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ r} = ⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b hb := by
        ext x
        simp only [mem_iUnion, mem_ofPred_eq, B, mem_ball, Real.dist_eq]
        exact ⟨fun ⟨_, a, ha, hxa⟩ => ⟨a, ha, hxa⟩, fun ⟨a, ha, hxa⟩ => ⟨hb, a, ha, hxa⟩⟩
      have hb' : (0 : ℝ≥0) < b := by exact_mod_cast hb
      rw [hset]
      calc
        volume (⋃ a ∈ Finset.Icc (0 : ℤ) b, B a b hb) ≤
            ∑ a ∈ Finset.Icc (0 : ℤ) b, volume (B a b hb) := measure_biUnion_finset_le _ _
        _ = ↑((b + 1) * (2 / (b : ℝ≥0) ^ r)) := by
          simp only [hB, Int.card_Icc, Finset.sum_const, nsmul_eq_mul, sub_zero,
            Int.toNat_natCast, ← Nat.cast_succ, ENNReal.coe_mul, ENNReal.coe_natCast]
        _ = _ := by
          rw [ENNReal.coe_inj, NNReal.rpow_sub hb'.ne' 1 r, NNReal.rpow_one,
            NNReal.rpow_neg _ _ (hxy := (NNReal.rpow_pos hb').ne'.isUnit)]
          simp only [div_eq_mul_inv₀]
          ring
    · simp [hb]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2 ?_)
    (ENNReal.tsum_le_tsum hbound)
  refine (Summable.add ?_ ?_).mul_left _ <;> simp only [NNReal.summable_rpow] <;> linarith

/-- The set of numbers satisfying the Liouville condition with some exponent `p > 2` has Lebesgue
measure zero. -/
@[simp]
theorem volume_iUnion_setOfPred_liouvilleWith :
    volume (⋃ (p : ℝ) (_hp : 2 < p), { x : ℝ | LiouvilleWith p x }) = 0 := by
  simp only [← ofPred_exists, exists_prop]
  refine measure_mono_null setOfPred_liouvilleWith_subset_aux ?_
  rw [measure_iUnion_null_iff]
  intro m
  rw [measure_preimage_add_right]
  rw [measure_iUnion_null_iff]
  intro n
  rw [measure_iUnion_null_iff]
  intro hn
  exact volume_frequently_rat_approx_eq_zero (lt_add_of_pos_right 2 (by positivity))

@[deprecated (since := "2026-07-09")]
alias volume_iUnion_setOf_liouvilleWith := volume_iUnion_setOfPred_liouvilleWith

theorem ae_not_liouvilleWith : ∀ᵐ x, ∀ p > (2 : ℝ), ¬LiouvilleWith p x := by
  simpa only [ae_iff, not_forall, Classical.not_not, ofPred_exists] using
    volume_iUnion_setOfPred_liouvilleWith

theorem ae_not_liouville : ∀ᵐ x, ¬Liouville x :=
  ae_not_liouvilleWith.mono fun _ h₁ h₂ => h₁ 3 (by norm_num) (h₂.liouvilleWith 3)

/-- The set of Liouville numbers has Lebesgue measure zero. -/
@[simp]
theorem volume_setOfPred_liouville : volume { x : ℝ | Liouville x } = 0 := by
  simpa only [ae_iff, Classical.not_not] using ae_not_liouville

@[deprecated (since := "2026-07-09")]
alias volume_setOf_liouville := volume_setOfPred_liouville

/-- The filters `residual ℝ` and `ae volume` are disjoint. This means that there exists a residual
set of Lebesgue measure zero (e.g., the set of Liouville numbers). -/
theorem Real.disjoint_residual_ae : Disjoint (residual ℝ) (ae volume) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right eventually_residual_liouville ae_not_liouville

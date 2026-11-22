/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Bounds
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# smoothingSeminorm

In this file, we prove [BGR, Proposition 1.3.2/1][bosch-guntzer-remmert]: if `μ` is a
nonarchimedean seminorm on a commutative ring `R`, then
`iInf (fun (n : PNat), (μ(x ^ (n : ℕ))) ^ (1 / (n : ℝ)))` is a power-multiplicative nonarchimedean
seminorm on `R`.

## Main Definitions
* `smoothingSeminormSeq` : the sequence `n ↦ μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))` for positive `n`.
* `smoothingFun` : the infimum of `smoothingSeminormSeq`.
* `smoothingSeminorm` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun`
  is a ring seminorm.

## Main Results

* `tendsto_smoothingFun_of_map_one_le_one` : if `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit
  of `smoothingSeminormSeq μ x` as `n` tends to infinity.
* `isNonarchimedean_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun` is nonarchimedean.
* `isPowMul_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun μ` is power-multiplicative.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

smoothingSeminorm, seminorm, nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter Nat Real

open scoped Topology NNReal

variable {R : Type*} [CommRing R] (μ : RingSeminorm R)

section smoothingSeminorm

/-- The `ℝ`-valued sequence of reciprocal roots of the seminorms of `x ^ n`, for `n > 0`. -/
abbrev smoothingSeminormSeq (x : R) (n : ℕ+) : ℝ := μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))

/-- `0` is a lower bound of `smoothingSeminormSeq`. -/
theorem zero_mem_lowerBounds_smoothingSeminormSeq_range (x : R) :
    0 ∈ lowerBounds (Set.range (smoothingSeminormSeq μ x)) := by
  rintro y ⟨n, rfl⟩
  exact rpow_nonneg (apply_nonneg μ _) _

/-- `smoothingSeminormSeq` is bounded below by zero. -/
theorem smoothingSeminormSeq_bddBelow (x : R) :
    BddBelow (Set.range (smoothingSeminormSeq μ x)) :=
  ⟨0, zero_mem_lowerBounds_smoothingSeminormSeq_range μ x⟩

/-- The infimum of the reciprocal roots of `μ (x ^ n)` over the positive natural numbers. -/
abbrev smoothingFun (x : R) : ℝ := ⨅ n : ℕ+, smoothingSeminormSeq μ x n

/-- The infimum lies below every term of the sequence. -/
theorem smoothingFun_le (x : R) (n : ℕ+) : smoothingFun μ x ≤ smoothingSeminormSeq μ x n :=
  ciInf_le (smoothingSeminormSeq_bddBelow μ x) n

private theorem pow_rpow_one_div_index {a : ℝ} (ha : 0 ≤ a) (n : ℕ+) :
    (a ^ (n : ℕ)) ^ (1 / (n : ℝ)) = a := by
  rw [← rpow_natCast, ← rpow_mul ha, mul_one_div_cancel, rpow_one]

/-- A rate above the smoothing infimum bounds all powers up to a constant factor. -/
private theorem exists_pow_bound_of_smoothingFun_lt (hμ1 : μ 1 ≤ 1) (x : R) {r : ℝ}
    (hr : smoothingFun μ x < r) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, μ (x ^ n) ≤ C * r ^ n := by
  have hr0 : 0 < r := (le_ciInf fun _ ↦ rpow_nonneg (apply_nonneg μ _) _).trans_lt hr
  obtain ⟨m, hm⟩ : ∃ m : ℕ+, smoothingSeminormSeq μ x m < r := exists_lt_of_ciInf_lt hr
  have hm' : μ (x ^ (m : ℕ)) ≤ r ^ (m : ℕ) := by
    have h := pow_le_pow_left₀ (rpow_nonneg (apply_nonneg μ (x ^ (m : ℕ))) _) hm.le (m : ℕ)
    simpa only [smoothingSeminormSeq, ← rpow_natCast, ← rpow_mul (apply_nonneg μ (x ^ (m : ℕ))),
      one_div_mul_cancel, rpow_one] using h
  let C := max 1 (∑ k ∈ Finset.range (m : ℕ), μ (x ^ k) / r ^ k)
  refine ⟨C, le_max_left _ _, fun n ↦ ?_⟩
  let q := Nat.euclideanDiv n m m.pos.ne'
  let k := n % (m : ℕ)
  have hdecomp : (m : ℕ) * q + k = n := Nat.euclideanDiv_mul_add_mod n m m.pos.ne'
  have hk : μ (x ^ k) ≤ C * r ^ k := by
    apply (div_le_iff₀ (pow_pos hr0 _)).1
    exact (Finset.single_le_sum (f := fun j : ℕ ↦ μ (x ^ j) / r ^ j)
      (fun j _ ↦ div_nonneg (apply_nonneg μ _) (pow_nonneg hr0.le j))
      (Finset.mem_range.mpr (Nat.mod_lt _ m.pos))).trans (le_max_right _ _)
  calc
    μ (x ^ n) = μ ((x ^ (m : ℕ)) ^ q * x ^ k) := by rw [← pow_mul, ← pow_add, hdecomp]
    _ ≤ μ ((x ^ (m : ℕ)) ^ q) * μ (x ^ k) := map_mul_le_mul μ _ _
    _ ≤ (r ^ (m : ℕ)) ^ q * (C * r ^ k) :=
      mul_le_mul ((map_pow_le_pow' hμ1 _ q).trans
        (pow_le_pow_left₀ (apply_nonneg μ _) hm' q)) hk (apply_nonneg μ _) (by positivity)
    _ = C * r ^ n := by rw [← pow_mul, mul_left_comm, ← pow_add, hdecomp]

private theorem smoothingSeminormSeq_le_of_pow_bound (x : R) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (h : ∀ n : ℕ, μ (x ^ n) ≤ C * r ^ n) (n : ℕ+) :
    smoothingSeminormSeq μ x n ≤ C ^ (1 / (n : ℝ)) * r := by
  calc
    smoothingSeminormSeq μ x n ≤ (C * r ^ (n : ℕ)) ^ (1 / (n : ℝ)) :=
      rpow_le_rpow (apply_nonneg μ _) (h n) (by positivity)
    _ = C ^ (1 / (n : ℝ)) * r := by
      rw [mul_rpow hC (pow_nonneg hr _), pow_rpow_one_div_index hr]

private theorem tendsto_const_rpow_one_div_index_mul {C : ℝ} (hC : 0 < C) (r : ℝ) :
    Tendsto (fun n : ℕ+ ↦ C ^ (1 / (n : ℝ)) * r) atTop (𝓝 r) := by
  have hcast : Tendsto (fun n : ℕ+ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ+ ↦ (1 / (n : ℝ))) atTop (𝓝 0) := by
    have hunit (n : ℕ+) : IsUnit (n : ℝ) := (show (n : ℝ) ≠ 0 by positivity).isUnit
    have hinv := hcast.fun_inv_tendsto_atTop (h0 := hunit)
    simpa only [one_div₀] using hinv
  have hroot : Tendsto (fun n : ℕ+ ↦ C ^ (1 / (n : ℝ))) atTop (𝓝 (C ^ (0 : ℝ))) :=
    Tendsto.rpow tendsto_const_nhds hdiv (Or.inl hC.ne')
  simpa only [rpow_zero, one_mul] using hroot.mul_const r

/-- If `μ x = 0`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`. -/
theorem tendsto_smoothingFun_of_eq_zero {x : R} (hx : μ x = 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  have hzero : smoothingSeminormSeq μ x = fun _ ↦ 0 := by
    funext n
    have hμn : μ (x ^ (n : ℕ)) = 0 := by
      refine le_antisymm ((map_pow_le_pow μ x n.ne_zero).trans ?_) (apply_nonneg μ _)
      rw [hx, zero_pow n.ne_zero]
    rw [smoothingSeminormSeq, hμn, zero_rpow (by positivity)]
  simp only [smoothingFun, hzero, ciInf_const, tendsto_const_nhds]

/-- If `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`. -/
theorem tendsto_smoothingFun_of_map_one_le_one (hμ1 : μ 1 ≤ 1) (x : R) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦
    ha.trans_le (smoothingFun_le μ x n), fun b hb ↦ ?_⟩
  obtain ⟨r, hr, hrb⟩ := exists_between hb
  have hr0 : 0 ≤ r := (le_ciInf fun _ ↦ rpow_nonneg (apply_nonneg μ _) _).trans hr.le
  obtain ⟨C, hC, hbound⟩ := exists_pow_bound_of_smoothingFun_lt μ hμ1 x hr
  have hlim := tendsto_const_rpow_one_div_index_mul (zero_lt_one.trans_le hC) r
  filter_upwards [(tendsto_order.1 hlim).2 b hrb] with n hn
  exact (smoothingSeminormSeq_le_of_pow_bound μ x (zero_le_one.trans hC) hr0 hbound n).trans_lt hn

/-- If `μ 1 ≤ 1` and `μ x ≠ 0`, then `smoothingFun μ x` is the limit of
`smoothingSeminormSeq μ x`. -/
theorem tendsto_smoothingFun_of_ne_zero (hμ1 : μ 1 ≤ 1) {x : R} (_hx : μ x ≠ 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) :=
  tendsto_smoothingFun_of_map_one_le_one μ hμ1 x

/-- If `μ 1 ≤ 1`, then `smoothingFun μ x` is nonnegative. -/
theorem smoothingFun_nonneg (hμ1 : μ 1 ≤ 1) (x : R) : 0 ≤ smoothingFun μ x :=
  ge_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) fun _ ↦
    rpow_nonneg (apply_nonneg μ _) _

/-- For all `x : R`, `smoothingFun μ x ≤ μ x`. -/
theorem smoothingFun_le_self (x : R) : smoothingFun μ x ≤ μ x := by
  simpa [smoothingSeminormSeq] using smoothingFun_le μ x 1

/-- If `μ 1 ≤ 1`, then `smoothingFun μ 1 ≤ 1`. -/
theorem smoothingFun_one_le (hμ1 : μ 1 ≤ 1) : smoothingFun μ 1 ≤ 1 :=
  (smoothingFun_le_self μ 1).trans hμ1

/-- Smoothing preserves the nonarchimedean inequality. -/
theorem isNonarchimedean_smoothingFun (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) :
    IsNonarchimedean (smoothingFun μ) := by
  intro x y
  by_contra! h
  obtain ⟨r, hr, hr'⟩ := exists_between h
  have hx := (le_max_left (smoothingFun μ x) (smoothingFun μ y)).trans_lt hr
  have hy := (le_max_right (smoothingFun μ x) (smoothingFun μ y)).trans_lt hr
  have hr0 := (smoothingFun_nonneg μ hμ1 x).trans hx.le
  obtain ⟨Cx, hCx, hxbound⟩ := exists_pow_bound_of_smoothingFun_lt μ hμ1 x hx
  obtain ⟨Cy, hCy, hybound⟩ := exists_pow_bound_of_smoothingFun_lt μ hμ1 y hy
  have hbound (n : ℕ) : μ ((x + y) ^ n) ≤ Cx * Cy * r ^ n := by
    obtain ⟨m, hm, hxy⟩ := hna.add_pow_le x y n (map_mul_le_mul μ)
    calc
      μ ((x + y) ^ n) ≤ μ (x ^ m) * μ (y ^ (n - m)) := hxy
      _ ≤ (Cx * r ^ m) * (Cy * r ^ (n - m)) :=
        mul_le_mul (hxbound m) (hybound (n - m)) (apply_nonneg μ _) (by positivity)
      _ = Cx * Cy * (r ^ m * r ^ (n - m)) := by ring
      _ = Cx * Cy * r ^ n := by rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hm)]
  have hC : 0 < Cx * Cy := mul_pos (zero_lt_one.trans_le hCx) (zero_lt_one.trans_le hCy)
  have hle := le_of_tendsto_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x + y))
    (tendsto_const_rpow_one_div_index_mul hC r)
    (smoothingSeminormSeq_le_of_pow_bound μ (x + y) hC.le hr0 hbound)
  exact hle.not_gt hr'

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun` is a ring seminorm. -/
def smoothingSeminorm (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) : RingSeminorm R where
  toFun     := smoothingFun μ
  map_zero' := by
    exact le_antisymm (by simpa only [map_zero] using smoothingFun_le_self μ 0)
      (smoothingFun_nonneg μ hμ1 0)
  add_le' _ _ := (isNonarchimedean_smoothingFun μ hμ1 hna).add_le (smoothingFun_nonneg μ hμ1)
  neg' n := by
    simp only [smoothingFun, smoothingSeminormSeq]
    congr
    ext n
    rw [neg_pow]
    rcases neg_one_pow_eq_or R (n : ℕ) with hpos | hneg
    · rw [hpos, one_mul]
    · rw [hneg, neg_one_mul, map_neg_eq_map μ]
  mul_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
      (Tendsto.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
        (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y))
    intro n
    simp only [smoothingSeminormSeq]
    rw [← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _), mul_pow]
    exact rpow_le_rpow (apply_nonneg μ _) (map_mul_le_mul μ _ _) (by positivity)

/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingSeminorm μ 1 ≤ 1`. -/
theorem smoothingSeminorm_map_one_le_one (hμ1 : μ 1 ≤ 1)
    (hna : IsNonarchimedean μ) : smoothingSeminorm μ hμ1 hna 1 ≤ 1 :=
  smoothingFun_one_le μ hμ1

/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun μ` is
  power-multiplicative. -/
theorem isPowMul_smoothingFun (hμ1 : μ 1 ≤ 1) : IsPowMul (smoothingFun μ) := by
  intro x m hm
  let m' : ℕ+ := ⟨m, hm⟩
  have hlim : Tendsto (fun n : ℕ+ ↦ smoothingSeminormSeq μ x (m' * n)) atTop
      (𝓝 (smoothingFun μ x)) :=
    (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hn ↦ Nat.mul_le_mul_left m hn)
        (fun n ↦ ⟨n, le_mul_of_one_le_left' hm⟩))
  refine tendsto_nhds_unique (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x ^ m)) ?_
  refine (Tendsto.pow hlim m).congr fun n ↦ ?_
  have hm0 : (m : ℝ) ≠ 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hm)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hexp : 1 / ((m' * n : ℕ+) : ℝ) * (m : ℝ) = 1 / (n : ℝ) := by
    field_simp
    change (n : ℝ) * (m : ℝ) = ((m * (n : ℕ) : ℕ) : ℝ)
    rw [Nat.cast_mul, mul_comm]
  change (μ (x ^ (m * (n : ℕ))) ^ (1 / ((m' * n : ℕ+) : ℝ))) ^ m =
    smoothingSeminormSeq μ (x ^ m) n
  rw [smoothingSeminormSeq, pow_mul, ← rpow_natCast, ← rpow_mul (apply_nonneg μ _), hexp]

/-- If `μ 1 ≤ 1` and `∀ (1 ≤ n), μ (x ^ n) = μ x ^ n`, then `smoothingFun μ x = μ x`. -/
theorem smoothingFun_of_powMul (hμ1 : μ 1 ≤ 1) {x : R}
    (hx : ∀ (n : ℕ) (_hn : 1 ≤ n), μ (x ^ n) = μ x ^ n) : smoothingFun μ x = μ x := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  exact Eventually.of_forall fun n ↦ by
    rw [smoothingSeminormSeq, hx n n.pos, pow_rpow_one_div_index (apply_nonneg μ _)]

/-- If `μ 1 ≤ 1` and `∀ y : R, μ (x * y) = μ x * μ y`, then `smoothingFun μ x = μ x`. -/
theorem smoothingFun_apply_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) : smoothingFun μ x = μ x := by
  by_cases hx0 : μ x = 0
  · exact le_antisymm (smoothingFun_le_self μ x) (hx0 ▸ smoothingFun_nonneg μ hμ1 x)
  · have h1 : μ 1 = 1 := by rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one]
    exact smoothingFun_of_powMul μ hμ1 fun n _ ↦ by
      rw [← mul_one (x ^ n), pow_mul_apply_eq_pow_mul μ hx, h1, mul_one]

/-- If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `∀ y : R, μ (x * y) = μ x * μ y`, then
  `smoothingSeminorm μ x = μ x`. -/
theorem smoothingSeminorm_apply_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) : smoothingSeminorm μ hμ1 hna x = μ x :=
  smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx

/-- If `μ 1 ≤ 1`, and `x` is multiplicative for `μ`, then it is multiplicative for
  `smoothingFun`. -/
theorem smoothingFun_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) {x : R} (hx : ∀ y : R, μ (x * y) = μ x * μ y)
    (y : R) : smoothingFun μ (x * y) = smoothingFun μ x * smoothingFun μ y := by
  have hlim : Tendsto (fun n => μ x * smoothingSeminormSeq μ y n) atTop
      (𝓝 (smoothingFun μ x * smoothingFun μ y)) := by
    rw [smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx]
    exact Tendsto.const_mul _ (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y)
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
    hlim
  exact Eventually.of_forall fun n ↦ by
    simp only [smoothingSeminormSeq]
    rw [mul_pow, pow_mul_apply_eq_pow_mul μ hx, mul_rpow (pow_nonneg (apply_nonneg μ _) _)
      (apply_nonneg μ _), pow_rpow_one_div_index (apply_nonneg μ _)]

/-- If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `x` is multiplicative for `μ`, then `x` is
  multiplicative for `smoothingSeminorm`. -/
theorem smoothingSeminorm_of_mul (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) (y : R) :
    smoothingSeminorm μ hμ1 hna (x * y) =
      smoothingSeminorm μ hμ1 hna x * smoothingSeminorm μ hμ1 hna y :=
  smoothingFun_of_map_mul_eq_mul μ hμ1 hx y

end smoothingSeminorm

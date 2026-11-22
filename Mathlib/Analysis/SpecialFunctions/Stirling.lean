/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
module

public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Tactic.AdaptationNote

/-!
# Stirling's formula

This file proves Stirling's formula for the factorial.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

Also some _global_ bounds on the factorial function and the Stirling sequence are proved.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
and prove that this sequence converges to a real, positive number $a$. For this the two main
ingredients are
- taking the logarithm of the sequence and
- using the series expansion of $\log(1 + x)$.

**Part 2**: We use the fact that the series defined in part 1 converges against a real number $a$
and prove that $a = \sqrt{\pi}$. Here the main ingredient is the convergence of Wallis' product
formula for `π`.
-/

@[expose] public section


open scoped Topology Real Nat Asymptotics

open Nat hiding log log_pow
open Finset Filter Real

namespace Stirling

/-!
### Part 1
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/


/-- Define `stirlingSeq n` as $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$ for positive `n`.
Stirling's formula states that this sequence has limit $\sqrt{\pi}$.
-/
noncomputable def stirlingSeq (n : ℕ+) : ℝ :=
  Checked.div ((n : ℕ)! : ℝ) (√(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ (n : ℕ))
    ((by have := n.pos; positivity : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ (n : ℕ)).ne'.isUnit)

local notation "stirlingSucc" => (stirlingSeq ∘ Nat.succPNat)

@[simp]
theorem stirlingSeq_one : stirlingSeq 1 = exp 1 / √2 := by
  unfold stirlingSeq
  simp only [PNat.val_ofNat, cast_one, mul_one, pow_one, factorial_one]
  field

theorem log_stirlingSeq_formula (n : ℕ+) :
    log (stirlingSeq n) =
      Real.log ((n : ℕ)!) - 1 / 2 * Real.log (2 * (n : ℝ)) - n * log ((n : ℝ) / exp 1) := by
  have hn := n.pos
  rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub] <;>
    positivity

/-- The difference of the logarithms of the Stirling terms at indices `m + 1` and `m + 2`
has the series expansion
`∑ 1 / (2 * (k + 1) + 1) * (1 / (2 * (m + 1) + 1))^(2 * (k + 1))`. -/
theorem log_stirlingSeq_sdiff_hasSum (m : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        ((1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (k + 1))
      (log (stirlingSucc m) - log (stirlingSucc (m + 1))) := by
  let f (k : ℕ) := (1 : ℝ) / (2 * (k : ℝ) + 1) * ((1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert! (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : ℝ) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul, pow_add]
    push_cast
    field
  · have h (x) (hx : x ≠ (0 : ℝ)) : 1 + x⁻¹ = (x + 1) / x := by field
    simp (disch := positivity) only [Function.comp_apply, log_stirlingSeq_formula,
      Nat.succPNat_coe, log_div, log_mul, log_exp,
      factorial_succ, cast_mul, cast_succ, range_one, sum_singleton, h]
    ring

@[deprecated (since := "2026-06-03")]
alias log_stirlingSeq_diff_hasSum := log_stirlingSeq_sdiff_hasSum

/-- The sequence `log ∘ stirlingSeq ∘ succ` is monotone decreasing -/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSucc) :=
  antitone_nat_of_succ_le fun n =>
    sub_nonneg.mp <| (log_stirlingSeq_sdiff_hasSum n).nonneg fun m => by positivity

local notation "stepRatioSq" n:arg => (((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ^ 2)

private lemma stepRatioSq_lt_one (n : ℕ) : stepRatioSq n < 1 := by
  have hn : (1 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact pow_lt_one₀ (by positivity) ((div_lt_one₀ (zero_lt_one.trans hn)).mpr hn) (by decide)

private lemma hasSum_stirling_step_geometric (n : ℕ) :
    HasSum (fun k : ℕ ↦ stepRatioSq n ^ (k + 1))
      (Checked.div (stepRatioSq n) (1 - stepRatioSq n)
        (sub_pos.mpr (stepRatioSq_lt_one n)).ne'.isUnit) := by
  let r := stepRatioSq n
  change HasSum (fun k : ℕ ↦ r ^ (k + 1))
    (Checked.div r (1 - r) (sub_pos.mpr (stepRatioSq_lt_one n)).ne'.isUnit)
  rw [div_eq_mul_inv₀]
  have hgeo := hasSum_geometric_of_lt_one (r := r) (sq_nonneg _) (stepRatioSq_lt_one n)
  exact (hgeo.mul_left r).congr_fun fun k ↦ _root_.pow_succ' r k

/-- We have a bound for successive elements in the sequence `log (stirlingSeq k)`. -/
@[deprecated "Use `log_stirlingSeq_sdiff_le` instead." (since := "2026-03-16")]
theorem log_stirlingSeq_sdiff_le_geo_sum (n : ℕ) :
    log (stirlingSucc n) - log (stirlingSucc (n + 1)) ≤
      Checked.div (stepRatioSq n) (1 - stepRatioSq n)
        (by exact (sub_pos.mpr (stepRatioSq_lt_one n)).ne'.isUnit) := by
  refine hasSum_le (fun k ↦ ?_) (log_stirlingSeq_sdiff_hasSum n) (hasSum_stirling_step_geometric n)
  refine mul_le_of_le_one_left (by positivity) ((div_le_one₀ (by positivity)).mpr ?_)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) k]

@[deprecated (since := "2026-06-03")]
alias log_stirlingSeq_diff_le_geo_sum := log_stirlingSeq_sdiff_le_geo_sum

/-- **Robbins' sharp stepwise bound** between the Stirling terms at indices `n + 1` and `n + 2`. -/
theorem log_stirlingSeq_sdiff_le (n : ℕ) :
    log (stirlingSucc n) - log (stirlingSucc (n + 1)) ≤
      1 / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  have hsum : HasSum (fun j : ℕ ↦ stepRatioSq n ^ (j + 1) / 3)
      ((1 : ℝ) / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
    have hn := (sub_pos.mpr (stepRatioSq_lt_one n)).ne'
    convert (hasSum_stirling_step_geometric n).div_const 3 using 1
    push_cast
    field_simp
    ring
  refine hasSum_le (fun j ↦ ?_) (log_stirlingSeq_sdiff_hasSum n) hsum
  have hj : (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  calc
    _ ≤ (1 / 3 : ℝ) * stepRatioSq n ^ (j + 1) := mul_le_mul_of_nonneg_right hj (by positivity)
    _ = _ := by rw [mul_comm, mul_one_div₀]

@[deprecated (since := "2026-06-03")] alias log_stirlingSeq_diff_le := log_stirlingSeq_sdiff_le

/-- The older stepwise bound `1 / (4 * (n + 1) ^ 2)` between indices `n + 1` and `n + 2`. -/
@[deprecated "Use `log_stirlingSeq_sdiff_le` instead." (since := "2026-03-16")]
theorem log_stirlingSeq_sub_log_stirlingSeq_succ (n : ℕ) :
    log (stirlingSucc n) - log (stirlingSucc (n + 1)) ≤ 1 / (4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  refine (log_stirlingSeq_sdiff_le n).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The difference between the logarithms of the Stirling terms at indices `1` and `n + 1`
is at most `12⁻¹`. -/
theorem log_stirlingSeq_bounded_aux (n : ℕ) :
    log (stirlingSeq 1) - log (stirlingSucc n) ≤ 12⁻¹ := by
  let f (k : ℕ) : ℝ := log (stirlingSucc k)
  let g (k : ℕ) : ℝ := 1 / (12 * ((k : ℝ) + 1))
  have hf k (hk : k ∈ range n) : f k - (f (k + 1)) ≤ g k - g (k + 1) := by
    refine (log_stirlingSeq_sdiff_le k).trans_eq ?_
    dsimp only [g]
    push_cast
    field_simp
    ring
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hf
  change log (stirlingSeq 1) - log (stirlingSucc n) ≤ g 0 - g n at hf
  calc
    _ ≤ g 0 - g n := hf
    _ ≤ _ := by
      have hzero : g 0 = (12 : ℝ)⁻¹ := by norm_num [g, one_div₀]
      rw [hzero]
      exact sub_le_self _ (by dsimp [g]; positivity)

/-- The sequence `log_stirlingSeq` is bounded below for `n ≥ 1`. -/
theorem log_stirlingSeq_bounded_by_constant (n : ℕ) :
    1 - 12⁻¹ - log 2 / 2 ≤ log (stirlingSucc n) := by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one, log_div (by positivity), log_exp, log_sqrt] at this <;> grind

/-- The Stirling sequence is positive. -/
theorem stirlingSeq_pos (n : ℕ+) : 0 < stirlingSeq n := by
  have := n.pos
  unfold stirlingSeq
  positivity

theorem stirlingSeq'_pos (n : ℕ) : 0 < stirlingSucc n := stirlingSeq_pos _

/-- The sequence `stirlingSeq` has a positive lower bound. -/
theorem stirlingSeq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirlingSucc n := by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n

/-- The Stirling sequence indexed by predecessors is monotone decreasing. -/
theorem stirlingSeq'_antitone : Antitone stirlingSucc := fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)

/-- The limit `a` of the sequence `stirlingSeq` satisfies `0 < a` -/
theorem stirlingSeq_has_pos_limit_a : ∃ a : ℝ, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a) := by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x ∈ lowerBounds (Set.range stirlingSucc) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  have he : stirlingSucc ∘ OrderIso.pnatIsoNat = stirlingSeq := by
    funext n
    change stirlingSeq n.natPred.succPNat = stirlingSeq n
    rw [PNat.succPNat_natPred]
  rw [← he]
  exact (tendsto_atTop_ciInf stirlingSeq'_antitone ⟨x, hx'⟩).comp OrderIso.pnatIsoNat.tendsto_atTop

/-!
### Part 2
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/


/-- The sequence `n / (2 * n + 1)` tends to `1/2` -/
theorem tendsto_self_div_two_mul_self_add_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * (n : ℝ) + 1)) atTop (𝓝 (1 / 2)) := by
  apply PNat.tendsto_comp_val_iff.mp
  let embed (n : ℕ+) : {n : ℕ // n ≠ 0} := ⟨n, n.pos.ne'⟩
  have hembed : Tendsto embed atTop (comap Subtype.val atTop) :=
    tendsto_comap_iff.mpr tendsto_PNat_val_atTop_atTop
  let f (n : ℕ+) : ℝ := 2 + 1 / (n : ℝ)
  have hf : Tendsto f atTop (𝓝 2) := by
    simpa only [f, Function.comp_def, embed, add_zero] using
      ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hembed).const_add (2 : ℝ)
  have hunit (n : ℕ+) : IsUnit (f n) :=
    (show 0 < f n by dsimp [f]; have := n.pos; positivity).ne'.isUnit
  rw [one_div₀]
  refine (hf.inv₀ (h0 := hunit) (ha := (by norm_num : (2 : ℝ) ≠ 0).isUnit)).congr fun n ↦ ?_
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.pos.ne'
  dsimp only [f]
  field

/-- For every positive `n`, we have the identity
`(stirlingSeq n)^4 / (stirlingSeq (2*n))^2 * (n / (2 * n + 1)) = W n`, where `W n` is the
`n`-th partial product of Wallis' formula for `π / 2`. -/
theorem stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq (n : ℕ+) :
    Checked.div (stirlingSeq n ^ 4) (stirlingSeq (2 * n) ^ 2)
      ((stirlingSeq_pos (2 * n)).ne'.isUnit.pow 2) *
        ((n : ℝ) / (2 * (n : ℝ) + 1)) = Wallis.W n := by
  have hn := n.pos
  have : 4 = 2 * 2 := by rfl
  unfold stirlingSeq
  rw [this, pow_mul, Wallis.W_eq_factorial_ratio]
  simp only [PNat.mul_coe, PNat.val_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  simp_rw [div_pow₀, mul_pow]
  have h₁ : √(2 * (n : ℝ)) ^ 2 = 2 * (n : ℝ) := sq_sqrt (by positivity)
  have h₂ : √(2 * (2 * (n : ℝ))) ^ 2 = 2 * (2 * (n : ℝ)) := sq_sqrt (by positivity)
  simp only [h₁, h₂]
  simp [field, ← exp_nsmul]
  ring_nf

/-- Suppose the sequence `stirlingSeq` (defined above) has the limit `a ≠ 0`.
Then the Wallis sequence `W n` has limit `a^2 / 2`.
-/
theorem second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : Tendsto stirlingSeq atTop (𝓝 a)) :
    Tendsto Wallis.W atTop (𝓝 (a ^ 2 / 2)) := by
  apply PNat.tendsto_comp_val_iff.mp
  have hdouble : Tendsto (fun n : ℕ+ ↦ 2 * n) atTop atTop := by
    refine tendsto_atTop.mpr fun n ↦ (eventually_ge_atTop n).mono fun m hm ↦ ?_
    change (n : ℕ) ≤ ((2 * m : ℕ+) : ℕ)
    rw [PNat.mul_coe, PNat.val_ofNat]
    have hnm : (n : ℕ) ≤ m := hm
    omega
  have h : a ^ 2 / 2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    field_simp
  rw [h]
  have hq := (ha.pow 4).div₀ ((ha.comp hdouble).pow 2)
    (h₀ := fun n ↦ (stirlingSeq_pos (2 * n)).ne'.isUnit.pow 2) (hb := hane.isUnit.pow 2)
  exact (hq.mul (tendsto_self_div_two_mul_self_add_one.comp tendsto_PNat_val_atTop_atTop)).congr
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq

/-- **Stirling's Formula** -/
theorem tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π)) := by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (hc := (two_ne_zero' ℝ).isUnit)).mp hπ, sqrt_sq hapos.le]

/-- **Stirling's Formula**, formulated in terms of `Asymptotics.IsEquivalent`. -/
lemma factorial_isEquivalent_stirling :
    (fun n ↦ n ! : ℕ → ℝ) ~[atTop] fun n ↦ Real.sqrt (2 * n * π) * ((n : ℝ) / exp 1) ^ n := by
  let f (n : ℕ) := Real.sqrt (2 * n * π) * ((n : ℝ) / exp 1) ^ n
  have hf (n : ℕ) (hn : n ≠ 0) : 0 < f n := by
    dsimp [f]
    positivity
  have hz : ∀ᶠ n : ℕ in atTop, f n = 0 → (n ! : ℝ) = 0 :=
    (eventually_ge_atTop 1).mono fun n hn h ↦
      False.elim ((hf n (Nat.one_le_iff_ne_zero.mp hn)).ne' h)
  refine Asymptotics.isEquivalent_of_tendsto_one hz ?_
  let positiveIndex (n : {n : ℕ // f n ≠ 0}) : ℕ+ :=
    ⟨n, Nat.pos_of_ne_zero (fun h ↦ n.2 (by simp [f, h]))⟩
  have hindex : Tendsto positiveIndex (comap Subtype.val atTop) atTop := by
    refine tendsto_atTop.mpr fun n ↦ ?_
    exact (tendsto_comap.eventually_ge_atTop (n : ℕ)).mono fun _ h ↦ h
  have hs : IsUnit (sqrt π) := (by positivity : 0 < sqrt π).ne'.isUnit
  have hq := (tendsto_stirlingSeq_sqrt_pi.comp hindex).div_const₀ (sqrt π) (hy := hs)
  rw [div_self (ha := hs)] at hq
  refine hq.congr fun n ↦ ?_
  apply (eq_div_iff).mpr
  have he : f n = sqrt π * (Real.sqrt (2 * ((n : ℕ) : ℝ)) *
      (((n : ℕ) : ℝ) / exp 1) ^ (n : ℕ)) := by
    dsimp [f]
    rw [sqrt_mul (by positivity)]
    ring
  change (stirlingSeq (positiveIndex n) / sqrt π) * f n = ((n : ℕ)! : ℝ)
  rw [he]
  rw [← mul_assoc, div_mul_cancel₀]
  have hn : 0 < (n : ℕ) := (positiveIndex n).pos
  let d := Real.sqrt (2 * ((n : ℕ) : ℝ)) * (((n : ℕ) : ℝ) / exp 1) ^ (n : ℕ)
  have hd : IsUnit d := (show 0 < d by dsimp [d]; positivity).ne'.isUnit
  change Checked.div ((n : ℕ)! : ℝ) d hd * d = _
  exact div_mul_cancel₀ _

/-! ### Global bounds -/

/--
The Stirling sequence is bounded below by `√π`, for all positive naturals. Note that this bound
holds for all `n > 0`, rather than for sufficiently large `n`: it is effective.
-/
theorem sqrt_pi_le_stirlingSeq (n : ℕ+) : √π ≤ stirlingSeq n := by
  simpa only [Function.comp_apply, PNat.succPNat_natPred] using
    (stirlingSeq'_antitone.le_of_tendsto (b := n.natPred)
      (tendsto_stirlingSeq_sqrt_pi.comp OrderIso.pnatIsoNat.symm.tendsto_atTop))

/--
Stirling's approximation gives a lower bound for `n!` for all `n`.
The left-hand side is formulated to mimic the usual informal description of the approximation.
See also `factorial_isEquivalent_stirling` which says these are asymptotically equivalent. That
statement gives an upper bound also, but requires sufficiently large `n`. In contrast, this one is
only a lower bound, but holds for all `n`.
See also `log_stirlingSeq_sdiff_le` for Robbins' sharp bound on successive differences in the
Stirling sequence.
-/
theorem le_factorial_stirling (n : ℕ) : √(2 * π * n) * ((n : ℝ) / exp 1) ^ n ≤ n ! := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * ((n : ℝ) / exp 1) ^ n = √π * (√(2 * n) * ((n : ℝ) / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this, ← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq ⟨n, Nat.pos_of_ne_zero hn⟩

/--
Stirling's approximation gives a lower bound for `log n!` for all positive `n`.
The left-hand side is formulated in decreasing order in `n`: the higher order terms are first.
This is a consequence of `le_factorial_stirling`, but is stated separately since the logarithmic
version is sometimes more practical, and having this version eases algebraic calculations for
applications.
See also `log_stirlingSeq_sdiff_le` for Robbins' sharp bound of `1/(12k(k+1))` on successive
differences in the Stirling sequence, which provides finer control over the convergence rate.
-/
theorem le_log_factorial_stirling {n : ℕ} (hn : n ≠ 0) :
    n * log n - n + log n / 2 + log (2 * π) / 2 ≤ log n ! := by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * ((n : ℝ) / rexp 1) ^ n) := by
      rw [log_mul (x := √_), log_sqrt, log_mul (x := 2 * π), log_pow, log_div, log_exp] <;>
      positivity
    _ ≤ _ := log_le_log (by positivity) (le_factorial_stirling n)

end Stirling

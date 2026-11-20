/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Binomial

import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Poisson limit of binomial probabilities

This file proves a Poisson limit theorem.

Fix `k : ℕ`. Assuming `n * p n → r` as `n → ∞`, we show
`PMF.binomial (p n) (h n) n (Fin.ofNat (n + 1) k) → poissonPMF r k`.

## Main results

* `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`:
  if `n * p n → r`, then `n.choose k * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.

* `ProbabilityTheory.binomial_tendsto_poissonPMFReal_atTop`:
  convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞` under the natural hypotheses
  (`p n ≤ 1` and `n * p n → r`).

## Tags

binomial distribution, Poisson distribution, asymptotics, limits, probability mass function
-/

public section

namespace ProbabilityTheory

open scoped NNReal

open Filter ENNReal

open scoped Topology

variable {p : ℕ → ℝ} {r : ℝ} (k : ℕ)

lemma tendsto_zero_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto p atTop (𝓝 0) := by
  refine tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    (f := fun n : ℕ ↦ (n : ℝ)) (g := p) ?_ tendsto_natCast_atTop_cobounded
  simpa only [smul_eq_mul] using hr.norm.isBoundedUnder_le

open Asymptotics in
lemma tendsto_choose_mul_pow_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k) atTop (𝓝 (r ^ k / k.factorial)) := by
  have : (fun n => n.choose k * (p n) ^ k) ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
    calc
    _ ~[atTop] (fun n => (n ^ k / k.factorial) * (p n) ^ k) :=
      (isEquivalent_choose k).mul IsEquivalent.refl
    _ ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
      EventuallyEq.isEquivalent (.of_eq (by ext; field))
  refine (IsEquivalent.tendsto_nhds_iff this).mpr ?_
  simpa [div_eq_mul_inv₀] using (hr.pow k).mul_const ((k.factorial : ℝ)⁻¹)

/--
**Poisson limit Theorem**: If `n * p n → r` as `n → ∞`. Then
`(n.choose k) * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.
-/
theorem tendsto_choose_mul_pow_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (Real.exp (-r) * (r ^ k) / k.factorial)) := by
  rw [mul_div_assoc₀, mul_comm]
  refine (tendsto_choose_mul_pow_atTop k hr).mul ?_
  have hp_lt_half : ∀ᶠ n in atTop, p n < 1 / 2 :=
    (tendsto_zero_of_tendsto_mul_atTop hr).eventually (Iio_mem_nhds (by norm_num))
  have hp_ne_one : ∀ᶠ n in atTop, p n ≠ 1 := hp_lt_half.mono fun n hn ↦ by linarith
  apply (tendsto_comap_val_iff hp_ne_one).mp
  have hunit (n : {n : ℕ // p n ≠ 1}) : IsUnit ((1 - p n) ^ k) :=
    (sub_ne_zero.mpr n.2.symm).isUnit.pow k
  have h_subtype : Tendsto (Subtype.val : {n : ℕ // p n ≠ 1} → ℕ)
      (comap Subtype.val atTop) atTop := tendsto_comap
  have hnum : Tendsto (fun n : {n : ℕ // p n ≠ 1} ↦ (1 - p n) ^ (n : ℕ))
      (comap Subtype.val atTop) (𝓝 (Real.exp (-r))) := by
    have h_neg : Tendsto (fun n : ℕ ↦ (n : ℝ) * (-p n)) atTop (𝓝 (-r)) := by
      simpa only [mul_neg] using hr.neg
    simpa only [Function.comp_def, sub_eq_add_neg, id_eq] using
      (Real.tendsto_one_add_pow_exp_of_tendsto (n := id) tendsto_id h_neg).comp h_subtype
  have hden : Tendsto (fun n : {n : ℕ // p n ≠ 1} ↦ (1 - p n) ^ k)
      (comap Subtype.val atTop) (𝓝 1) := by
    have h_one : Tendsto (fun n : ℕ ↦ 1 - p n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_zero_of_tendsto_mul_atTop hr)
    simpa only [Function.comp_def, sub_zero, one_pow] using (h_one.pow k).comp h_subtype
  have hquot := hnum.div₀ (h₀ := hunit) (hb := isUnit_one) hden
  simp only [div_one₀] at hquot
  refine hquot.congr' ?_
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop k)] with n hn
  apply div_eq_iff.2
  rw [← pow_add, Nat.sub_add_cancel hn]

/--
Another version of Poisson Limit Theorem: convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞`
under the natural hypotheses (`∀ n, p n ≤ 1` and `r ≥ 0`).
-/
@[deprecated tendsto_choose_mul_pow_of_tendsto_mul_atTop (since := "2026-03-08")]
lemma binomial_tendsto_poissonPMFReal_atTop {r : ℝ≥0} {p : ℕ → unitInterval}
    (hr : Tendsto (fun n => n * (p n : ℝ)) atTop (𝓝 r)) :
    Tendsto (fun n ↦ Bin(n, p n) {k}) atTop (𝓝 (poissonMeasure r {k})) := by
  have t1 : Tendsto (fun n => (ENNReal.ofReal (n.choose k * (p n) ^ k * (1 - p n) ^ (n - k) : ℝ)))
      atTop (𝓝 (poissonMeasure r {k})) := by
    simp_rw [poissonMeasure_singleton]
    exact tendsto_ofReal
      (tendsto_choose_mul_pow_of_tendsto_mul_atTop (p := fun n ↦ (p n : ℝ)) k hr)
  refine Tendsto.congr' ?_ t1
  simpa only [EventuallyEq, eventually_atTop, ge_iff_le] using
    ⟨k, fun b hb ↦ (binomial_singleton b k (p b)).symm⟩

end ProbabilityTheory

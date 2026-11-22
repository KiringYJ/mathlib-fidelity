/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecificLimits.RCLike

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Estimates for the complex logarithm

We show that `log (1+z)` differs from its Taylor polynomial up to degree `n` by at most
`‖z‖^(n+1)/((n+1)*(1-‖z‖))` when `‖z‖ < 1`; see `Complex.norm_log_sub_logTaylor_le`.

To this end, we derive the representation of `log (1+z)` as the integral of `1/(1+tz)`
over the unit interval (`Complex.log_eq_integral`) and introduce notation
`Complex.logTaylor n` for the Taylor polynomial up to degree `n-1`.

## TODO

Refactor using general Taylor series theory, once this exists in Mathlib.
-/

@[expose] public section

namespace Complex

/-!
### Integral representation of the complex log
-/

lemma one_add_mul_ne_zero {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ}
    (hz : 1 + z ∈ slitPlane) : 1 + t * z ≠ 0 := by
  simpa only [real_smul] using
    slitPlane_ne_zero (StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

lemma continuous_one_add_mul_inv {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      Checked.inv (1 + (t : ℝ) * z) (one_add_mul_ne_zero t.2 hz).isUnit) :=
  Continuous.fun_inv₀ (by fun_prop)

open intervalIntegral in
/-- Represent `log (1 + z)` as an integral over the unit interval -/
lemma log_eq_integral {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    log (1 + z) = z * ∫ t : Set.Icc (0 : ℝ) 1,
      Checked.inv (1 + (t : ℝ) * z) (one_add_mul_ne_zero t.2 hz).isUnit
        ∂(MeasureTheory.volume.comap Subtype.val) := by
  convert!
    (integral_unitInterval_deriv_eq_sub (z₀ := 1) (z₁ := z) (continuous_one_add_mul_inv hz)
        (fun t ↦ by simpa only [real_smul] using
          hasDerivAt_log <|
            StarConvex.add_smul_mem starConvex_one_slitPlane hz t.2.1 t.2.2)).symm using 1
  change log (1 + z) = log (1 + ((1 : ℝ) : ℂ) * z) - log (1 + ((0 : ℝ) : ℂ) * z)
  simp

/-- Represent `log (1 - z)⁻¹` as an integral over the unit interval -/
lemma log_inv_eq_integral {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    log (Checked.inv (1 - z) (slitPlane_ne_zero hz).isUnit) =
      z * ∫ t : Set.Icc (0 : ℝ) 1,
        Checked.inv (1 - (t : ℝ) * z)
          (by simpa only [mul_neg, ← sub_eq_add_neg] using
            (one_add_mul_ne_zero t.2 (z := -z) (by simpa only [← sub_eq_add_neg] using hz)).isUnit)
          ∂(MeasureTheory.volume.comap Subtype.val) := by
  rw [log_inv _ <| slitPlane_arg_ne_pi hz]
  simpa only [mul_neg, ← sub_eq_add_neg, neg_mul, neg_neg] using
    congrArg Neg.neg (log_eq_integral (z := -z) (by simpa only [← sub_eq_add_neg] using hz))

/-!
### The Taylor polynomials of the logarithm
-/

/-- The `n`th Taylor polynomial of `log` at `1`, as a function `ℂ → ℂ` -/
noncomputable
def logTaylor (n : ℕ) : ℂ → ℂ :=
  fun z ↦ ∑ j ∈ Finset.range (n - 1), (-1) ^ (j + 2) * z ^ (j + 1) / ((j : ℂ) + 1)

lemma logTaylor_zero : logTaylor 0 = fun _ ↦ 0 := by
  funext
  simp only [logTaylor, Nat.zero_sub, Finset.range_zero, Finset.sum_empty]

lemma logTaylor_one : logTaylor 1 = fun _ ↦ 0 := by
  funext
  simp only [logTaylor, Nat.sub_self, Finset.range_zero, Finset.sum_empty]

lemma logTaylor_succ {n : ℕ} (hn : n ≠ 0) :
    logTaylor (n + 1) = logTaylor n + (fun z : ℂ ↦ (-1) ^ (n + 1) * z ^ n / (n : ℂ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  funext z
  simpa only [logTaylor, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    Pi.add_apply] using
    Finset.sum_range_succ (fun j ↦ (-1 : ℂ) ^ (j + 2) * z ^ (j + 1) / ((j : ℂ) + 1)) k

lemma logTaylor_at_zero (n : ℕ) : logTaylor n 0 = 0 := by
  simp [logTaylor]

lemma hasDerivAt_logTaylor (n : ℕ) (z : ℂ) :
    HasDerivAt (logTaylor (n + 1)) (∑ j ∈ Finset.range n, (-1) ^ j * z ^ j) z := by
  induction n with
  | zero => simp [logTaylor_one, hasDerivAt_const]
  | succ n ih =>
    have hn : IsUnit ((n : ℂ) + 1) := (Nat.cast_add_one_ne_zero n).isUnit
    have hp : HasDerivAt (fun x : ℂ ↦ x ^ (n + 1) / ((n : ℂ) + 1)) (z ^ n) z := by
      convert (hasDerivAt_pow (n + 1) z).div_const ((n : ℂ) + 1) (hd := hn) using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      rw [mul_comm, mul_div_cancel_right₀]
    have hsign : (-1 : ℂ) ^ (n + 1 + 1) = (-1) ^ n := by
      rw [show n + 1 + 1 = n + 2 by omega, pow_add]
      norm_num
    rw [logTaylor_succ (Nat.succ_ne_zero n), Finset.sum_range_succ]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, hsign, mul_div_assoc₀] using
      ih.add (hp.const_mul ((-1 : ℂ) ^ n))

/-!
### Bounds for the difference between log and its Taylor polynomials
-/

lemma hasDerivAt_log_sub_logTaylor (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ ↦ log (1 + z) - logTaylor (n + 1) z)
      ((-z) ^ n * Checked.inv (1 + z) (slitPlane_ne_zero hz).isUnit) z := by
  convert! ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z ≠ 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_add', div_neg₀, add_comm z]
  simp [field]

/-- Give a bound on `‖(1 + t * z)⁻¹‖` for `0 ≤ t ≤ 1` and `‖z‖ < 1`. -/
lemma norm_one_add_mul_inv_le {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Checked.inv (1 + t * z) (one_add_mul_ne_zero ht (mem_slitPlane_of_norm_lt_one hz)).isUnit‖ ≤
      (1 - ‖z‖)⁻¹ := by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ ≤ 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
    _ ≤ ‖1 + t * z‖ := by
      rw [← norm_neg (t * z), ← sub_neg_eq_add]
      convert! norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm

lemma integrable_pow_mul_norm_one_add_mul_inv (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    MeasureTheory.Integrable (fun t : Set.Icc (0 : ℝ) 1 ↦ (t : ℝ) ^ n *
      ‖Checked.inv (1 + (t : ℝ) * z)
        (one_add_mul_ne_zero t.2 (mem_slitPlane_of_norm_lt_one hz)).isUnit‖)
      (MeasureTheory.volume.comap Subtype.val) := by
  have hpow : MeasureTheory.Integrable (fun t : Set.Icc (0 : ℝ) 1 ↦ (t : ℝ) ^ n)
      (MeasureTheory.volume.comap Subtype.val) :=
    (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
      ((continuous_pow n).continuousOn.integrableOn_compact isCompact_Icc)
  have hc := (continuous_subtype_val.pow n).mul
    (continuous_one_add_mul_inv (mem_slitPlane_of_norm_lt_one hz)).norm
  refine (hpow.mul_const ((1 - ‖z‖)⁻¹)).mono' hc.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg t.2.1 n) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (norm_one_add_mul_inv_le t.2 hz) (pow_nonneg t.2.1 n)

open intervalIntegral in
/-- The difference of `log (1+z)` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_sub_logTaylor_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - logTaylor (n + 1) z‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / ((n : ℝ) + 1) := by
  have hzS : 1 + z ∈ slitPlane := mem_slitPlane_of_norm_lt_one hz
  let f (z : ℂ) : ℂ := log (1 + z) - logTaylor (n + 1) z
  let f' (t : Set.Icc (0 : ℝ) 1) : ℂ := (-(t : ℝ) * z) ^ n *
    Checked.inv (1 + (t : ℝ) * z) (one_add_mul_ne_zero t.2 hzS).isUnit
  have hderiv (t : Set.Icc (0 : ℝ) 1) :
      HasDerivAt f (f' t) (0 + (t : ℝ) • z) := by
    simpa only [f, f', zero_add, real_smul, neg_mul] using
      hasDerivAt_log_sub_logTaylor n
        (StarConvex.add_smul_mem starConvex_one_slitPlane hzS t.2.1 t.2.2)
  have hcont : Continuous f' :=
    (by fun_prop : Continuous fun t : Set.Icc (0 : ℝ) 1 ↦ (-(t : ℝ) * z) ^ n).mul
      (continuous_one_add_mul_inv hzS)
  have H : f z = z * ∫ t, f' t ∂(MeasureTheory.volume.comap Subtype.val) := by
    have h := (integral_unitInterval_deriv_eq_sub hcont hderiv).symm
    change f (0 + (1 : ℝ) • z) - f (0 + (0 : ℝ) • z) =
      z • ∫ t, f' t ∂(MeasureTheory.volume.comap Subtype.val) at h
    simpa only [f, zero_add, add_zero, zero_smul, one_smul, log_one, logTaylor_at_zero,
      sub_self, sub_zero, smul_eq_mul] using h
  have hpow : MeasureTheory.Integrable (fun t : Set.Icc (0 : ℝ) 1 ↦ (t : ℝ) ^ n)
      (MeasureTheory.volume.comap Subtype.val) :=
    (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
      ((continuous_pow n).continuousOn.integrableOn_compact isCompact_Icc)
  have hint : (∫ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ^ n
      ∂(MeasureTheory.volume.comap Subtype.val)) = 1 / ((n : ℝ) + 1) := by
    rw [MeasureTheory.integral_subtype_comap measurableSet_Icc (fun t : ℝ ↦ t ^ n),
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_pow]
    simp
  calc
    ‖log (1 + z) - logTaylor (n + 1) z‖ =
        ‖z‖ * ‖∫ t, f' t ∂(MeasureTheory.volume.comap Subtype.val)‖ := by
      rw [← norm_mul, ← H]
    _ ≤ ‖z‖ * ∫ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ^ n * ‖z‖ ^ n * (1 - ‖z‖)⁻¹
        ∂(MeasureTheory.volume.comap Subtype.val) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      refine MeasureTheory.norm_integral_le_of_norm_le
        ((hpow.mul_const (‖z‖ ^ n)).mul_const ((1 - ‖z‖)⁻¹)) ?_
      filter_upwards with t
      simp only [f', norm_mul, norm_pow, norm_neg, Complex.norm_of_nonneg t.2.1, mul_pow]
      exact mul_le_mul_of_nonneg_left (norm_one_add_mul_inv_le t.2 hz)
        (mul_nonneg (pow_nonneg t.2.1 n) (pow_nonneg (norm_nonneg z) n))
    _ = ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / ((n : ℝ) + 1) := by
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, hint]
      rw [pow_succ, div_eq_mul_inv₀]
      ring

/-- The difference `log (1+z) - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_add_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert! norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_one, sub_eq_add_neg]
  · norm_num

set_option linter.style.whitespace false in -- manual alignment is not recognised
open scoped Topology in
lemma log_sub_logTaylor_isBigO (n : ℕ) :
    (fun z ↦ log (1 + z) - logTaylor (n + 1) z) =O[𝓝 0] fun z ↦ z ^ (n + 1) := by
  rw [Asymptotics.isBigO_iff]
  use 2 / ((n : ℝ) + 1)
  have hhalf_pos : (0 : ℝ) < (2 : ℝ)⁻¹ := inv_pos.mpr zero_lt_two
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 hhalf_pos] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have hhalf : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  have : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]
    linarith
  apply (norm_log_sub_logTaylor_le n hz1).trans
  rw [mul_div_assoc₀, mul_comm, norm_pow]
  gcongr

open scoped Topology in
lemma log_sub_self_isBigO :
    (fun z ↦ log (1 + z) - z) =O[𝓝 0] fun z ↦ z ^ 2 := by
  convert! log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_one]

lemma norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

/-- For `‖z‖ ≤ 1/2`, the complex logarithm is bounded by `(3/2) * ‖z‖`. -/
lemma norm_log_one_add_half_le_self {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  have hz1 := lt_of_le_of_lt hz one_half_lt_one
  have hden := sub_pos_of_lt hz1
  apply le_trans (norm_log_one_add_le hz1)
  have hz3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div₀, div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 * 2 / 2 := by
    gcongr
    rw [sq, div_eq_mul_one_div₀]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg z)
  simp only [div_mul_cancel₀] at hz4
  linarith

/-- The difference of `log (1-z)⁻¹` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_one_sub_inv_add_logTaylor_neg_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (Checked.inv (1 - z) (isUnit_one_sub_of_norm_lt_one hz)) + logTaylor (n + 1) (-z)‖ ≤
      ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / ((n : ℝ) + 1) := by
  have hneg : ‖-z‖ < 1 := by simpa only [norm_neg] using hz
  have hs : 1 - z ∈ slitPlane := by
    simpa only [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one hneg
  rw [log_inv _ (slitPlane_arg_ne_pi hs), ← sub_neg_eq_add, ← neg_sub', norm_neg,
    sub_eq_add_neg 1 z]
  convert! norm_log_sub_logTaylor_le n <| (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

/-- The difference `log (1-z)⁻¹ - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_sub_inv_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (Checked.inv (1 - z) (isUnit_one_sub_of_norm_lt_one hz)) - z‖ ≤
      ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert! norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_one, sub_eq_add_neg]
  · norm_num

open Filter Asymptotics in
/-- The Taylor series of the complex logarithm at `1` converges to the logarithm in the
open unit disk. -/
lemma hasSum_taylorSeries_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ (n + 2) * z ^ (n + 1) / ((n : ℂ) + 1)) (log (1 + z)) := by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      ← Nat.cast_add_one, norm_natCast]
    calc
      ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ ‖z‖ ^ (n + 1) :=
        div_le_self (pow_nonneg (norm_nonneg z) _)
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      _ ≤ ‖z‖ ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) n) hz.le
  · have hsum (n : ℕ) :
        (∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 2) * z ^ (j + 1) / ((j : ℂ) + 1)) =
          logTaylor (n + 1) z := by simp only [logTaylor, Nat.add_sub_cancel]
    simp_rw [hsum]
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ ↦ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹)
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ?_
    · rw [norm_sub_rev]
      exact (norm_log_sub_logTaylor_le n hz).trans
        (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg n)))
    · simpa only [pow_succ, mul_assoc, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).mul_const
          (‖z‖ * (1 - ‖z‖)⁻¹)

/-- The series `∑ z^n/n` converges to `-log (1-z)` on the open unit disk. -/
lemma hasSum_taylorSeries_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ (n + 1) / ((n : ℂ) + 1)) (-log (1 - z)) := by
  conv => enter [1, n]; rw [← neg_neg (z ^ (n + 1) / ((n : ℂ) + 1))]
  refine HasSum.neg ?_
  convert! hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  suffices h : z ^ n * z = z * (-1) ^ n * (-z) ^ n by
    simpa [field, pow_add] using h
  rw [mul_assoc, ← mul_pow, neg_one_mul, neg_neg, mul_comm z]

end Complex

section Limits

/-! Limits of functions of the form `(1 + t/x + o(1/x)) ^ x` as `x → ∞`. -/

open Filter Asymptotics
open scoped Topology

namespace Complex

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {α : Type*} {l : Filter α} {x : α → ℝ}
    {g : α → ℂ} {t : ℂ} (hx : Tendsto x l atTop)
    (hg : Tendsto (fun a ↦ x a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ x a * log (1 + g a)) l (𝓝 t) := by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBoundedUnder_le
    ((RCLike.tendsto_ofReal_atTop_cobounded ℂ).comp hx)
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ (show Tendsto (fun a ↦ (x a * g a) * g a) l (𝓝 (0 : ℂ))
    from by simpa using hg.mul hg0)
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[l] fun a ↦ x a * g a ^ 2 := by
      exact (isBigO_refl _ _).mul (log_sub_self_isBigO.comp_tendsto hg0)
    _ =ᶠ[l] fun a ↦ (x a * g a) * g a := Eventually.of_forall fun _ ↦ by ring

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_one_add_cpow_exp_of_tendsto {α : Type*} {l : Filter α} {x : α → ℝ}
    {g : α → ℂ} {t : ℂ} (hx : Tendsto x l atTop)
    (hg : Tendsto (fun a ↦ x a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ (1 + g a) ^ (x a : ℂ)) l (𝓝 (exp t)) := by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hx hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le ((RCLike.tendsto_ofReal_atTop_cobounded ℂ).comp hx)
  filter_upwards [hg0.eventually_ne (show 0 ≠ -1 by simp)] with x hg1
  dsimp
  rw [cpow_def_of_ne_zero, mul_comm]
  intro hg0
  rw [← add_eq_zero_iff_neg_eq.mp hg0] at hg1
  norm_num at hg1

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_cpow_exp (t : ℂ) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} ↦ (1 + t / ((x : ℝ) : ℂ)) ^ ((x : ℝ) : ℂ))
      (comap Subtype.val atTop) (𝓝 (exp t)) := by
  apply tendsto_one_add_cpow_exp_of_tendsto tendsto_comap
  apply tendsto_nhds_of_eventually_eq
  exact Eventually.of_forall fun x ↦ mul_div_cancel₀ t

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {α : Type*} {l : Filter α} {n : α → ℕ}
    {g : α → ℂ} {t : ℂ} (hn : Tendsto n l atTop)
    (hg : Tendsto (fun a ↦ n a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ n a * log (1 + g a)) l (𝓝 t) := by
  simpa only [Function.comp_apply, ofReal_natCast] using
    tendsto_mul_log_one_add_of_tendsto (tendsto_natCast_atTop_atTop.comp hn)
      (by simpa only [Function.comp_apply, ofReal_natCast] using hg)

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {α : Type*} {l : Filter α} {n : α → ℕ}
    {g : α → ℂ} {t : ℂ} (hn : Tendsto n l atTop)
    (hg : Tendsto (fun a ↦ n a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ (1 + g a) ^ n a) l (𝓝 (exp t)) := by
  simpa only [Function.comp_apply, ofReal_natCast, cpow_natCast] using
    tendsto_one_add_cpow_exp_of_tendsto (tendsto_natCast_atTop_atTop.comp hn)
      (by simpa only [Function.comp_apply, ofReal_natCast] using hg)

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℂ) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ (1 + t / ((n : ℕ) : ℂ)) ^ (n : ℕ))
      (comap Subtype.val atTop) (𝓝 (exp t)) := by
  apply tendsto_one_add_pow_exp_of_tendsto tendsto_comap
  exact tendsto_const_nhds.congr (fun n ↦ (mul_div_cancel₀ t).symm)

/-- `(1 + t/n + o(1/n)) ^ n → exp t` for `t ∈ ℂ`. -/
lemma tendsto_pow_exp_of_isLittleO_sub_add_div {f : {n : ℕ // n ≠ 0} → ℂ} (t : ℂ)
    (hf : (fun n ↦ f n - (1 + t / ((n : ℕ) : ℂ))) =o[comap Subtype.val atTop]
      fun n ↦ 1 / ((n : ℕ) : ℂ)) :
    Tendsto (fun n ↦ f n ^ (n : ℕ)) (comap Subtype.val atTop) (𝓝 (exp t)) := by
  rw [show (fun n ↦ f n ^ (n : ℕ)) = (fun n ↦ (1 + (f n - 1)) ^ (n : ℕ)) by ext; simp]
  refine tendsto_one_add_pow_exp_of_tendsto tendsto_comap (tendsto_sub_nhds_zero_iff.1 ?_)
  have hu (n : {n : ℕ // n ≠ 0}) : IsUnit ((n : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.mpr n.2).isUnit
  refine (hf.tendsto_inv_smul_nhds_zero (hg := fun n ↦ isUnit_one.div₀ (hu n))).congr ?_
  intro n
  have hinv : Checked.inv (1 / ((n : ℕ) : ℂ)) (isUnit_one.div₀ (hu n)) = (n : ℕ) := by
    apply inv_eq_of_mul_eq_one_right₀
    exact div_mul_cancel₀ 1
  rw [hinv, smul_eq_mul, mul_sub, mul_add, mul_one, mul_div_cancel₀]
  ring

end Complex

namespace Real

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {α : Type*} {l : Filter α} {x : α → ℝ}
    {g : α → ℝ} {t : ℝ} (hx : Tendsto x l atTop)
    (hg : Tendsto (fun a ↦ x a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ x a * log (1 + g a)) l (𝓝 t) := by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le ((tendsto_id'.mpr (by simp)).comp hx)
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hx hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_log (by linarith), Complex.ofReal_add, Complex.ofReal_one]

theorem tendsto_mul_log_one_add_div_atTop (t : ℝ) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} ↦ (x : ℝ) * log (1 + t / (x : ℝ)))
      (comap Subtype.val atTop) (𝓝 t) := by
  apply tendsto_mul_log_one_add_of_tendsto tendsto_comap
  exact tendsto_const_nhds.congr (fun x ↦ (mul_div_cancel₀ t).symm)

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_one_add_rpow_exp_of_tendsto {α : Type*} {l : Filter α} {x : α → ℝ}
    {g : α → ℝ} {t : ℝ} (hx : Tendsto x l atTop)
    (hg : Tendsto (fun a ↦ x a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ (1 + g a) ^ x a) l (𝓝 (exp t)) := by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le ((tendsto_id'.mpr (by simp)).comp hx)
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hx hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_cpow (by linarith), Complex.ofReal_add, Complex.ofReal_one]

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_rpow_exp (t : ℝ) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} ↦ (1 + t / (x : ℝ)) ^ (x : ℝ))
      (comap Subtype.val atTop) (𝓝 (exp t)) := by
  apply tendsto_one_add_rpow_exp_of_tendsto tendsto_comap
  apply tendsto_nhds_of_eventually_eq
  exact Eventually.of_forall fun x ↦ mul_div_cancel₀ t

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {α : Type*} {l : Filter α} {n : α → ℕ}
    {g : α → ℝ} {t : ℝ} (hn : Tendsto n l atTop)
    (hg : Tendsto (fun a ↦ n a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ n a * log (1 + g a)) l (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_natCast_atTop_atTop.comp hn) hg

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {α : Type*} {l : Filter α} {n : α → ℕ}
    {g : α → ℝ} {t : ℝ} (hn : Tendsto n l atTop)
    (hg : Tendsto (fun a ↦ n a * g a) l (𝓝 t)) :
    Tendsto (fun a ↦ (1 + g a) ^ n a) l (𝓝 (exp t)) := by
  simpa only [Function.comp_apply, rpow_natCast] using
    tendsto_one_add_rpow_exp_of_tendsto (tendsto_natCast_atTop_atTop.comp hn) hg

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℝ) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ (1 + t / ((n : ℕ) : ℝ)) ^ (n : ℕ))
      (comap Subtype.val atTop) (𝓝 (exp t)) := by
  apply tendsto_one_add_pow_exp_of_tendsto tendsto_comap
  exact tendsto_const_nhds.congr (fun n ↦ (mul_div_cancel₀ t).symm)

end Real

end Limits

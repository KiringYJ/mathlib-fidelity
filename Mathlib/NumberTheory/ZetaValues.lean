/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `hasSum_zeta_nat`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `hasSum_zeta_two` and `hasSum_zeta_four`: special cases given explicitly.
* `hasSum_one_div_nat_pow_mul_cos`: a formula for `∑' n : ℕ+, cos (2 π n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `hasSum_one_div_nat_pow_mul_sin`: a formula for `∑' n : ℕ+, sin (2 π n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/

@[expose] public section

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/


/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulliFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli k)).eval x

section Evaluation

@[simp]
theorem bernoulliFun_zero (x : ℝ) : bernoulliFun 0 x = 1 := by
  simp only [bernoulliFun, Polynomial.bernoulli_zero, Polynomial.map_one, Polynomial.eval_one]

@[simp]
theorem bernoulliFun_one (x : ℝ) : bernoulliFun 1 x = x - 1 / 2 := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

@[simp]
theorem bernoulliFun_two (x : ℝ) : bernoulliFun 2 x = x ^ 2 - x + 6⁻¹ := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

theorem bernoulliFun_eval_zero (k : ℕ) : bernoulliFun k 0 = bernoulli k := by
  rw [bernoulliFun, Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]

theorem bernoulliFun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    bernoulliFun k 1 = bernoulliFun k 0 := by
  rw [bernoulliFun_eval_zero, bernoulliFun, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one,
    bernoulli_eq_bernoulli'_of_ne_one hk, eq_ratCast]

theorem bernoulliFun_eval_one (k : ℕ) : bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0 := by
  rw [bernoulliFun, bernoulliFun_eval_zero, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one]
  split_ifs with h
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast; ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_ratCast]

end Evaluation

section Calculus

theorem hasDerivAt_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (bernoulliFun k) (k * bernoulliFun (k - 1) x) x := by
  convert! ((Polynomial.bernoulli k).map <| algebraMap ℚ ℝ).hasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_natCast]

variable (k : ℕ)

theorem contDiff_bernoulliFun : ContDiff ℝ ⊤ (bernoulliFun k) := by
  simp +unfoldPartialApp [bernoulliFun, Polynomial.eval_map_algebraMap, Polynomial.contDiff_aeval]

@[continuity, fun_prop]
theorem continuous_bernoulliFun : Continuous (bernoulliFun k) := Polynomial.continuous_aeval _

theorem intervalIntegrable_bernoulliFun (a b : ℝ) :
    IntervalIntegrable (bernoulliFun k) volume a b :=
  (continuous_bernoulliFun k).intervalIntegrable a b

theorem deriv_bernoulliFun :
    deriv (bernoulliFun k) = fun x ↦ k * bernoulliFun (k - 1) x := by
  ext x
  exact (hasDerivAt_bernoulliFun _ _).deriv

/-- The derivative of the Bernoulli polynomial of index `k` at `x`. -/
@[simp]
theorem deriv_bernoulliFun_apply (x : ℝ) :
    deriv (bernoulliFun k) x = k * bernoulliFun (k - 1) x :=
  congrFun (deriv_bernoulliFun k) x

theorem antideriv_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => bernoulliFun (k + 1) x / ((k : ℝ) + 1)) (bernoulliFun k x) x := by
  convert! (hasDerivAt_bernoulliFun (k + 1) x).div_const _ using 1
  simp

theorem integral_bernoulliFun : ∫ x : ℝ in 0..1, bernoulliFun k x = if k = 0 then 1 else 0 := by
  simp +contextual [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun k x)
      (intervalIntegrable_bernoulliFun k _ _), bernoulliFun_eval_one, ← sub_div]
  split_ifs with hk <;> simp_all

variable {k} in
theorem integral_bernoulliFun_eq_zero (hk : k ≠ 0) :
    ∫ x : ℝ in 0..1, bernoulliFun k x = 0 := by
  rw [integral_bernoulliFun, ite_eq_right hk]

/-- Fundamental theorem of calculus to express a Bernoulli polynomial via the previous one -/
theorem bernoulliFun_eq_integral (k : ℕ) (x y : ℝ) :
    bernoulliFun (k + 1) y =
      bernoulliFun (k + 1) x + ∫ t in x..y, (k + 1 : ℕ) * bernoulliFun k t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt, add_sub_cancel]
  · exact fun y _ ↦ hasDerivAt_bernoulliFun _ y
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

end Calculus

/-- Reflection principle: `B_s(1 - x) = (-1)^s B_s(x)` -/
theorem bernoulliFun_eval_one_sub {k : ℕ} {x : ℝ} :
    bernoulliFun k (1 - x) = (-1) ^ k * bernoulliFun k x := by
  simpa [bernoulliFun, Polynomial.aeval_comp]
    using congr_arg (·.aeval x) (Polynomial.bernoulli_comp_one_sub_X k)

/-- The multiplication theorem. Proof follows https://math.stackexchange.com/a/1721099/38218. -/
theorem bernoulliFun_mul (k : ℕ) {m : ℕ} (m0 : m ≠ 0) (x : ℝ) :
    bernoulliFun k (m * x) =
      (m : ℝ) ^ k / (m : ℝ) * ∑ i ∈ Finset.range m, bernoulliFun k (x + (i : ℝ) / (m : ℝ)) := by
  have m0' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m0
  let f (k x) := bernoulliFun k (m * x) -
    (m : ℝ) ^ k / (m : ℝ) * ∑ i ∈ Finset.range m, bernoulliFun k (x + (i : ℝ) / (m : ℝ))
  suffices h : ∀ x, f k x = 0 by
    rw [← sub_eq_zero]
    exact h x
  induction k with
  | zero =>
    intro x
    simp only [f, bernoulliFun_zero, pow_zero, one_div₀, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, sub_eq_zero]
    rw [inv_mul_cancel₀]
  | succ k h =>
    have d (x) : HasDerivAt (f (k + 1)) (m * (k + 1) * f k x) x := by
      simp only [f, mul_sub, Finset.mul_sum, pow_succ, mul_div_cancel_right₀,
        ← mul_assoc]
      apply HasDerivAt.sub
      · rw [mul_assoc, mul_comm (m : ℝ) _, ← Nat.cast_add_one]
        exact (hasDerivAt_bernoulliFun _ _).comp _ (hasDerivAt_const_mul ..)
      · refine HasDerivAt.fun_sum fun i _ ↦ ?_
        simp only [mul_assoc, ← Nat.cast_add_one]
        have hd := (hasDerivAt_bernoulliFun (k + 1) (x + (i : ℝ) / (m : ℝ))).comp
          (coord' := id) x ((hasDerivAt_id' x).add_const ((i : ℝ) / (m : ℝ)))
        apply (hd.const_mul ((m : ℝ) ^ k)).congr_deriv
        push_cast
        field
    simp only [h, mul_zero] at d
    have fc (x) : f (k + 1) x = f (k + 1) 0 :=
      is_const_of_deriv_eq_zero (fun _ ↦ (d _).differentiableAt) (fun _ ↦ (d _).deriv) x 0
    generalize f (k + 1) 0 = c at fc
    have i : ∫ x in (0 : ℝ)..m⁻¹, f (k + 1) x = 0 := by
      simp only [f]
      rw [intervalIntegral.integral_sub,
        intervalIntegral.integral_comp_mul_left _ (hc := m0'), mul_zero,
        mul_inv_cancel₀, integral_bernoulliFun_eq_zero (by lia), smul_zero, sub_eq_zero,
        intervalIntegral.integral_const_mul, eq_comm (a := 0), mul_eq_zero]
      · right
        rw [intervalIntegral.integral_finsetSum]
        · simp only [intervalIntegral.integral_comp_add_right, zero_add, ← one_div₀, ← add_div,
            add_comm (1 : ℝ), ← Nat.cast_add_one]
          rw [intervalIntegral.sum_integral_adjacent_intervals]
          · simp [div_self, integral_bernoulliFun_eq_zero]
          · intros; exact Continuous.intervalIntegrable (by fun_prop) _ _
        · intros; exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
    simp only [fc, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_eq_zero,
      inv_ne_zero, false_or] at i
    simpa only [i] using fc

/-!
### Values at 1/2
-/

theorem bernoulliFun_eval_half_eq_zero (k : ℕ) : bernoulliFun (2 * k + 1) 2⁻¹ = 0 := by
  have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := 2⁻¹)
  simp only [pow_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_neg, mul_one, neg_mul,
    one_mul, ← one_div₀, (sub_eq_of_eq_add (add_halves (1 : ℝ)).symm)] at h
  linarith

theorem bernoulliFun_eval_half (k : ℕ) : bernoulliFun k 2⁻¹ = (2 / 2 ^ k - 1) * bernoulli k := by
  by_cases k1 : k = 1
  · simp [k1]
  · have m := bernoulliFun_mul k two_ne_zero 2⁻¹
    simp_rw [Nat.cast_ofNat, mul_inv_cancel₀ (ha := (two_ne_zero' ℝ).isUnit), Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, ← one_div₀, add_halves,
      bernoulliFun_eval_one, ite_eq_right k1, bernoulliFun_eval_zero, zero_div, add_zero,
      zero_add] at m
    have hunit : IsUnit ((2 : ℝ) ^ k / 2) := (div_ne_zero (pow_ne_zero _ two_ne_zero)).isUnit
    rw [← inv_mul_eq_iff_eq_mul₀ (ha := hunit), ← sub_eq_iff_eq_add, ← sub_one_mul, inv_div₀] at m
    rw [m, one_div₀]

end BernoulliFunProps

section BernoulliFourierCoeffs

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/


/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulliFourierCoeff (k : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n

private theorem isUnit_fourierFrequency {n : ℤ} (hn : n ≠ 0) :
    IsUnit (2 * (π : ℂ) * I * n) :=
  (mul_ne_zero two_pi_I_ne_zero (Int.cast_ne_zero.mpr hn)).isUnit

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
theorem bernoulliFourierCoeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    bernoulliFourierCoeff k n =
      Checked.div 1 (-2 * π * I * n)
        (by convert (isUnit_fourierFrequency hn).neg using 1; ring) *
        (ite (k = 1) 1 0 - k * bernoulliFourierCoeff (k - 1) n) := by
  unfold bernoulliFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ => (hasDerivAt_bernoulliFun k x).ofReal_comp)
      ((continuous_ofReal.comp <|
            continuous_const.mul <| Polynomial.continuous _).intervalIntegrable
        _ _)]
  simp_rw [ofReal_one, ofReal_zero, sub_zero, one_mul]
  let : NeZero ((1 : ℝ) - 0) := ⟨by norm_num⟩
  rw [QuotientAddGroup.mk_zero, fourier_eval_zero, one_mul, ← ofReal_sub, bernoulliFun_eval_one,
    add_sub_cancel_left]
  congr 2
  · split_ifs <;> simp only [ofReal_one, ofReal_zero]
  · simp_rw [ofReal_mul, ofReal_natCast, fourierCoeffOn.const_mul]

/-- The Fourier coefficients of `B₀(x) = 1`. -/
theorem bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulliFourierCoeff 0 n = 0 := by
  simpa using bernoulliFourierCoeff_recurrence 0 hn

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
theorem bernoulliFourierCoeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulliFourierCoeff k 0 = 0 := by
  simp_rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one₀, one_smul, intervalIntegral.integral_ofReal, integral_bernoulliFun_eq_zero hk,
    ofReal_zero]

theorem bernoulliFourierCoeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) (hn : n ≠ 0) :
    bernoulliFourierCoeff k n =
      Checked.div (-(k ! : ℂ)) ((2 * π * I * n) ^ k)
        (by exact (isUnit_fourierFrequency hn).pow k) := by
  have hfreq := isUnit_fourierFrequency hn
  refine Nat.le_induction ?_ (fun k hk h'k => ?_) k (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulliFourierCoeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_self, one_mul, ite_true, Nat.factorial_one, pow_one,
      bernoulli_zero_fourier_coeff hn, sub_zero, mul_one]
    field
  · rw [bernoulliFourierCoeff_recurrence (k + 1) hn, ite_eq_right (by omega),
      Nat.add_sub_cancel k 1, h'k]
    simp only [Nat.factorial_succ, zero_sub, Nat.cast_mul, Nat.cast_succ, pow_succ]
    field

end BernoulliFourierCoeffs

section BernoulliPeriodized

/-! In this section we use the above evaluations of the Fourier coefficients of Bernoulli
polynomials, together with the theorem `has_pointwise_sum_fourier_series_of_summable` from Fourier
theory, to obtain an explicit formula for `∑' n : {n : ℤ // n ≠ 0}, 1 / n ^ k * fourier n x`. -/


/-- The Bernoulli polynomial, extended from `[0, 1)` to the unit circle. -/
def periodizedBernoulli (k : ℕ) : 𝕌 → ℝ :=
  AddCircle.liftIco 1 0 (bernoulliFun k)

theorem periodizedBernoulli.continuous {k : ℕ} (hk : k ≠ 1) : Continuous (periodizedBernoulli k) :=
  AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn

private theorem fourierCoeff_bernoulli_eq_coeff (k : ℕ) (n : ℤ) :
    fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) n = bernoulliFourierCoeff k n := by
  have : ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) = AddCircle.liftIco 1 0 ((↑) ∘ bernoulliFun k) := by
    ext1 x; rfl
  rw [this, fourierCoeff_liftIco_eq]
  simp only [bernoulliFourierCoeff, zero_add]
  rfl

theorem fourierCoeff_bernoulli_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) n =
      Checked.div (-(k ! : ℂ)) ((2 * π * I * n) ^ k)
        (by exact (isUnit_fourierFrequency hn).pow k) :=
  (fourierCoeff_bernoulli_eq_coeff k n).trans (bernoulliFourierCoeff_eq hk n hn)

theorem summable_bernoulli_fourier {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : {n : ℤ // n ≠ 0} ↦ Checked.div (-(k ! : ℂ))
      ((2 * π * I * (n : ℤ)) ^ k) (by exact (isUnit_fourierFrequency n.2).pow k)) := by
  have hp : IsUnit ((2 * ↑π * I : ℂ) ^ k) := two_pi_I_ne_zero.isUnit.pow k
  have :
      ∀ n : {n : ℤ // n ≠ 0}, Checked.div (-(k ! : ℂ)) ((2 * π * I * (n : ℤ)) ^ k)
        ((isUnit_fourierFrequency n.2).pow k) =
        -(k ! : ℂ) / (2 * π * I) ^ k * (1 / ((n : ℤ) : ℂ) ^ k) := by
    intro n
    rw [mul_one_div₀, div_div₀]
    simp only [mul_pow]
  simp_rw [this]
  refine Summable.mul_left _ <| .of_norm ?_
  have : (fun x : {n : ℤ // n ≠ 0} ↦ ‖1 / ((x : ℤ) : ℂ) ^ k‖) =
      fun x : {n : ℤ // n ≠ 0} ↦ |1 / ((x : ℤ) : ℝ) ^ k| := by
    ext1 x
    simp only [one_div₀, norm_inv, norm_pow, norm_intCast, pow_abs, abs_inv]
  simp_rw [this]
  rwa [summable_abs_iff, Real.summable_one_div_int_pow]

theorem hasSum_one_div_pow_mul_fourier_mul_bernoulliFun {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : {n : ℤ // n ≠ 0} ↦ 1 / ((n : ℤ) : ℂ) ^ k * fourier n (x : 𝕌))
      (-(2 * π * I) ^ k / (k ! : ℂ) * bernoulliFun k x) := by
  -- first show it suffices to prove result for `Ico 0 1`
  suffices ∀ {y : ℝ}, y ∈ Ico (0 : ℝ) 1 →
      HasSum (fun n : {n : ℤ // n ≠ 0} ↦ 1 / ((n : ℤ) : ℂ) ^ k * fourier n y)
        (-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * bernoulliFun k y) by
    rw [← Ico_insert_right (zero_le_one' ℝ), mem_insert_iff, or_comm] at hx
    rcases hx with (hx | rfl)
    · exact this hx
    · convert! this (left_mem_Ico.mpr zero_lt_one) using 1
      · rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
      · rw [bernoulliFun_endpoints_eq_of_ne_one (by lia : k ≠ 1)]
  intro y hy
  let B : C(𝕌, ℂ) :=
    ContinuousMap.mk ((↑) ∘ periodizedBernoulli k)
      (continuous_ofReal.comp (periodizedBernoulli.continuous (by lia)))
  have hk0 : k ≠ 0 := by omega
  have h0 : fourierCoeff B 0 = 0 :=
    (fourierCoeff_bernoulli_eq_coeff k 0).trans (bernoulliFourierCoeff_zero hk0)
  have hsupport : Function.support (fourierCoeff B) ⊆ {n : ℤ | n ≠ 0} := by
    intro n hn h
    subst n
    exact hn h0
  have hsumCoeffs : Summable (fourierCoeff B) := by
    have hf : Summable (fun n : {n : ℤ // n ≠ 0} ↦ fourierCoeff B n) :=
      (summable_bernoulli_fourier hk).congr fun n ↦
        (fourierCoeff_bernoulli_eq hk0 n n.2).symm
    exact ((hasSum_subtype_iff_of_support_subset hsupport).mp hf.hasSum).summable
  have hsum := has_pointwise_sum_fourier_series_of_summable hsumCoeffs y
  have htermSupport : Function.support (fun n : ℤ ↦ fourierCoeff B n • fourier n (y : 𝕌)) ⊆
      {n : ℤ | n ≠ 0} := by
    intro n hn h
    subst n
    exact hn (by change fourierCoeff B 0 • _ = 0; rw [h0, zero_smul])
  have hsum' := (hasSum_subtype_iff_of_support_subset htermSupport).mpr hsum
  have hB : B (y : 𝕌) = bernoulliFun k y := by
    rw [ContinuousMap.coe_mk, Function.comp_apply, ofReal_inj, periodizedBernoulli,
      AddCircle.liftIco_coe_apply (show y ∈ Ico 0 (0 + 1) by rwa [zero_add])]
  rw [hB] at hsum'
  apply (hsum'.mul_left (-(2 * ↑π * I) ^ k / (k ! : ℂ))).congr_fun
  intro n
  have hn : ((n : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr n.2
  have hfreq := isUnit_fourierFrequency n.2
  symm
  change -(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) *
      (fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) n • fourier n (y : 𝕌)) = _
  rw [smul_eq_mul, fourierCoeff_bernoulli_eq hk0 n n.2]
  simp only [mul_pow (2 * (π : ℂ) * I)]
  field

end BernoulliPeriodized

section Cleanup

-- This section is just reformulating the results in a nicer form.
theorem hasSum_one_div_nat_pow_mul_fourier {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℕ+ =>
        (1 : ℂ) / (n : ℂ) ^ k * (fourier n (x : 𝕌) + (-1 : ℂ) ^ k * fourier (-n) (x : 𝕌)))
      (-(2 * π * I) ^ k / (k ! : ℂ) * bernoulliFun k x) := by
  apply (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).int_pos_add_neg.congr_fun
  intro n
  have hpow : (-(n : ℂ)) ^ k = (-1 : ℂ) ^ k * (n : ℂ) ^ k := by
    rw [← neg_one_mul (n : ℂ), mul_pow]
  have hinv : (((-1 : ℂ) ^ k)⁻¹) = (-1 : ℂ) ^ k := by
    rw [← inv_pow₀ (ha := IsUnit.neg isUnit_one), inv_neg_one₀]
  simp only [Int.cast_neg, Int.cast_natCast, hpow, one_div₀, mul_inv₀, hinv]
  ring

theorem hasSum_one_div_nat_pow_mul_cos {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ+ ↦ 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval x) := by
  have :
    HasSum (fun n : ℕ+ ↦ 1 / (n : ℂ) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
      ((-1 : ℂ) ^ (k + 1) * (2 * (π : ℂ)) ^ (2 * k) / ((2 * k)! : ℂ) * bernoulliFun (2 * k) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 ≤ 2 * k) hx using 3
    · rw [pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul]
    · rw [pow_add, pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : ℝ) : ℂ) = 2 := by norm_cast
  convert! ((hasSum_iff _ _).mp (this.div_const 2 (hb := (two_ne_zero : (2 : ℂ) ≠ 0).isUnit))).1
    with n
  · convert! (ofReal_re _).symm
    rw [ofReal_mul, mul_div_assoc₀]; congr
    · simp only [ofReal_div, ofReal_one, ofReal_pow, ofReal_natCast]
    · simp only [ofReal_cos, ofReal_mul, fourier_coe_apply, cos, ofReal_one,
        div_one₀, ofReal_two, Int.cast_neg, Int.cast_natCast,
        ofReal_natCast]
      congr 3
      · ring
      · ring
  · convert! (ofReal_re _).symm
    simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_neg,
      ofReal_natCast, ofReal_mul, ofReal_two, ofReal_one]
    rw [bernoulliFun]
    ring

theorem hasSum_one_div_nat_pow_mul_sin {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ+ ↦ 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / ((2 * k + 1)! : ℝ) *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 1))).eval x) := by
  have :
    HasSum (fun n : ℕ+ ↦ 1 / (n : ℂ) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
      ((-1 : ℂ) ^ (k + 1) * I * (2 * π : ℂ) ^ (2 * k + 1) / ((2 * k + 1)! : ℂ) *
        bernoulliFun (2 * k + 1) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 ≤ 2 * k + 1) hx using 1
    · ext1 n
      rw [pow_add (-1 : ℂ), pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul, pow_one, ←
        neg_eq_neg_one_mul, ← sub_eq_add_neg]
    · congr
      rw [pow_add, pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_add, pow_one, pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : ℝ) : ℂ) = 2 := by norm_cast
  have h2I : IsUnit (2 * I) := (mul_ne_zero two_ne_zero I_ne_zero).isUnit
  convert! ((hasSum_iff _ _).mp (this.div_const (2 * I) (hb := h2I))).1
  · convert! (ofReal_re _).symm
    rw [ofReal_mul, mul_div_assoc₀]; congr
    · simp only [ofReal_div, ofReal_one, ofReal_pow, ofReal_natCast]
    · simp only [ofReal_sin, ofReal_mul, fourier_coe_apply, sin, ofReal_one, div_one₀,
        ofReal_two, Int.cast_neg, Int.cast_natCast, ofReal_natCast]
      field_simp
      ring_nf
      simp [I_sq, sub_eq_add_neg]
  · convert! (ofReal_re _).symm
    simp only [bernoulliFun, ofReal_mul, ofReal_div, ofReal_pow, ofReal_neg,
      ofReal_natCast, ofReal_two, ofReal_one]
    field

theorem hasSum_zeta_nat {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ+ ↦ 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / ((2 * k)! : ℝ)) := by
  convert! hasSum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one) using 1
  · ext1 n; rw [mul_zero, Real.cos_zero, mul_one]
  rw [Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]
  have : (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) / 2 := by
    rw [eq_div_iff]
    conv_lhs =>
      congr
      · skip
      · rw [← pow_one (2 : ℝ)]
    rw [← pow_add, Nat.sub_add_cancel]
    lia
  rw [this, mul_pow]
  ring

end Cleanup

section Examples

theorem hasSum_zeta_two : HasSum (fun n : ℕ+ ↦ (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := by
  convert! hasSum_zeta_nat one_ne_zero using 1
  simp only [mul_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]
  simp [Nat.factorial]; ring

theorem hasSum_zeta_four : HasSum (fun n : ℕ+ ↦ (1 : ℝ) / (n : ℝ) ^ 4) (π ^ 4 / 90) := by
  convert! hasSum_zeta_nat two_ne_zero using 1
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four]
  · simp [Nat.factorial]; ring
  · decide

/-- Explicit formula for `L(χ, 3)`, where `χ` is the unique nontrivial Dirichlet character modulo 4.
-/
theorem hasSum_L_function_mod_four_eval_three :
    HasSum (fun n : ℕ+ ↦ (1 : ℝ) / (n : ℝ) ^ 3 * Real.sin (π * n / 2)) (π ^ 3 / 32) := by
  apply (congr_arg₂ HasSum ?_ ?_).to_iff.mp <|
    hasSum_one_div_nat_pow_mul_sin one_ne_zero (?_ : 1 / 4 ∈ Icc (0 : ℝ) 1)
  · ext1 n
    ring_nf
  · have : (1 / 4 : ℝ) = (algebraMap ℚ ℝ) (1 / 4 : ℚ) := by simp
    simp only [this, mul_pow, Polynomial.eval_map, Polynomial.eval₂_at_apply, Nat.reduceMul,
      Nat.reduceAdd, Polynomial.bernoulli_three_eval_one_quarter]
    simp [Nat.factorial]; ring
  · rw [mem_Icc]; constructor
    · linarith
    · linarith

end Examples

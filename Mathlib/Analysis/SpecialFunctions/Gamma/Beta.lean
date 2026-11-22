/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Beta function, and further properties of the Gamma function

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `Complex.betaIntegral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `Complex.Gamma_mul_Gamma_eq_betaIntegral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * betaIntegral u v`.

## Results on the Gamma function

* `Complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `Complex.GammaSeq_tendsto_Gamma`: for `s` away from the nonpositive integers, the limit of
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `Complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `Complex.reciprocalGamma`: the entire reciprocal Gamma function, with zeros at the
  nonpositive integers.
* `Complex.differentiable_reciprocalGamma`: the reciprocal Gamma function is differentiable
  everywhere.
* `Complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π`.
* `Real.Gamma_ne_zero`, `Real.GammaSeq_tendsto_Gamma`,
  `Real.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/

@[expose] public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)

/-- Auxiliary lemma for `betaIntegral_convergent`, showing convergence at the left endpoint. -/
theorem betaIntegral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) := by
  apply IntervalIntegrable.mul_continuousOn
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / 2)] at hx
    apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
    norm_cast
    exact ofReal_mem_slitPlane.2 <| by linarith only [hx.2]

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
theorem betaIntegral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 1 := by
  refine (betaIntegral_convergent_left hu v).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert! ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast; ring
  · norm_num
  · simp

theorem betaIntegral_symm (u v : ℂ) : betaIntegral v u = betaIntegral u v := by
  simpa [betaIntegral, ← intervalIntegral.integral_symm, add_comm, mul_comm, sub_eq_add_neg]
    using intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
      (hc := neg_ne_zero.mpr one_ne_zero)
      (fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)) 1

theorem betaIntegral_eval_one_right {u : ℂ} (hu : 0 < re u) :
    betaIntegral u 1 = Checked.div (1 : ℂ) u (ne_zero_of_re_pos hu).isUnit := by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  have hu' : -1 < re (u - 1) := by rw [sub_re, one_re]; linarith
  have hden : u - 1 + 1 = u := sub_add_cancel _ _
  have hne : u - 1 + 1 ≠ 0 := by simpa only [hden] using ne_zero_of_re_pos hu
  rw [integral_cpow (Or.inl hu'), ofReal_zero, ofReal_one, one_cpow, zero_cpow hne, sub_zero]
  apply (eq_div_iff).mpr
  calc
    _ = 1 / (u - 1 + 1) * (u - 1 + 1) :=
      congrArg (fun z : ℂ ↦ Checked.div (1 : ℂ) (u - 1 + 1) hne.isUnit * z) hden.symm
    _ = 1 := div_mul_cancel₀ 1

theorem betaIntegral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x in 0..a, (x : ℂ) ^ (s - 1) * ((a : ℂ) - x) ^ (t - 1) =
    (a : ℂ) ^ (s + t - 1) * betaIntegral s t := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [betaIntegral]
  have A : (a : ℂ) ^ (s + t - 1) = a * ((a : ℂ) ^ (s - 1) * (a : ℂ) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)), cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one,
      mul_assoc]
  rw [A, mul_assoc, ← intervalIntegral.integral_const_mul, ← real_smul,
    ← zero_div a (ha := ha.ne'.isUnit), ← div_self (ha := ha.ne'.isUnit),
    ← intervalIntegral.integral_comp_div _ (hc := ha.ne'.isUnit), zero_div]
  simp_rw [intervalIntegral.integral_of_le ha.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← mul_cpow_ofReal_nonneg ha.le (div_pos hx.1 ha).le, ofReal_div, mul_div_cancel₀]
  · rw [(by norm_cast : (1 : ℂ) - ↑(x / a) = ↑(1 - x / a)), ←
      mul_cpow_ofReal_nonneg ha.le (sub_nonneg.mpr <| (div_le_one ha).mpr hx.2)]
    push_cast
    rw [mul_sub, mul_one, mul_div_cancel₀]

/-- Relation between Beta integral and Gamma function. -/
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t := by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul ℝ ℂ)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int
  have hst : 0 < re (s + t) := by rw [add_re]; exact add_pos hs ht
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, GammaIntegral,
    GammaIntegral, GammaIntegral, ← conv_int, ← MeasureTheory.integral_mul_const (betaIntegral _ _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [mul_assoc, ← betaIntegral_scaled s t hx, ← intervalIntegral.integral_const_mul]
  congr 1 with y : 1
  push_cast
  suffices Complex.exp (-x) = Complex.exp (-y) * Complex.exp (-(x - y)) by rw [this]; ring
  rw [← Complex.exp_add]; congr 1; abel

/-- Recurrence formula for the Beta function. -/
theorem betaIntegral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v := by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ u * (1 - (x : ℂ)) ^ v
  have hu' : 0 < re (u + 1) := by rw [add_re, one_re]; positivity
  have hv' : 0 < re (v + 1) := by rw [add_re, one_re]; positivity
  have hc : ContinuousOn F (Icc 0 1) := by
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).mul
        (continuousOn_of_forall_continuousAt fun x hx => ?_)
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hu).comp continuous_ofReal.continuousAt
      rw [ofReal_re]; exact hx.1
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hv).comp (by fun_prop)
      rw [sub_re, one_re, ofReal_re, sub_nonneg]
      exact hx.2
  have hder : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt F (u * ((x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ v) -
        v * ((x : ℂ) ^ u * (1 - (x : ℂ)) ^ (v - 1))) x := by
    intro x hx
    have U : HasDerivAt (fun y : ℂ => y ^ u) (u * (x : ℂ) ^ (u - 1)) ↑x := by
      have := @HasDerivAt.cpow_const _ _ _ u (hasDerivAt_id (x : ℂ)) (Or.inl ?_)
      · simp only [id_eq, mul_one] at this
        exact this
      · rw [id_eq, ofReal_re]; exact hx.1
    have V : HasDerivAt (fun y : ℂ => (1 - y) ^ v) (-v * (1 - (x : ℂ)) ^ (v - 1)) ↑x := by
      have A := @HasDerivAt.cpow_const _ _ _ v (hasDerivAt_id (1 - (x : ℂ))) (Or.inl ?_)
      swap; · rw [id, sub_re, one_re, ofReal_re, sub_pos]; exact hx.2
      simp_rw [id] at A
      have B : HasDerivAt (fun y : ℂ => 1 - y) (-1) ↑x := by
        apply HasDerivAt.const_sub; apply hasDerivAt_id
      convert! HasDerivAt.comp (↑x) A B using 1
      ring
    convert! (U.mul V).comp_ofReal using 1
    ring
  have h_int := ((betaIntegral_convergent hu hv').const_mul u).sub
    ((betaIntegral_convergent hu' hv).const_mul v)
  rw [add_sub_cancel_right, add_sub_cancel_right] at h_int
  have int_ev := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hder h_int
  have hF0 : F 0 = 0 := by
    simp only [F, mul_eq_zero, ofReal_zero, cpow_eq_zero_iff, Ne,
      true_and, sub_zero, one_cpow, one_ne_zero, or_false]
    contrapose! hu; rw [hu, zero_re]
  have hF1 : F 1 = 0 := by
    simp only [F, mul_eq_zero, ofReal_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      Ne, true_and, false_or]
    contrapose! hv; rw [hv, zero_re]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at int_ev
  · rw [betaIntegral, betaIntegral, ← sub_eq_zero]
    convert! int_ev <;> ring
  · apply IntervalIntegrable.const_mul
    convert! betaIntegral_convergent hu hv'; ring
  · apply IntervalIntegrable.const_mul
    convert! betaIntegral_convergent hu' hv; ring

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = Checked.div (n ! : ℂ)
      (∏ j ∈ Finset.range (n + 1), (u + j))
      (Finset.prod_ne_zero_iff.mpr (fun j _ ↦
        ne_zero_of_re_pos (by simpa only [add_re, natCast_re] using
          add_pos_of_pos_of_nonneg hu (Nat.cast_nonneg j)))).isUnit := by
  induction n generalizing u with
  | zero =>
    apply (eq_div_iff).mpr
    simp only [Nat.cast_zero, zero_add, betaIntegral_eval_one_right hu, Finset.prod_range_one,
      add_zero, Nat.factorial_zero, Nat.cast_one, div_mul_cancel₀]
  | succ n ih =>
    have hu' : 0 < (u + 1).re := by rw [add_re, one_re]; positivity
    have hv : 0 < re (n.succ : ℂ) := by rw [natCast_re]; positivity
    have hstep := betaIntegral_recurrence hu hv
    rw [Nat.cast_succ] at hstep
    rw [ih (u := u + 1) hu'] at hstep
    apply (eq_div_iff).mpr
    rw [Finset.prod_range_succ' (fun j : ℕ ↦ u + (j : ℂ)) n.succ,
      Nat.cast_zero, add_zero, mul_comm _ u, ← mul_assoc, mul_comm (betaIntegral _ _) u,
      Nat.cast_succ, hstep]
    have hprod : (∏ j ∈ Finset.range (n + 1), (u + ((j + 1 : ℕ) : ℂ))) =
        ∏ j ∈ Finset.range (n + 1), (u + 1 + (j : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      push_cast
      ring
    rw [hprod, mul_assoc, div_mul_cancel₀, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
The finite quotient is defined exactly when `s` avoids `0, -1, ..., -n`.
For arguments avoiding all nonpositive integers it tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℂ) (n : ℕ) (hs : ∀ j ≤ n, s ≠ -j) : ℂ :=
  Checked.div ((n : ℂ) ^ s * n !) (∏ j ∈ Finset.range (n + 1), (s + j))
    (Finset.prod_ne_zero_iff.mpr fun j hj h ↦
      hs j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (by linear_combination h)).isUnit

theorem GammaSeq_eq_betaIntegral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
    GammaSeq s n (fun j _ ↦ Gamma_regular_of_re_pos hs j) =
      (n : ℂ) ^ s * betaIntegral s (n + 1) := by
  rw [GammaSeq, betaIntegral_eval_nat_add_one_right hs n, ← mul_div_assoc₀]

theorem GammaSeq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0)
    (hs : ∀ j ≤ n + 1, s ≠ -j) :
    Checked.div (GammaSeq (s + 1) n (by
        intro j hj h
        apply hs (j + 1) (by omega)
        push_cast
        linear_combination h)) s (isUnit_iff_ne_zero.mpr (by simpa using hs 0 (by omega))) =
      Checked.div (n : ℂ) (n + 1 + s) (isUnit_iff_ne_zero.mpr (by
        have h := hs (n + 1) le_rfl
        contrapose! h
        push_cast
        linear_combination h)) * GammaSeq s n (fun j hj ↦ hs j (by omega)) := by
  unfold GammaSeq
  field_simp
  have hprod : (∏ j ∈ Finset.range n, (s + 1 + (j : ℂ))) =
      ∏ j ∈ Finset.range n, (s + ((j + 1 : ℕ) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [Finset.prod_range_succ (fun j : ℕ ↦ s + 1 + (j : ℂ)) n,
    Finset.prod_range_succ' (fun j : ℕ ↦ s + (j : ℂ)) n, hprod, Nat.cast_zero, add_zero,
    cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_one]
  ring

theorem GammaSeq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n (fun j _ ↦ Gamma_regular_of_re_pos hs j) =
      ∫ x : ℝ in 0..n, ↑((1 - x / (n : ℝ)) ^ n) * (x : ℂ) ^ (s - 1) := by
  have : ∀ x : ℝ, x = x / (n : ℝ) * n := by intro x; rw [div_mul_cancel₀]
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (hc := (Nat.cast_ne_zero.mpr hn).isUnit)
    (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ)
  rw [betaIntegral, this, real_smul, zero_div, div_self, add_sub_cancel_right,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  push_cast
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1) * n := by
    conv_lhs => rw [(by ring : s = s - 1 + 1), cpow_add _ _ hn']
    simp
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * (n : ℂ) ^ (s - 1) := by
    rw [← ofReal_natCast,
      mul_cpow_ofReal_nonneg hx.1.le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).le]
  rw [A, B, cpow_natCast]; ring

/-- The main technical lemma for `GammaSeq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
theorem approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} =>
      ∫ x : ℝ in 0..(n : ℕ), ((1 - x / ((n : ℕ) : ℝ)) ^ (n : ℕ) : ℝ) * (x : ℂ) ^ (s - 1))
      (comap Subtype.val atTop)
      (𝓝 <| Gamma s) := by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : {n : ℕ // n ≠ 0} → ℝ → ℂ := fun n =>
    indicator (Ioc 0 ((n : ℕ) : ℝ)) fun x : ℝ =>
      ((1 - x / ((n : ℕ) : ℝ)) ^ (n : ℕ) : ℝ) * (x : ℂ) ^ (s - 1)
  -- integrability of f
  have f_ible : ∀ n : {n : ℕ // n ≠ 0}, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)), IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ← IntegrableOn, ←
      intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ (n : ℕ))]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · fun_prop
  -- pointwise limit of f
  have f_tends : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      Tendsto (fun n => f n x) (comap Subtype.val atTop)
        (𝓝 <| ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1)) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ n : {n : ℕ // n ≠ 0} in comap Subtype.val atTop,
        ↑((1 - x / ((n : ℕ) : ℝ)) ^ (n : ℕ)) * (x : ℂ) ^ (s - 1) = f n x
      filter_upwards [preimage_mem_comap (eventually_ge_atTop ⌈x⌉₊)] with n hn
      change ⌈x⌉₊ ≤ n.val at hn
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · simp_rw [mul_comm]
      refine (Tendsto.comp (continuous_ofReal.tendsto _) ?_).const_mul _
      convert! Real.tendsto_one_add_div_pow_exp (-x) using 1
      ext1 n
      rw [neg_div₀, ← sub_eq_add_neg]
  have hbound (n : {n : ℕ // n ≠ 0}) :
      ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), ‖f n x‖ ≤ Real.exp (-x) * x ^ (s.re - 1) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi, f] at hx ⊢
    rcases lt_or_ge ((n : ℕ) : ℝ) x with (hxn | hxn)
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)]
      positivity
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩), norm_mul, Complex.norm_of_nonneg
          (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le₀ hxn <| by positivity) _),
          norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
      gcongr
      exact one_sub_div_pow_le_exp_neg hxn
  convert! tendsto_integral_filter_of_dominated_convergence
      (l := comap (Subtype.val : {n : ℕ // n ≠ 0} → ℕ) atTop)
      (fun x : ℝ ↦ Real.exp (-x) * x ^ (s.re - 1))
      (Eventually.of_forall fun n ↦ (f_ible n).1) (Eventually.of_forall hbound)
      (Real.GammaIntegral_convergent hs)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
  ext1 n
  rw [MeasureTheory.integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)),
    intervalIntegral.integral_of_le (by positivity : 0 ≤ ((n : ℕ) : ℝ)),
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

/-- Euler's limit formula for the complex Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℂ) (hregular : ∀ j : ℕ, s ≠ -j) :
    Tendsto (fun n ↦ GammaSeq s n (fun j _ ↦ hregular j)) atTop (𝓝 <| Gamma s) := by
  suffices ∀ m : ℕ, ⌊1 - s.re⌋₊ = m →
      Tendsto (fun n ↦ GammaSeq s n (fun j _ ↦ hregular j)) atTop (𝓝 <| Gamma s) by tauto
  intro m
  induction m generalizing s with intro hs
  | zero => -- Base case: `0 < re s`, so Gamma is given by the integral formula
    rw [Nat.floor_eq_zero, sub_lt_self_iff] at hs
    have hrange : Set.range (Subtype.val : {n : ℕ // n ≠ 0} → ℕ) ∈ (atTop : Filter ℕ) := by
      filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
      exact ⟨⟨n, hn⟩, rfl⟩
    apply (tendsto_comap'_iff hrange).mp
    exact (approx_Gamma_integral_tendsto_Gamma_integral hs).congr fun n ↦
      (GammaSeq_eq_approx_Gamma_integral hs n.2).symm
  | succ m IH => -- Induction step: use recurrence formulae in `s` for Gamma and GammaSeq
    have hsne : s ≠ 0 := by simpa using hregular 0
    have hregular' : ∀ j : ℕ, s + 1 ≠ -j := by
      intro j hj
      apply hregular (j + 1)
      push_cast
      linear_combination hj
    specialize IH (s + 1) hregular' ?_
    · rw [Nat.floor_eq_iff' (by lia)] at hs
      have : s.re ≤ -m := by grind
      rw [Nat.floor_eq_iff <| by simpa using (show s.re ≤ 0 by grind)]
      grind [add_re, one_re]
    rw [Gamma_add_one _ hsne] at IH
    have hden (n : ℕ) : (n : ℂ) + (1 + s) ≠ 0 := by
      have h := hregular (n + 1)
      contrapose! h
      push_cast
      linear_combination h
    have hratio := (tendsto_natCast_div_add_atTop (1 + s)).comp
      (show Tendsto (fun n : ℕ ↦ (⟨n, hden n⟩ : {n : ℕ // (n : ℂ) + (1 + s) ≠ 0}))
        atTop (comap Subtype.val atTop) from tendsto_comap_iff.mpr tendsto_id)
    have := (IH.div_const₀ s (hy := hsne.isUnit)).congr' <| by
      filter_upwards [eventually_ne_atTop 0] with n hn
      simpa only [add_assoc] using GammaSeq_add_one_left s hn (fun j _ ↦ hregular j)
    simp only [mul_comm _ (GammaSeq s _ _)] at this
    rwa [mul_div_cancel_left₀, ← mul_one (Gamma s),
      tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this
    exact hratio

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


namespace Complex

theorem GammaSeq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0)
    (hz : ∀ j ≤ n, z ≠ -j) (hz' : ∀ j ≤ n, 1 - z ≠ -j) :
    GammaSeq z n hz * GammaSeq (1 - z) n hz' *
      (z * ∏ j ∈ Finset.range n, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2)) * (n + 1 - z) = n := by
  unfold GammaSeq
  rw [div_mul_div_comm₀, div_mul_eq_mul_div₀, div_mul_eq_mul_div₀, div_eq_iff]
  have hpow : (n : ℂ) ^ z * (n : ℂ) ^ (1 - z) = n := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_sub_cancel, cpow_one]
  have hfactor (j : ℕ) : (z + ((j + 1 : ℕ) : ℂ)) * (1 - z + j) =
      ((↑(j + 1) : ℂ) ^ 2) * (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2) := by
    have hj : (j : ℂ) + 1 ≠ 0 := by rw [← Nat.cast_succ, Nat.cast_ne_zero]; exact Nat.succ_ne_zero j
    push_cast
    field
  have hprod : (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) *
      (∏ j ∈ Finset.range n, (1 - z + (j : ℂ))) =
        ((n ! : ℕ) : ℂ) ^ 2 * ∏ j ∈ Finset.range n, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib, Finset.prod_pow, ← Nat.cast_prod,
      Finset.prod_range_add_one_eq_factorial]
  rw [mul_mul_mul_comm ((n : ℂ) ^ z) (↑n ! : ℂ) ((n : ℂ) ^ (1 - z)) (↑n ! : ℂ), hpow,
    Finset.prod_range_succ' (fun j : ℕ ↦ z + (j : ℂ)) n,
    Finset.prod_range_succ (fun j : ℕ ↦ 1 - z + (j : ℂ)) n, Nat.cast_zero, add_zero,
    mul_mul_mul_comm (∏ j ∈ Finset.range n, (z + ((j + 1 : ℕ) : ℂ))) z, hprod]
  ring

/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) (hs : sin (π * z) ≠ 0) :
    Gamma z * Gamma (1 - z) = (π : ℂ) / sin (π * z) := by
  have pi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hz : ∀ j : ℕ, z ≠ -j := by
    intro j hj
    apply hs
    apply sin_eq_zero_iff.mpr
    exact ⟨-(j : ℤ), by push_cast; rw [hj]; ring⟩
  have hz' : ∀ j : ℕ, 1 - z ≠ -j := by
    intro j hj
    apply hs
    apply sin_eq_zero_iff.mpr
    refine ⟨1 + (j : ℤ), ?_⟩
    push_cast
    linear_combination -π * hj
  have hden (n : ℕ) : (n : ℂ) + (1 - z) ≠ 0 :=
    fun h ↦ hz' n (by linear_combination h)
  have hratio := (tendsto_natCast_div_add_atTop (1 - z)).comp
    (show Tendsto (fun n : ℕ ↦ (⟨n, hden n⟩ : {n : ℕ // (n : ℂ) + (1 - z) ≠ 0}))
      atTop (comap Subtype.val atTop) from tendsto_comap_iff.mpr tendsto_id)
  have hprod := ((GammaSeq_tendsto_Gamma z hz).mul (GammaSeq_tendsto_Gamma (1 - z) hz')).mul
    ((tendsto_euler_sin_prod z).div_const₀ (π : ℂ) (hy := pi_ne.isUnit))
  have heq : Gamma z * Gamma (1 - z) * (sin (π * z) / (π : ℂ)) = 1 := by
    apply tendsto_nhds_unique hprod
    apply hratio.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have h := GammaSeq_mul z hn (fun j _ ↦ hz j) (fun j _ ↦ hz' j)
    simp only [Function.comp_apply]
    apply (div_eq_iff (hb := (hden n).isUnit)).mpr
    have hpi (w : ℂ) : π * z * w / (π : ℂ) = z * w := by field
    simpa only [add_sub_assoc, hpi] using h.symm
  apply (eq_div_iff (hb := hs.isUnit)).mpr
  have := congrArg (fun x : ℂ ↦ x * π) heq
  simpa only [mul_assoc, div_mul_cancel₀, one_mul] using this

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im, ofReal_zero, zero_mul, add_zero]
    rw [this, Gamma_ofReal, ofReal_ne_zero]
    refine Real.Gamma_ne_zero fun n => ?_
    specialize hs n
    contrapose hs
    rwa [this, ← ofReal_natCast, ← ofReal_neg, ofReal_inj]
  · have : sin (↑π * s) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k
      apply_fun im
      rw [im_ofReal_mul, ← ofReal_intCast, ← ofReal_mul, ofReal_im]
      exact mul_ne_zero Real.pi_pos.ne' h_im
    have A := div_ne_zero (b := sin (π * s)) (hb := this.isUnit)
      (ofReal_ne_zero.mpr Real.pi_pos.ne')
    rw [← Complex.Gamma_mul_Gamma_one_sub s this, mul_ne_zero_iff] at A
    exact A.1

@[grind =]
theorem Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m := by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m

/-- A weaker, but easier-to-apply, version of `Complex.Gamma_ne_zero`. -/
theorem Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0 :=
  Gamma_ne_zero (Gamma_regular_of_re_pos hs)

/-- The ascending Pochhammer symbol is given by the ratio of `Γ` functions. -/
theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Checked.div (Gamma (z + n)) (Gamma z) (Gamma_ne_zero hz).isUnit =
      (ascPochhammer ℂ n).eval z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    suffices h : Gamma (z + n + 1) = Gamma (z + n) * (z + n) by
      simp [ascPochhammer_succ_right, ← ih z hz, div_mul_eq_mul_div₀, h, ← add_assoc]
    have hz₀ : z + (n : ℂ) ≠ 0 := fun h ↦ hz n (by linear_combination h)
    exact (Gamma_add_one _ hz₀).trans (mul_comm _ _)

end Complex

namespace Real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℝ) (n : ℕ) (hs : ∀ j ≤ n, s ≠ -j) : ℝ :=
  Checked.div ((n : ℝ) ^ s * n !) (∏ j ∈ Finset.range (n + 1), (s + j))
    (Finset.prod_ne_zero_iff.mpr fun j hj h ↦
      hs j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (by linear_combination h)).isUnit

/-- Euler's limit formula for the real Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℝ) (hs : ∀ j : ℕ, s ≠ -j) :
    Tendsto (fun n ↦ GammaSeq s n (fun j _ ↦ hs j)) atTop (𝓝 <| Gamma s) := by
  suffices Tendsto (fun n ↦ (GammaSeq s n (fun j _ ↦ hs j) : ℂ)) atTop
      (𝓝 <| Complex.Gamma s) by
    exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  have hregular (j : ℕ) : (s : ℂ) ≠ -j := fun h ↦ hs j (by exact_mod_cast h)
  refine (Complex.GammaSeq_tendsto_Gamma s hregular).congr fun n ↦ ?_
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_natCast]

/-- Euler's reflection formula for the real Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (s : ℝ) (hs : sin (π * s) ≠ 0) :
    Gamma s * Gamma (1 - s) = π / sin (π * s) := by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s (by
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_ne_zero] using hs)

end Real

end GammaReflection

section ReciprocalGamma

open scoped Real

namespace Complex

/-! ## The reciprocal Gamma function

The reciprocal Gamma function is the entire function agreeing with `1 / Γ(s)` away from the
nonpositive integers and vanishing at those integers. This is the convention of
[DLMF §5.2](https://dlmf.nist.gov/5.2), independently specified by the Weierstrass product
[DLMF (5.8.2)](https://dlmf.nist.gov/5.8.E2). Its definition does not evaluate Gamma or an
inverse at a pole. We prove the recurrence, entire differentiability, and the derivatives at
its zeros directly; the Weierstrass product itself is not proved here. -/

/-- The entire reciprocal Gamma function. Its values at the nonpositive integers are specified
as zero independently of the convention for the values of `Gamma` at its poles. -/
noncomputable def reciprocalGamma (s : ℂ) : ℂ := by
  classical
  exact if hs : ∀ n : ℕ, s ≠ -n then
    Checked.inv (Gamma s) (isUnit_iff_ne_zero.mpr (Gamma_ne_zero hs))
  else 0

theorem reciprocalGamma_eq_inv {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    reciprocalGamma s = Checked.inv (Gamma s) (isUnit_iff_ne_zero.mpr (Gamma_ne_zero hs)) := by
  simp only [reciprocalGamma, dite_eq_left hs]

open scoped Classical in
/-- Replacing Gamma's values at its poles has no effect on the reciprocal Gamma function.
Only the values at regular arguments are used in the defining inverse. -/
theorem reciprocalGamma_eq_of_eq_on_regular (g : ℂ → ℂ)
    (hg : ∀ s : ℂ, (∀ n : ℕ, s ≠ -n) → g s = Gamma s) (s : ℂ) :
    reciprocalGamma s = if hs : ∀ n : ℕ, s ≠ -n then
      Checked.inv (g s) (isUnit_iff_ne_zero.mpr (by rw [hg s hs]; exact Gamma_ne_zero hs))
    else 0 := by
  classical
  by_cases hs : ∀ n : ℕ, s ≠ -n
  · simp only [reciprocalGamma, dite_eq_left hs]
    exact inv_inj₀.mpr (hg s hs).symm
  · simp only [reciprocalGamma, dite_eq_right hs]

@[simp]
theorem reciprocalGamma_neg_nat (n : ℕ) : reciprocalGamma (-n) = 0 := by
  exact dite_eq_right (by intro h; exact h n rfl)

@[simp]
theorem reciprocalGamma_zero : reciprocalGamma 0 = 0 := by
  simpa only [Nat.cast_zero, neg_zero] using reciprocalGamma_neg_nat 0

@[simp]
theorem reciprocalGamma_one : reciprocalGamma 1 = 1 := by
  rw [reciprocalGamma_eq_inv (by intro n; exact_mod_cast (by omega : (1 : ℤ) ≠ -n))]
  simp only [Gamma_one, inv_one₀]

@[simp, grind =]
theorem reciprocalGamma_eq_zero_iff (s : ℂ) :
    reciprocalGamma s = 0 ↔ ∃ n : ℕ, s = -n := by
  by_cases hs : ∀ n : ℕ, s ≠ -n
  · rw [reciprocalGamma_eq_inv hs]
    simp only [inv_ne_zero, false_iff, not_exists]
    exact hs
  · push Not at hs
    obtain ⟨n, rfl⟩ := hs
    simp

theorem reciprocalGamma_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    reciprocalGamma s ≠ 0 := by
  rw [reciprocalGamma_eq_inv hs]
  exact inv_ne_zero

theorem reciprocalGamma_mul_Gamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    reciprocalGamma s * Gamma s = 1 := by
  rw [reciprocalGamma_eq_inv hs, inv_mul_cancel₀]

theorem Gamma_mul_reciprocalGamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    Gamma s * reciprocalGamma s = 1 := by
  rw [mul_comm, reciprocalGamma_mul_Gamma hs]

/-- Euler's reflection formula for the entire reciprocal Gamma function. -/
theorem reciprocalGamma_mul_reciprocalGamma_one_sub (s : ℂ) :
    reciprocalGamma s * reciprocalGamma (1 - s) = sin (π * s) / (π : ℂ) := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  by_cases hsin : sin (π * s) = 0
  · rw [hsin, zero_div]
    have hz : sin (-(π * s)) = 0 := by rw [sin_neg, hsin, neg_zero]
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp hz
    have hneg : -s = (k : ℂ) := mul_left_cancel₀ hp (by
      simpa only [mul_neg, mul_comm (k : ℂ)] using hk)
    have hs : s = -(k : ℂ) := by linear_combination -hneg
    rw [hs]
    cases k with
    | ofNat n =>
      rw [show -((Int.ofNat n : ℤ) : ℂ) = -(n : ℂ) by simp, reciprocalGamma_neg_nat, zero_mul]
    | negSucc n =>
      rw [show (1 : ℂ) - -((Int.negSucc n : ℤ) : ℂ) = -(n : ℂ) by
        simp only [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one]; ring,
        reciprocalGamma_neg_nat, mul_zero]
  · have hg : Gamma s * Gamma (1 - s) ≠ 0 := by
      rw [Gamma_mul_Gamma_one_sub s hsin]
      exact div_ne_zero hp
    have hregular {z : ℂ} (hz : Gamma z ≠ 0) : ∀ n : ℕ, z ≠ -n := by
      intro n he
      exact hz ((Gamma_eq_zero_iff z).2 ⟨n, he⟩)
    apply mul_right_cancel₀ hg
    calc
      reciprocalGamma s * reciprocalGamma (1 - s) * (Gamma s * Gamma (1 - s)) = 1 := by
        rw [mul_mul_mul_comm, reciprocalGamma_mul_Gamma (hregular (mul_ne_zero_iff.mp hg).1),
          reciprocalGamma_mul_Gamma (hregular (mul_ne_zero_iff.mp hg).2), one_mul]
      _ = sin (π * s) / (π : ℂ) * (Gamma s * Gamma (1 - s)) := by
        rw [Gamma_mul_Gamma_one_sub s hsin]
        field

/-- The reciprocal Gamma recurrence holds everywhere, including at its zeros. -/
theorem reciprocalGamma_eq_self_mul_reciprocalGamma_add_one (s : ℂ) :
    reciprocalGamma s = s * reciprocalGamma (s + 1) := by
  by_cases hs : ∀ n : ℕ, s ≠ -n
  · have hs0 : s ≠ 0 := by simpa using hs 0
    have hs1 : ∀ n : ℕ, s + 1 ≠ -n := by
      intro n hn
      apply hs (n + 1)
      push_cast
      linear_combination hn
    apply mul_right_cancel₀ (Gamma_ne_zero hs)
    calc
      reciprocalGamma s * Gamma s = 1 := reciprocalGamma_mul_Gamma hs
      _ = reciprocalGamma (s + 1) * Gamma (s + 1) := (reciprocalGamma_mul_Gamma hs1).symm
      _ = _ := by rw [Gamma_add_one s hs0]; ring
  · push Not at hs
    obtain ⟨n, rfl⟩ := hs
    cases n with
    | zero =>
      simp only [Nat.cast_zero, neg_zero, zero_mul]
      exact reciprocalGamma_zero
    | succ n =>
      rw [reciprocalGamma_neg_nat,
        show -(↑(n + 1) : ℂ) + 1 = -n by push_cast; ring, reciprocalGamma_neg_nat, mul_zero]

theorem reciprocalGamma_add_one {s : ℂ} (hs : s ≠ 0) :
    reciprocalGamma (s + 1) = reciprocalGamma s / s := by
  rw [eq_div_iff, mul_comm, ← reciprocalGamma_eq_self_mul_reciprocalGamma_add_one]

/-- On the right half-plane, the checked inverse of Gamma gives the derivative of its
reciprocal. The proof transports the derivative from its actual domain and uses no pole values. -/
theorem differentiableAt_reciprocalGamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ reciprocalGamma s := by
  have hGamma := differentiableAt_Gamma s (Gamma_regular_of_re_pos hs)
  have hu : IsUnit (Gamma s) := isUnit_iff_ne_zero.mpr (Gamma_ne_zero_of_re_pos hs)
  obtain ⟨d, hd⟩ := hGamma.inv hu
  have hdom : {z : ℂ | IsUnit (Gamma z)} ∈ 𝓝 s :=
    hGamma.continuousAt.eventually (Units.isOpen.mem_nhds hu)
  have heq : ∀ᶠ z : {z : ℂ | IsUnit (Gamma z)} in 𝓝 ⟨s, hu⟩,
      reciprocalGamma z = (↑z.property.unit⁻¹ : ℂ) := by
    filter_upwards [((continuous_re.comp continuous_subtype_val).tendsto ⟨s, hu⟩).eventually
      (eventually_gt_nhds hs)] with z hz
    exact reciprocalGamma_eq_inv (Gamma_regular_of_re_pos hz)
  have hcenter : reciprocalGamma s = (↑hu.unit⁻¹ : ℂ) :=
    reciprocalGamma_eq_inv (Gamma_regular_of_re_pos hs)
  have hrec : DifferentiableAt ℂ
      (fun z : {z : ℂ | IsUnit (Gamma z)} ↦ reciprocalGamma z) ⟨s, hu⟩
      (fun z ↦ (z : ℂ)) := by
    refine ⟨d, HasFDerivAt.of_isLittleOTVS ?_⟩
    apply hd.isLittleOTVS.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [heq] with z hz
    simp only [hz, hcenter]
  exact DifferentiableAt.of_restrict (f := reciprocalGamma) (s := {z : ℂ | IsUnit (Gamma z)})
    (x := ⟨s, hu⟩) (coord := id) hrec hdom

/-- The reciprocal Gamma function is differentiable everywhere, including at the poles of Gamma. -/
@[fun_prop]
theorem differentiable_reciprocalGamma : Differentiable ℂ reciprocalGamma := fun s ↦ by
  rcases exists_nat_gt (-s.re) with ⟨n, hs⟩
  induction n generalizing s with
  | zero =>
    rw [Nat.cast_zero, neg_lt_zero] at hs
    exact differentiableAt_reciprocalGamma_of_re_pos hs
  | succ n ihn =>
    rw [funext reciprocalGamma_eq_self_mul_reciprocalGamma_add_one]
    specialize ihn (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ← Nat.cast_succ])
    exact differentiableAt_id.mul (ihn.comp s (f := fun s => s + 1) <|
      differentiableAt_id.add_const (1 : ℂ))

theorem analyticOnNhd_reciprocalGamma : AnalyticOnNhd ℂ reciprocalGamma univ :=
  differentiable_reciprocalGamma.differentiableOn.analyticOnNhd isOpen_univ

/-- The zeros of reciprocal Gamma are simple; the derivative at `-n` is `(-1)^n n!`. -/
theorem hasDerivAt_reciprocalGamma_neg_nat (n : ℕ) :
    HasDerivAt reciprocalGamma ((-1 : ℂ) ^ n * n !) (-n) := by
  induction n with
  | zero =>
    have hd : HasDerivAt (fun z : ℂ ↦ reciprocalGamma (z + 1)) (deriv reciprocalGamma 1) 0 :=
      HasDerivAt.comp_add_const 0 1
        (by simpa only [zero_add] using (differentiable_reciprocalGamma 1).hasDerivAt)
    rw [funext reciprocalGamma_eq_self_mul_reciprocalGamma_add_one]
    simpa only [Nat.cast_zero, neg_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, zero_add, reciprocalGamma_one, id_eq, zero_mul, add_zero] using
      (hasDerivAt_id (0 : ℂ)).fun_mul hd
  | succ n ih =>
    have hshift : -(↑(n + 1) : ℂ) + 1 = -n := by push_cast; ring
    have hprev : HasDerivAt reciprocalGamma ((-1 : ℂ) ^ n * n !) (-(↑(n + 1) : ℂ) + 1) :=
      hshift.symm ▸ ih
    have hd := (hasDerivAt_id (-(↑(n + 1) : ℂ))).fun_mul
      (HasDerivAt.comp_add_const _ 1 hprev)
    have hcoef : (-1 : ℂ) ^ (n + 1) * ((n + 1)! : ℕ) =
        -(↑(n + 1) : ℂ) * ((-1 : ℂ) ^ n * n !) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      ring
    rw [funext reciprocalGamma_eq_self_mul_reciprocalGamma_add_one, hcoef]
    simpa only [hshift, reciprocalGamma_neg_nat, mul_zero, zero_add, id_eq] using hd

theorem deriv_reciprocalGamma_neg_nat (n : ℕ) :
    deriv reciprocalGamma (-n) = (-1 : ℂ) ^ n * n ! :=
  (hasDerivAt_reciprocalGamma_neg_nat n).deriv

theorem deriv_reciprocalGamma_neg_nat_ne_zero (n : ℕ) :
    deriv reciprocalGamma (-n) ≠ 0 := by
  rw [deriv_reciprocalGamma_neg_nat]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

lemma betaIntegral_eq_Gamma_mul_div (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Checked.div (Gamma u * Gamma v) (Gamma (u + v))
      (Gamma_ne_zero_of_re_pos (by simpa only [add_re] using add_pos hu hv)).isUnit := by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv,
      mul_div_cancel_left₀]

end Complex

end ReciprocalGamma

section Doubling

/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/


namespace Complex

/-- Legendre's duplication formula for the entire reciprocal Gamma function. -/
theorem reciprocalGamma_mul_reciprocalGamma_add_half (s : ℂ) :
    reciprocalGamma s * reciprocalGamma (s + 1 / 2) =
      reciprocalGamma (2 * s) * (2 : ℂ) ^ (2 * s - 1) / ↑(√π) := by
  suffices (fun z => reciprocalGamma z * reciprocalGamma (z + 1 / 2)) =
      (fun z => reciprocalGamma (2 * z) * (2 : ℂ) ^ (2 * z - 1) / ↑(√π)) from
    congr_fun this s
  have h1 : AnalyticOnNhd ℂ
      (fun z : ℂ => reciprocalGamma z * reciprocalGamma (z + 1 / 2)) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine (differentiable_reciprocalGamma.mul ?_).differentiableOn
    exact differentiable_reciprocalGamma.comp (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOnNhd ℂ
      (fun z => reciprocalGamma (2 * z) * (2 : ℂ) ^ (2 * z - 1) / ↑(√π)) univ := by
    have hR : Differentiable ℂ (fun z : ℂ ↦ reciprocalGamma (2 * z)) :=
      differentiable_reciprocalGamma.comp (differentiable_id.const_mul _)
    have hpow : Differentiable ℂ (fun z : ℂ ↦ (2 : ℂ) ^ (2 * z - 1)) := fun t ↦
      ((differentiableAt_id (x := t)).const_mul 2 |>.sub_const 1).const_cpow (Or.inl two_ne_zero)
    have hsqrt : (↑(√π) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr pi_pos)
    exact ((hR.mul hpow).div_const _ (hd := hsqrt.isUnit)).differentiableOn.analyticOnNhd
      isOpen_univ
  have h3 : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ofReal_ne_one.mpr ht)
  refine AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
  refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
  refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
  have ht' : ∀ n : ℕ, (t : ℂ) ≠ -n := by
    intro n hn
    have := congr_arg re hn
    simp only [ofReal_re, neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hthalf : ∀ n : ℕ, (t : ℂ) + 1 / 2 ≠ -n := by
    intro n hn
    have := congr_arg re hn
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have httwo : ∀ n : ℕ, 2 * (t : ℂ) ≠ -n := by
    intro n hn
    have := congr_arg re hn
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hgamma : Gamma (t : ℂ) * Gamma ((t : ℂ) + 1 / 2) =
      Gamma (2 * (t : ℂ)) * (2 : ℂ) ^ (1 - 2 * (t : ℂ)) * ↑(√π) := by
    simpa only [ofReal_mul, ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat, ofReal_sub,
      ← Gamma_ofReal, ofReal_cpow zero_le_two] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (Real.Gamma_mul_Gamma_add_half_of_pos ht)
  have hp : (2 : ℂ) ^ (2 * (t : ℂ) - 1) * (2 : ℂ) ^ (1 - 2 * (t : ℂ)) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show 2 * (t : ℂ) - 1 + (1 - 2 * t) = 0 by ring, cpow_zero]
  have hsqrt : (↑(√π) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr pi_pos)
  apply mul_right_cancel₀ (mul_ne_zero (Gamma_ne_zero ht') (Gamma_ne_zero hthalf))
  rw [mul_mul_mul_comm, reciprocalGamma_mul_Gamma ht', reciprocalGamma_mul_Gamma hthalf,
    one_mul, hgamma]
  calc
    1 = (reciprocalGamma (2 * (t : ℂ)) * Gamma (2 * (t : ℂ))) *
        ((2 : ℂ) ^ (2 * (t : ℂ) - 1) * (2 : ℂ) ^ (1 - 2 * (t : ℂ))) := by
      rw [reciprocalGamma_mul_Gamma httwo, hp, one_mul]
    _ = _ := by field

theorem Gamma_mul_Gamma_add_half (s : ℂ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s) * ↑(√π) := by
  let p : ℂ := (2 : ℂ) ^ (2 * s - 1)
  let q : ℂ := (2 : ℂ) ^ (1 - 2 * s)
  let r : ℂ := ↑(√π)
  have hr : r ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr pi_pos)
  have hp : p ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hpq : p * q = 1 := by
    dsimp only [p, q]
    rw [← cpow_add _ _ two_ne_zero, show 2 * s - 1 + (1 - 2 * s) = 0 by ring, cpow_zero]
  have hrec := reciprocalGamma_mul_reciprocalGamma_add_half s
  change reciprocalGamma s * reciprocalGamma (s + 1 / 2) = reciprocalGamma (2 * s) * p / r at hrec
  have hzero (z : ℂ) : reciprocalGamma z = 0 ↔ Gamma z = 0 := by
    rw [reciprocalGamma_eq_zero_iff, Gamma_eq_zero_iff]
  have hzeros : Gamma s * Gamma (s + 1 / 2) = 0 ↔ Gamma (2 * s) = 0 := by
    calc
      _ ↔ reciprocalGamma s * reciprocalGamma (s + 1 / 2) = 0 := by
        simp only [mul_eq_zero, hzero]
      _ ↔ _ := by rw [hrec, div_eq_zero_iff, mul_eq_zero, or_iff_left hp, hzero]
  by_cases h2 : Gamma (2 * s) = 0
  · rw [hzeros.mpr h2, h2, zero_mul, zero_mul]
  have hg := mul_ne_zero_iff.mp (mt hzeros.mp h2)
  have hR : reciprocalGamma s * reciprocalGamma (s + 1 / 2) ≠ 0 := by
    simpa only [ne_eq, mul_eq_zero, hzero] using (mul_ne_zero hg.1 hg.2)
  have hmul {z : ℂ} (hz : Gamma z ≠ 0) : reciprocalGamma z * Gamma z = 1 :=
    reciprocalGamma_mul_Gamma (fun n hn ↦ hz ((Gamma_eq_zero_iff z).2 ⟨n, hn⟩))
  change Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * q * r
  apply mul_left_cancel₀ hR
  calc
    reciprocalGamma s * reciprocalGamma (s + 1 / 2) * (Gamma s * Gamma (s + 1 / 2)) = 1 := by
      rw [mul_mul_mul_comm, hmul hg.1, hmul hg.2, one_mul]
    _ = (reciprocalGamma (2 * s) * Gamma (2 * s)) * (p * q) := by
      rw [hmul h2, hpq, one_mul]
    _ = (reciprocalGamma s * reciprocalGamma (s + 1 / 2)) * (Gamma (2 * s) * q * r) := by
      rw [hrec]
      symm
      calc
        _ = (reciprocalGamma (2 * s) * p / r * (Gamma (2 * s) * q)) * r := (mul_assoc _ _ _).symm
        _ = (reciprocalGamma (2 * s) * p * (Gamma (2 * s) * q) / r) * r := by
          rw [div_mul_eq_mul_div₀]
        _ = _ := by rw [div_mul_cancel₀]; ring

end Complex

namespace Real

open Complex

theorem Gamma_mul_Gamma_add_half (s : ℝ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * √π := by
  rw [← ofReal_inj]
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using! Complex.Gamma_mul_Gamma_add_half ↑s

end Real

end Doubling

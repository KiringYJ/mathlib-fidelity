/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.HalfPlane

/-!
# Differentiability and derivatives of L-series

## Main results

* We show that the `LSeries` of `f` is differentiable at `s` when `re s` is greater than
  the abscissa of absolute convergence of `f` (`LSeries.hasDerivAt`) and that its derivative
  there is the negative of the `LSeries` of the point-wise product `log * f` (`LSeries.deriv`).

* We prove similar results for iterated derivatives (`LSeries.iteratedDeriv`).

* We use this to show that `LSeries f` is holomorphic on the right half-plane of
  absolute convergence (`LSeries.analyticOnNhd`).

## Implementation notes

We introduce `LSeries.logMul` as an abbreviation for the point-wise product `log * f`, to avoid
the problem that this expression does not type-check.
-/

public section

open Complex LSeries

/-!
### The derivative of an L-series
-/

/-- The (point-wise) product of `log : ℕ → ℂ` with `f`. -/
noncomputable abbrev LSeries.logMul (f : ℕ → ℂ) (n : ℕ) : ℂ := log n * f n

/-- The derivative of the terms of an L-series. -/
lemma LSeries.hasDerivAt_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ term f z n) (-(term (logMul f) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hasDerivAt_const]
  let p : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
  have hf (z : ℂ) : term f z n = f n * (n : ℂ) ^ (-z) := term_eq_mul_cpow_neg f z p
  have hg : term (logMul f) s n = logMul f n * (n : ℂ) ^ (-s) :=
    term_eq_mul_cpow_neg (logMul f) s p
  simp_rw [hf, hg]
  have hd := (hasDerivAt_neg' s).const_cpow (c := (n : ℂ))
    (Or.inl (Nat.cast_ne_zero.mpr hn))
  convert HasDerivAt.const_mul (f n) hd using 1
  simp only [logMul]
  ring

/- This lemma proves two things at once, since their proofs are intertwined; we give separate
non-private lemmas below that extract the two statements. -/
private lemma LSeries.LSeriesSummable_logMul_and_hasDerivAt {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries (logMul f) s) s := by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  -- We work in the right half-plane `y < re z`, for some `y` such that `x < y < re s`, on which
  -- we have a uniform summable bound on `‖term f z ·‖`.
  let S : Set ℂ := {z | y < z.re}
  have h₀ : Summable (fun n ↦ ‖term f x n‖) := summable_norm_iff.mpr hf
  have h₁ (n) : DifferentiableOn ℂ (term f · n) S :=
    fun z _ ↦ (hasDerivAt_term f n _).differentiableAt.differentiableWithinAt
  have h₂ : IsOpen S := isOpen_lt continuous_const continuous_re
  have h₃ (n z) (hz : z ∈ S) : ‖term f z n‖ ≤ ‖term f x n‖ :=
    norm_term_le_of_re_le_re f (by simpa using! (hxy.trans hz).le) n
  have H := hasSum_deriv_of_summable_norm h₀ h₁ h₂ h₃ hys
  simp_rw [(hasDerivAt_term f _ _).deriv] at H
  refine ⟨summable_neg_iff.mp H.summable, ?_⟩
  simpa [← H.tsum_eq, tsum_neg] using! ((differentiableOn_tsum_of_summable_norm
    h₀ h₁ h₂ h₃).differentiableAt <| h₂.mem_nhds hys).hasDerivAt

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then the L-series
of `f` is differentiable with derivative the negative of the L-series of the point-wise
product of `log` with `f`. -/
lemma LSeries_hasDerivAt {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (-LSeries (logMul f) s) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).2

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series at `s` is the negative of the L-series of `log * f`. -/
lemma LSeries_deriv {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) s = -LSeries (logMul f) s :=
  (LSeries_hasDerivAt h).deriv

/-- The derivative of the L-series of `f` agrees with the negative of the L-series of
`log * f` on the right half-plane of absolute convergence. -/
lemma LSeries_deriv_eqOn {f : ℕ → ℂ} :
    {s | abscissaOfAbsConv f < s.re}.EqOn (deriv (LSeries f)) (-LSeries (logMul f)) :=
  deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs ↦ (LSeries_hasDerivAt hs).hasDerivWithinAt

/-- If the L-series of `f` is summable at `s` and `re s < re s'`, then the L-series of the
point-wise product of `log` with `f` is summable at `s'`. -/
lemma LSeriesSummable_logMul_of_lt_re {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).1

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
@[simp]
lemma LSeries.abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs ↦ ?_
  · exact LSeriesSummable_logMul_of_lt_re <| by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp [hs])
      |>.norm.of_norm_bounded_eventually_nat (g := fun n ↦ ‖term (logMul f) s n‖) ?_
    filter_upwards [Filter.eventually_ge_atTop <| max 1 (Nat.ceil (Real.exp 1))] with n hn
    have hn₀ : n ≠ 0 := by omega
    have hnorm : ‖term (logMul f) s n‖ = ‖log (n : ℂ)‖ * ‖term f s n‖ := by
      rw [term_of_ne_zero hn₀, term_of_ne_zero hn₀, logMul, mul_div_assoc₀, norm_mul]
    rw [hnorm]
    refine le_mul_of_one_le_left (norm_nonneg (term f s n)) ?_
    rw [← natCast_log, norm_real]
    refine le_trans ?_ (Real.le_norm_self _)
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (Nat.ceil_le.mp ((le_max_right _ _).trans hn))

/-!
### Higher derivatives of L-series
-/

/-- The abscissa of absolute convergence of the point-wise product of a power of `log` and `f`
is the same as that of `f`. -/
@[simp]
lemma LSeries.absicssaOfAbsConv_logPowMul {f : ℕ → ℂ} {m : ℕ} :
    abscissaOfAbsConv (logMul^[m] f) = abscissaOfAbsConv f := by
  induction m with
  | zero => simp
  | succ n ih => simp [ih, Function.iterate_succ', Function.comp_def,
      -Function.comp_apply, -Function.iterate_succ]

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then
the `m`th derivative of this L-series is `(-1)^m` times the L-series of `log^m * f`. -/
lemma LSeries_iteratedDeriv {f : ℕ → ℂ} (m : ℕ) {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv m (LSeries f) s = (-1) ^ m * LSeries (logMul^[m] f) s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs ↦ ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_re_gt_EReal _) h] at this
    rw [iteratedDeriv_succ]
    dsimp only
    rw [this]
    simp only [Pi.mul_def, Pi.pow_apply, Pi.neg_apply, Pi.one_apply]
    rw [deriv_const_mul_field, LSeries_deriv (absicssaOfAbsConv_logPowMul.symm ▸ h)]
    simp [pow_succ, Function.iterate_succ', -Function.iterate_succ]

/-!
### The L-series is holomorphic
-/

/-- The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence. -/
lemma LSeries_differentiableOn (f : ℕ → ℂ) :
    DifferentiableOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  fun _ hz ↦ (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt

/-- The L-series of `f` is holomorphic on its open half-plane of absolute convergence. -/
lemma LSeries_analyticOnNhd (f : ℕ → ℂ) :
    AnalyticOnNhd ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_differentiableOn f).analyticOnNhd <| isOpen_re_gt_EReal _

lemma LSeries_analyticOn (f : ℕ → ℂ) :
    AnalyticOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_analyticOnNhd f).analyticOn

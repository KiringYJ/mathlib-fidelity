/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Infinitely smooth transition function

In this file we construct two infinitely smooth functions with properties that an analytic function
cannot have:

* `expNegInvGlue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `Real.smoothTransition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`;
-/

@[expose] public section

noncomputable section

open scoped Topology
open Polynomial Real Filter Set Function

/-- `expNegInvGlue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`expNegInvGlue.contDiff`. -/
def expNegInvGlue (x : ℝ) : ℝ :=
  if hx : 0 < x then exp (-Checked.inv x hx.ne'.isUnit) else 0

namespace expNegInvGlue

/-- The function `expNegInvGlue` vanishes on `(-∞, 0]`. -/
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by
  simp [expNegInvGlue, not_lt_of_ge hx]

@[simp]
protected theorem zero : expNegInvGlue 0 = 0 := zero_of_nonpos le_rfl

/-- The function `expNegInvGlue` is positive on `(0, +∞)`. -/
theorem pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < expNegInvGlue x := by
  simp [expNegInvGlue, hx, exp_pos]

/-- The function `expNegInvGlue` is nonnegative. -/
theorem nonneg (x : ℝ) : 0 ≤ expNegInvGlue x := by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)

@[simp] theorem zero_iff_nonpos {x : ℝ} : expNegInvGlue x = 0 ↔ x ≤ 0 :=
  ⟨fun h ↦ not_lt.mp fun h' ↦ (pos_of_pos h').ne' h, zero_of_nonpos⟩

protected theorem monotone : Monotone expNegInvGlue := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx, nonneg]
  simp [expNegInvGlue, hx, hx.trans_le hxy,
    inv_le_inv₀ (hx.trans_le hxy) hx, hxy]

/-- The function `expNegInvGlue` is not analytic at `0`. -/
theorem not_analyticAt_zero : ¬ AnalyticAt ℝ expNegInvGlue 0 := by
  intro h
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  suffices expNegInvGlue (r / 2) = 0 from (pos_of_pos (half_pos hr)).ne' this
  exact h.eqOn_zero_of_preconnected_of_mem_closure (z₀ := 0)
    (Real.ball_eq_Ioo 0 r ▸ isPreconnected_Ioo)
    (by simp [hr]) (by simp [Set.Iic_def]) (by simp [abs_of_pos, hr])

/-!
### Smoothness of `expNegInvGlue`

In this section we prove that the function `f = expNegInvGlue` is infinitely smooth. To do
this, we show that $g_p(x)=p(x^{-1})f(x)$ is infinitely smooth for any polynomial `p` with real
coefficients. First we show that $g_p(x)$ tends to zero at zero, then we show that it is
differentiable with derivative $g_p'=g_{x^2(p-p')}$. Finally, we prove smoothness of $g_p$ by
induction, then deduce smoothness of $f$ by setting $p=1$.
-/

/-- Extend `x ↦ p(x⁻¹) * exp(-x⁻¹)` from the positive reals by zero. -/
def polynomialEvalInvMul (p : ℝ[X]) (x : ℝ) : ℝ :=
  if hx : 0 < x then p.eval (Checked.inv x hx.ne'.isUnit) * expNegInvGlue x else 0

/-- The zero extension of `p(x⁻¹) * exp(-x⁻¹)` tends to zero at zero. -/
theorem tendsto_polynomial_inv_mul_zero (p : ℝ[X]) :
    Tendsto (polynomialEvalInvMul p) (𝓝 0) (𝓝 0) := by
  have hnhds : 𝓝[≤] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) = 𝓝 0 := by
    rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]
  nth_rw 1 [← hnhds]
  rw [tendsto_sup]
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [polynomialEvalInvMul, dite_eq_right (not_lt_of_ge (mem_Iic.mp hx))]
  · let U := {x : ℝ // IsUnit x}
    have hU : range (Subtype.val : U → ℝ) ∈ 𝓝[>] (0 : ℝ) := by
      refine mem_of_superset self_mem_nhdsWithin ?_
      exact fun x hx ↦ ⟨⟨x, hx.ne'.isUnit⟩, rfl⟩
    rw [← tendsto_comap'_iff hU]
    apply (p.tendsto_div_exp_atTop.comp tendsto_inv_nhdsGT_zero).congr'
    have hpos : ∀ᶠ x : U in comap Subtype.val (𝓝[>] (0 : ℝ)), 0 < (x : ℝ) :=
      tendsto_comap.eventually self_mem_nhdsWithin
    filter_upwards [hpos] with x hx
    have hx' : 0 < (x : ℝ) := hx
    simp only [Function.comp_apply, polynomialEvalInvMul, expNegInvGlue, dite_eq_left hx',
      exp_neg, div_eq_mul_inv₀]

theorem hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (polynomialEvalInvMul p)
      (polynomialEvalInvMul (X ^ 2 * (p - p.derivative)) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [polynomialEvalInvMul, dite_eq_right (not_lt_of_ge hx.le)]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    simp only [polynomialEvalInvMul, dite_eq_right (not_lt_of_ge hy.le)]
  · rw [show polynomialEvalInvMul (X ^ 2 * (p - p.derivative)) 0 = 0 by
        simp [polynomialEvalInvMul], hasDerivAt_iff_tendsto_slope]
    apply ((tendsto_polynomial_inv_mul_zero (p * X)).comp tendsto_comap).congr
    intro y
    change _ = slope (polynomialEvalInvMul p) 0 y (Ne.symm y.2)
    by_cases hy : 0 < (y : ℝ)
    · simp only [Function.comp_apply, slope_fun_def_field, polynomialEvalInvMul, dite_eq_left hy,
        lt_irrefl, dite_false, sub_zero, eval_mul, eval_X]
      ring
    · simp only [Function.comp_apply, slope_fun_def_field, polynomialEvalInvMul, dite_eq_right hy,
        lt_irrefl, dite_false, sub_self, zero_div]
  · let g (y : ℝ) := if hy : 0 < y then Checked.inv y hy.ne'.isUnit else 0
    have hpos : ∀ᶠ y in 𝓝 x, 0 < y := Ioi_mem_nhds hx
    have hg : g x = x⁻¹ := dite_eq_left hx
    have hc : ContDiffAt ℝ 1 g x :=
      contDiffAt_id.inv (hpos.mono fun y hy ↦ ⟨hy.ne'.isUnit, dite_eq_left hy⟩)
    have hd := (hc.differentiableAt (by decide)).hasDerivAt
    have hconst : HasDerivAt (fun y ↦ g y * y) 0 x := by
      refine (hasDerivAt_const _ 1).congr_of_eventuallyEq ?_
      filter_upwards [hpos] with y hy
      simp only [g, dite_eq_left hy, inv_mul_cancel₀]
    have heq := (hd.mul (hasDerivAt_id x)).unique hconst
    simp only [id_eq, mul_one, hg] at heq
    have hdg : HasDerivAt g (-(x⁻¹) ^ 2) x := by
      have hder : deriv g x = -(x⁻¹) ^ 2 := by
        apply (mul_left_injective₀ hx.ne')
        change deriv g x id * x = (-(x⁻¹) ^ 2) * x
        rw [show deriv g x id * x = -x⁻¹ by linarith]
        field
      exact hder ▸ hd
    have hcom := ((p.hasDerivAt (g x)).mul (hasDerivAt_neg _).exp).scomp x hdg
    change HasDerivAt (fun y ↦ p.eval (g y) * exp (-(g y))) _ x at hcom
    have hcom' : HasDerivAt (fun y ↦ p.eval (g y) * exp (-(g y)))
        (polynomialEvalInvMul (X ^ 2 * (p - p.derivative)) x) x := by
      convert hcom using 1
      simp only [polynomialEvalInvMul, expNegInvGlue, dite_eq_left hx, hg, eval_mul, eval_pow,
        eval_X, eval_sub]
      ring
    apply hcom'.congr_of_eventuallyEq
    filter_upwards [hpos] with y hy
    simp only [polynomialEvalInvMul, expNegInvGlue, g, dite_eq_left hy]

theorem differentiable_polynomial_eval_inv_mul (p : ℝ[X]) :
    Differentiable ℝ (polynomialEvalInvMul p) := fun x ↦
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt

theorem continuous_polynomial_eval_inv_mul (p : ℝ[X]) :
    Continuous (polynomialEvalInvMul p) :=
  (differentiable_polynomial_eval_inv_mul p).continuous

theorem contDiff_polynomial_eval_inv_mul {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (polynomialEvalInvMul p) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
  | zero => exact contDiff_zero.2 <| continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eval_inv_mul _, by simp, ?_⟩
    convert! ihm (X ^ 2 * (p - p.derivative)) using 2
    exact (hasDerivAt_polynomial_eval_inv_mul p _).deriv

/-- The function `expNegInvGlue` is smooth. -/
@[fun_prop]
protected theorem contDiff {n : ℕ∞} : ContDiff ℝ n expNegInvGlue := by
  have h : polynomialEvalInvMul 1 = expNegInvGlue := by
    funext x
    by_cases hx : 0 < x
    · simp [polynomialEvalInvMul, hx]
    · simp [polynomialEvalInvMul, hx, zero_of_nonpos (not_lt.mp hx)]
  rw [← h]
  exact contDiff_polynomial_eval_inv_mul 1

end expNegInvGlue

theorem Real.smoothTransition.pos_denom (x : ℝ) :
    0 < expNegInvGlue x + expNegInvGlue (1 - x) := by
  open expNegInvGlue in
  exact
    (zero_lt_one.gt_or_lt x).elim (fun hx ↦ add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
      fun hx ↦ add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos (sub_pos.mpr hx))

/-- An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`,
`f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`. -/
def Real.smoothTransition (x : ℝ) : ℝ :=
  Checked.div (expNegInvGlue x) (expNegInvGlue x + expNegInvGlue (1 - x))
    (Real.smoothTransition.pos_denom x).ne'.isUnit

namespace Real

namespace smoothTransition

variable {x : ℝ}

open expNegInvGlue

theorem one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1 :=
  div_eq_one_iff_eq.2 <| by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x ≤ 0 := by
  simp only [smoothTransition, div_eq_zero_iff, expNegInvGlue.zero_iff_nonpos]

theorem zero_of_nonpos (h : x ≤ 0) : smoothTransition x = 0 := zero_iff_nonpos.2 h

@[simp]
protected theorem zero : smoothTransition 0 = 0 :=
  zero_of_nonpos le_rfl

@[simp]
protected theorem one : smoothTransition 1 = 1 :=
  one_of_one_le le_rfl

/-- Since `Real.smoothTransition` is constant on $(-∞, 0]$ and $[1, ∞)$, applying it to the
projection of `x : ℝ` to $[0, 1]$ gives the same result as applying it to `x`. -/
@[simp]
protected theorem projIcc :
    smoothTransition (projIcc (0 : ℝ) 1 zero_le_one x) = smoothTransition x := by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]

theorem le_one (x : ℝ) : smoothTransition x ≤ 1 :=
  (div_le_one (pos_denom x)).2 <| le_add_of_nonneg_right (nonneg _)

theorem nonneg (x : ℝ) : 0 ≤ smoothTransition x :=
  div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le

theorem lt_one_of_lt_one (h : x < 1) : smoothTransition x < 1 :=
  (div_lt_one <| pos_denom x).2 <| lt_add_of_pos_right _ <| pos_of_pos <| sub_pos.2 h

theorem pos_of_pos (h : 0 < x) : 0 < smoothTransition x :=
  div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)

@[simp] theorem eq_one_iff_one_le : smoothTransition x = 1 ↔ 1 ≤ x := by
  rcases le_or_gt 1 x with hx | hx
  · simp [hx, one_of_one_le]
  · simpa [(lt_one_of_lt_one hx).ne] using hx

@[fun_prop]
protected theorem contDiff {n : ℕ∞} : ContDiff ℝ n smoothTransition :=
  expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    (h := fun x ↦ (pos_denom x).ne'.isUnit)

@[fun_prop]
protected theorem contDiffAt {x : ℝ} {n : ℕ∞} : ContDiffAt ℝ n smoothTransition x :=
  smoothTransition.contDiff.contDiffAt

@[fun_prop]
protected theorem continuous : Continuous smoothTransition :=
  (@smoothTransition.contDiff 0).continuous

@[fun_prop]
protected theorem continuousAt : ContinuousAt smoothTransition x :=
  smoothTransition.continuous.continuousAt

protected theorem monotone : Monotone smoothTransition := by
  intro x y hxy
  simp only [smoothTransition]
  rw [div_le_div_iff₀ (pos_denom x) (pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_le_add_iff_left]
  gcongr
  · exact expNegInvGlue.nonneg _
  · exact expNegInvGlue.nonneg _
  · apply expNegInvGlue.monotone hxy
  · apply expNegInvGlue.monotone (by linarith)

end smoothTransition

end Real

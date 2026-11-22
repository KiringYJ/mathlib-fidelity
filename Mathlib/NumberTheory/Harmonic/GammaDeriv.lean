/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

public section

open Nat Set Filter Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace Real

/-- Explicit formula for the derivative of the Gamma function at positive integers, in terms of
harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m ↦ by linarith))
      (hx := (Gamma_pos_of_pos (by positivity : (0 : ℝ) < n + 1)).ne'),
      div_eq_iff_mul_eq, Gamma_nat_eq_factorial,
      mul_comm, Eq.comm] at this
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const, one_div₀, ← deriv_log (hx := hx.ne'.isUnit),
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : ℝ)) (by linarith) (hder <| by positivity)
    rw [slope_def_field]
    apply (eq_div_iff).mpr
    rw [show n + 1 - n = (1 : ℝ) by ring, mul_one, h_rec n (by positivity), add_sub_cancel_left]
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field]
    apply (div_eq_iff).mpr
    rw [show n + 2 - (n + 1) = (1 : ℝ) by ring, mul_one,
      show n + 2 = (n + 1) + (1 : ℝ) by ring, h_rec (n + 1) (by positivity), add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, sub_le_iff_le_add', ← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add', ← sub_eq_add_neg, le_sub_iff_add_le', ← hder_nat]
    exact derivUB n


lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) :=
  (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m ↦ (by linarith : (n : ℝ) + 1 ≠ -m)).hasDerivAt

lemma eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have h_diff {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ Gamma s :=
    differentiableAt_Gamma fun m ↦ ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (fun s ↦ Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s ↦ Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul, Gamma_one_half_eq,
      add_assoc, ← mul_add, deriv_comp_add_const,
      (by norm_num : 1 / 2 + 1 / 2 = (1 : ℝ)), Gamma_one, mul_one,
      eulerMascheroniConstant_eq_neg_deriv, add_neg_cancel, mul_zero, add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π, mul_comm √π, deriv_mul_const, add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
    · exact continuousAt_id
  _ = √π * (deriv (fun s ↦ Gamma (2 * s)) (1 / 2) +
              deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s ↦ 2 * s) _ = _
    rw [deriv_comp, deriv_const_mul_id, mul_one_div₀, div_self]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    refine HasDerivAt.deriv ?_ Topology.IsOpenEmbedding.id
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : ℝ) (2 : ℝ))
      (?_ : HasDerivAt (fun s : ℝ ↦ 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : ℝ) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : ℝ)
  _ = -√π * (γ + 2 * log 2) := by ring

end Real

namespace Complex

open scoped Real

private lemma HasDerivAt.complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

lemma differentiableAt_Gamma_nat_add_one (n : ℕ) :
    DifferentiableAt ℂ Gamma (n + 1) := by
  refine differentiableAt_Gamma _ (fun m ↦ ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) := by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

/-- Explicit formula for the derivative of the complex Gamma function at positive integers, in
terms of harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) :=
  (hasDerivAt_Gamma_nat n).deriv

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div₀, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast, ← ofReal_neg, ne_eq, ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

lemma hasDerivAt_Gammaℂ_one : HasDerivAt Gammaℂ (-(γ + log (2 * π)) / (π : ℂ)) 1 := by
  have hp : IsUnit (2 * π : ℂ) :=
    (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)).isUnit
  have hf : HasDerivAt (fun s : ℂ ↦ 2 * (2 * π : ℂ) ^ (-s)) (-log (2 * π) / (π : ℂ)) 1 := by
    have := (hasDerivAt_neg' (1 : ℂ)).const_cpow (c := 2 * π)
      (Or.inl hp.ne_zero)
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one, mul_neg, cpow_neg_one _ (hx := hp), ← div_eq_inv_mul₀, ← mul_div_assoc₀,
      mul_div_mul_left _ _, neg_div₀]
  have hfactor : (2 : ℂ) * (2 * π : ℂ) ^ (-1 : ℂ) = 1 / (π : ℂ) := by
    simpa only [Gammaℂ_def, Gamma_one, mul_one] using Gammaℂ_one
  refine (hf.mul hasDerivAt_Gamma_one).congr_deriv ?_
  simp only [Gamma_one, mul_one, hfactor, div_eq_mul_inv₀]
  ring

lemma hasDerivAt_Gammaℝ_one : HasDerivAt Gammaℝ (-(γ + log (4 * π)) / 2) 1 := by
  let f (s : ℂ) : ℂ := π ^ (-s / 2)
  let g (s : ℂ) : ℂ := Gamma (s / 2)
  have aux : (π : ℂ) ^ (1 / 2 : ℂ) = ↑√π := by
    have hhalf : (↑(1 / 2 : ℝ) : ℂ) = 1 / 2 := by
      apply (eq_div_iff).mpr
      rw [← ofReal_ofNat 2, ← ofReal_mul]
      norm_num
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le, hhalf]
  have aux2 : (√π : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
  have hrec : f 1 = Checked.inv (↑√π : ℂ) aux2.isUnit := by
    have hp : IsUnit ((π : ℂ) ^ (1 / 2 : ℂ)) := by rw [aux]; exact aux2.isUnit
    change (π : ℂ) ^ (-1 / 2 : ℂ) = _
    rw [neg_div₀, cpow_neg _ _ (hxy := hp)]
    exact inv_inj₀.mpr aux
  have hf : HasDerivAt f (-log π / 2 / (√π : ℂ)) 1 := by
    have hd := ((hasDerivAt_neg (1 : ℂ)).div_const 2 (hd := two_ne_zero.isUnit)).const_cpow (c := π)
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    refine hd.congr_deriv ?_
    change f 1 * log π * (-1 / 2) = -log π / 2 / (√π : ℂ)
    rw [hrec]
    simp only [div_eq_mul_inv₀]
    ring
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have hhalf : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2) (1 : ℂ) :=
      (hasDerivAt_id (1 : ℂ)).div_const 2
    simpa only [g, Function.comp_def, mul_one_div₀] using
      hasDerivAt_Gamma_one_half.comp (h := fun z : ℂ ↦ z / 2) (coord' := id) (1 : ℂ) hhalf
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  change -log π / 2 / (√π : ℂ) * Gamma (1 / 2) + f 1 * _ = _
  rw [Gamma_one_half_eq, aux, div_mul_cancel₀, hrec]
  have hterm : Checked.inv (↑√π : ℂ) aux2.isUnit * (-↑√π * (γ + 2 * log 2) / 2) =
      -(γ + 2 * log 2) / 2 := by
    rw [← mul_div_assoc₀, ← mul_assoc, mul_neg, inv_mul_cancel₀, neg_one_mul]
  have hlog : log ((4 : ℂ) * π) = log π + 2 * log 2 := by
    have hr : Real.log ((4 : ℝ) * π) = Real.log π + 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
        Real.log_mul (pow_ne_zero _ two_ne_zero) Real.pi_ne_zero, Real.log_pow, Nat.cast_ofNat,
        add_comm]
    simpa only [ofReal_log (by positivity : (0 : ℝ) ≤ 4 * π), ofReal_log Real.pi_pos.le,
      ofReal_log zero_le_two, ofReal_add, ofReal_mul, ofReal_ofNat] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hr
  rw [hterm, hlog]
  ring

/-- The derivative of the entire reciprocal Gamma function at one. -/
lemma hasDerivAt_reciprocalGamma_one : HasDerivAt reciprocalGamma γ 1 := by
  have hR := (differentiable_reciprocalGamma 1).hasDerivAt
  refine hR.congr_deriv ?_
  have hpos : ∀ᶠ z : ℂ in 𝓝 1, 0 < z.re :=
    (continuous_re.tendsto 1).eventually (eventually_gt_nhds (by norm_num))
  have heq : (fun z : ℂ ↦ reciprocalGamma z * Gamma z) =ᶠ[𝓝 1] fun _ ↦ 1 := by
    filter_upwards [hpos] with z hz
    apply reciprocalGamma_mul_Gamma
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd := ((hR.mul hasDerivAt_Gamma_one).congr_of_eventuallyEq heq.symm).unique
    (hasDerivAt_const (1 : ℂ) (1 : ℂ))
  simp only [Gamma_one, reciprocalGamma_one, mul_one, one_mul] at hd
  linear_combination hd

/-- The derivative of the entire reciprocal real-place Gamma factor at one. -/
lemma hasDerivAt_reciprocalGammaℝ_one :
    HasDerivAt reciprocalGammaℝ ((γ + log (4 * π)) / 2) 1 := by
  have hR := (differentiable_reciprocalGammaℝ 1).hasDerivAt
  refine hR.congr_deriv ?_
  have hpos : ∀ᶠ z : ℂ in 𝓝 1, 0 < z.re :=
    (continuous_re.tendsto 1).eventually (eventually_gt_nhds (by norm_num))
  have heq : (fun z : ℂ ↦ reciprocalGammaℝ z * Gammaℝ z) =ᶠ[𝓝 1] fun _ ↦ 1 := by
    filter_upwards [hpos] with z hz
    apply reciprocalGammaℝ_mul_Gammaℝ
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd := ((hR.mul hasDerivAt_Gammaℝ_one).congr_of_eventuallyEq heq.symm).unique
    (hasDerivAt_const (1 : ℂ) (1 : ℂ))
  simp only [Gammaℝ_one, reciprocalGammaℝ_one, mul_one, one_mul] at hd
  linear_combination hd

end Complex

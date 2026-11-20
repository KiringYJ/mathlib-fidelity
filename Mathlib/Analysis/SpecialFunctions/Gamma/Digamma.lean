/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv.Basic
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv


/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.digamma_apply_add_nat`: The iterated recurrence
  `digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹`.
* `Complex.digamma_nat_add_one`: The digamma function at positive integers, in terms of harmonic
  numbers: `digamma (n + 1) = harmonic n - eulerMascheroniConstant`.
* `Complex.digamma_one_sub`: Euler's reflection formula
  `digamma (1 - s) = digamma s + π * cot (π * s)`.
* `Complex.digamma_two_mul`: The duplication formula
  `digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2`.
* `Complex.meromorphicDigamma`: The meromorphic section represented by digamma.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

open scoped Real
open Filter Set Topology

namespace Complex

/-- The digamma function, defined as the logarithmic derivative of Gamma on its regular domain. -/
noncomputable def digamma (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n := by assumption) : ℂ :=
  logDeriv Gamma s (hderiv := (differentiableAt_Gamma s hs).existsUnique_hasDerivAt)
    (hvalue := (Gamma_ne_zero hs).isUnit)

theorem digamma_def (s : ℂ) {hs : ∀ n : ℕ, s ≠ -n} :
    digamma s hs = logDeriv Gamma s
      (hderiv := (differentiableAt_Gamma s hs).existsUnique_hasDerivAt)
      (hvalue := (Gamma_ne_zero hs).isUnit) := rfl

theorem digamma_one :
    digamma 1 (Gamma_regular_of_re_pos (by simp)) = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_eq hasDerivAt_Gamma_one, div_eq_iff, Gamma_one, mul_one]

theorem digamma_one_half : digamma (1 / 2)
      (Gamma_regular_of_re_pos (by rw [div_ofNat_re, one_re]; positivity)) =
    - 2 * log 2 - Real.eulerMascheroniConstant := by
  have hΓ : Gamma (1 / 2) = ↑√π := by
    have hhalf : (↑(1 / 2 : ℝ) : ℂ) = 1 / 2 := by
      apply eq_div_iff.mpr
      rw [← ofReal_ofNat 2, ← ofReal_mul]
      norm_num
    rw [← hhalf, Gamma_ofReal, Real.Gamma_one_half_eq]
  rw [digamma_def, logDeriv_eq hasDerivAt_Gamma_one_half, div_eq_iff, hΓ]
  ring

theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) (fun n h ↦ hs (n + 1) (by push_cast; linear_combination h)) =
      digamma s hs + Checked.inv s ((by simpa using hs 0 : s ≠ 0).isUnit) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hg : IsUnit (Gamma s) := (Gamma_ne_zero hs).isUnit
  rw [digamma_def, digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs,
    div_eq_iff, Gamma_add_one s hs0]
  field

/-- **The iterated digamma recurrence** `ψ(s + n) = ψ(s) + ∑_{k < n} 1 / (s + k)`, for
`s ∉ {0, -1, -2, …}`. Proved by induction from `digamma_apply_add_one`. -/
theorem digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    digamma (s + n) (fun m h ↦ hs (m + n) (by push_cast; linear_combination h)) =
      digamma s hs + ∑ k ∈ Finset.range n, Checked.inv (s + k)
        (Ne.isUnit (fun h ↦ hs k (eq_neg_of_add_eq_zero_left h))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h ↦
      hs (m + n) (by push_cast at h ⊢; linear_combination h)
    simp only [Nat.cast_succ, ← add_assoc, digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]

open scoped ComplexOrder in
/-- The digamma function at a positive integer, in terms of harmonic numbers. -/
theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) (Gamma_regular_of_re_pos (by rw [add_re, one_re, natCast_re]; positivity)) =
      harmonic n - Real.eulerMascheroniConstant := by
  simp only [add_comm _ (1 : ℂ),
    digamma_apply_add_nat (s := 1) (Gamma_regular_of_re_pos (by simp)) n,
    digamma_one, harmonic]
  push_cast [add_comm (1 : ℂ)]
  ring

/-- An argument outside the integers avoids the zeros of `sin (π s)`. -/
private theorem sin_pi_mul_ne_zero {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : sin (π * s) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
  apply hs n
  apply mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)
  simpa only [mul_comm (n : ℂ)] using hn

private theorem regular_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (n : ℕ) : s ≠ -n := by
  exact_mod_cast hs (-(n : ℤ))

private theorem regular_one_sub_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n)
    (n : ℕ) : 1 - s ≠ -n := by
  intro h
  apply hs ((n : ℤ) + 1)
  push_cast
  linear_combination -h

/-- **Euler's reflection formula for the digamma function**:
`ψ (1 - s) = ψ s + π * cot (π * s)` for `s` not an integer. -/
theorem digamma_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    digamma (1 - s) (by exact regular_one_sub_of_not_int hs) =
      digamma s (by exact regular_of_not_int hs) +
        π * cot (π * s) (by exact sin_pi_mul_ne_zero hs) := by
  have hsin := sin_pi_mul_ne_zero hs
  have hg := Gamma_ne_zero (regular_of_not_int hs)
  have hg' := Gamma_ne_zero (regular_one_sub_of_not_int hs)
  have heq : (fun z : ℂ ↦ Gamma z * Gamma (1 - z) * sin (π * z)) =ᶠ[𝓝 s] fun _ ↦ π := by
    filter_upwards [(isOpen_ne_fun (continuous_sin.comp (continuous_const.mul continuous_id))
      continuous_const).mem_nhds hsin] with z hz
    rw [Gamma_mul_Gamma_one_sub z hz, div_mul_cancel₀]
  have hdg := (differentiableAt_Gamma s (regular_of_not_int hs)).hasDerivAt
  have hdg' := (differentiableAt_Gamma (1 - s) (regular_one_sub_of_not_int hs)).hasDerivAt.comp s
    ((hasDerivAt_id s).const_sub 1)
  have hds := (hasDerivAt_sin (π * s)).comp s ((hasDerivAt_id s).const_mul (π : ℂ))
  have hd := ((hdg.fun_mul hdg').fun_mul hds).congr_of_eventuallyEq heq.symm
  have h := hd.unique (hasDerivAt_const s (π : ℂ))
  simp only [Function.comp_apply, mul_one, mul_neg] at h
  rw [digamma_def, digamma_def, logDeriv_apply, logDeriv_apply, cot_eq_cos_div_sin]
  field_simp
  simp only [mul_comm s (π : ℂ)]
  linear_combination -h

/-- If `g` has derivative `a` at `s`, then the logarithmic derivative of `Gamma ∘ g` at `s` is
`a * digamma (g s)`. -/
theorem _root_.HasDerivAt.logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
    (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
    logDeriv (Gamma ∘ g) s
      (hderiv := ((differentiableAt_Gamma (g s) h).hasDerivAt.comp s hg).existsUnique_hasDerivAt)
      (hvalue := (Gamma_ne_zero h).isUnit) = a * digamma (g s) h := by
  rw [logDeriv_eq ((differentiableAt_Gamma (g s) h).hasDerivAt.comp s hg), digamma_def,
    logDeriv_apply]
  have hΓ := (Gamma_ne_zero h).isUnit
  change deriv Gamma (g s) * a / Gamma (g s) = _
  simp only [div_eq_mul_inv₀]
  ring

private theorem regular_of_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ))
    (m : ℕ) : s ≠ -(m : ℂ) := fun h ↦
  hs (2 * m) (by push_cast; linear_combination 2 * h)

private theorem regular_add_half_of_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ))
    (m : ℕ) : s + 1 / 2 ≠ -(m : ℂ) := fun h ↦
  hs (2 * m + 1) (by push_cast; linear_combination 2 * h)

/-- **The digamma duplication formula** `ψ(2s) = ½(ψ(s) + ψ(s + ½)) + log 2`, for
`2s ∉ {0, -1, -2, …}`, which is equivalent to `s` and `s + ½` both avoiding the poles of `ψ`.
Proved from Legendre's duplication formula by taking logarithmic derivatives. -/
theorem digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ)) :
    digamma (2 * s) hs =
      (1 / 2) * (digamma s (by exact regular_of_two_mul hs) +
        digamma (s + 1 / 2) (by exact regular_add_half_of_two_mul hs)) + log 2 := by
  have hg := Gamma_ne_zero hs
  have hg₀ := Gamma_ne_zero (regular_of_two_mul hs)
  have hg₁ := Gamma_ne_zero (regular_add_half_of_two_mul hs)
  have hA := (differentiableAt_Gamma s (regular_of_two_mul hs)).hasDerivAt
  have hB := (differentiableAt_Gamma (s + 1 / 2) (regular_add_half_of_two_mul hs)).hasDerivAt.comp
    (coord' := id) s ((hasDerivAt_id s).add_const (1 / 2))
  have hC := (differentiableAt_Gamma (2 * s) hs).hasDerivAt.comp
    (coord' := id) s ((hasDerivAt_id s).const_mul 2)
  let w (z : ℂ) := (2 : ℂ) ^ (1 - 2 * z)
  have hW : HasDerivAt w (-2 * log 2 * w s) s := by
    convert ((hasDerivAt_id' s).const_mul 2 |>.const_sub 1).const_cpow
      (c := 2) (Or.inl two_ne_zero) using 1
    simp [w]
    ring
  have hD := (hA.fun_mul hB).unique
    (((hC.fun_mul hW).mul_const (√π : ℂ)).congr_of_eventuallyEq
      (Eventually.of_forall Gamma_mul_Gamma_add_half))
  simp only [Function.comp_apply, id_eq, mul_one] at hD
  have heq : digamma s (regular_of_two_mul hs) +
      digamma (s + 1 / 2) (regular_add_half_of_two_mul hs) =
        2 * digamma (2 * s) hs - 2 * log 2 := by
    simp only [digamma_def, logDeriv_apply]
    apply mul_right_cancel₀ (mul_ne_zero hg₀ hg₁)
    calc
      _ = deriv Gamma s * Gamma (s + 1 / 2) + Gamma s * deriv Gamma (s + 1 / 2) := by field
      _ = (deriv Gamma (2 * s) * 2 * w s + Gamma (2 * s) * (-2 * log 2 * w s)) * √π := hD
      _ = _ := by rw [Gamma_mul_Gamma_add_half]; unfold w; field
  linear_combination (-1 / 2 : ℂ) * heq

/-- The derivative of the reciprocal Gamma function is entire. -/
theorem analyticOnNhd_deriv_reciprocalGamma :
    AnalyticOnNhd ℂ (deriv reciprocalGamma) univ :=
  fun z hz ↦ (analyticOnNhd_reciprocalGamma z hz).deriv

open TopologicalSpace MeromorphicSection in
/-- The meromorphic digamma section, given by the negative logarithmic derivative of the entire
reciprocal Gamma function. -/
noncomputable def meromorphicDigamma : MeromorphicSection (⊤ : Opens ℂ) :=
  -(ofAnalyticOn (deriv reciprocalGamma) analyticOnNhd_deriv_reciprocalGamma * meromorphicGamma)

private theorem digamma_eq_neg_deriv_reciprocalGamma_mul_Gamma {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) :
    digamma s hs = -(deriv reciprocalGamma s * Gamma s) := by
  have hprod : (fun z ↦ reciprocalGamma z * Gamma z) =ᶠ[𝓝 s] fun _ ↦ 1 := by
    filter_upwards [differentiable_reciprocalGamma.continuous.continuousAt.eventually_ne
      (reciprocalGamma_ne_zero hs)] with z hz
    apply reciprocalGamma_mul_Gamma
    intro n h
    exact hz ((reciprocalGamma_eq_zero_iff z).mpr ⟨n, h⟩)
  have h := (((differentiable_reciprocalGamma s).hasDerivAt.fun_mul
    (differentiableAt_Gamma s hs).hasDerivAt).congr_of_eventuallyEq hprod.symm).unique
    (hasDerivAt_const s (1 : ℂ))
  rw [digamma_def, logDeriv_apply, div_eq_iff]
  calc
    _ = Gamma s * (reciprocalGamma s * deriv Gamma s) := by
      rw [← mul_assoc, Gamma_mul_reciprocalGamma hs, one_mul]
    _ = _ := by rw [eq_neg_of_add_eq_zero_right h]; ring

open TopologicalSpace MeromorphicSection MeromorphicGerm AnalyticGerm in
private theorem germ_meromorphicDigamma_of_regular {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    germ (⟨s, mem_univ s⟩ : (⊤ : Opens ℂ)) meromorphicDigamma =
      ofAnalytic (ofFun (-(deriv reciprocalGamma * Gamma))
        (((analyticOnNhd_deriv_reciprocalGamma s (mem_univ s)).mul
          (analyticAt_Gamma hs)).neg)) := by
  rw [meromorphicDigamma, map_neg, map_mul, germ_ofAnalyticOn, germ_meromorphicGamma_of_regular hs,
    ofFun_neg, ofFun_mul, map_neg, map_mul]
  exact (analyticOnNhd_deriv_reciprocalGamma s (mem_univ s)).mul (analyticAt_Gamma hs)

open TopologicalSpace MeromorphicSection in
/-- The digamma section is regular wherever the scalar digamma function is defined. -/
theorem mem_regularLocus_meromorphicDigamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    (⟨s, mem_univ s⟩ : (⊤ : Opens ℂ)) ∈ regularLocus meromorphicDigamma :=
  ⟨_, (germ_meromorphicDigamma_of_regular hs).symm⟩

open TopologicalSpace MeromorphicSection MeromorphicGerm AnalyticGerm in
/-- The poles of the meromorphic digamma section are the nonpositive integers. -/
theorem mem_regularLocus_meromorphicDigamma_iff (s : ℂ) :
    (⟨s, mem_univ s⟩ : (⊤ : Opens ℂ)) ∈ regularLocus meromorphicDigamma ↔ ∀ n : ℕ, s ≠ -n := by
  refine ⟨?_, mem_regularLocus_meromorphicDigamma⟩
  intro hs n hn
  subst s
  let z := (⟨-(n : ℂ), mem_univ _⟩ : (⊤ : Opens ℂ))
  let a := ofFun (deriv reciprocalGamma)
    (analyticOnNhd_deriv_reciprocalGamma z (mem_univ _))
  have ha : IsUnit a := (AnalyticGerm.isUnit_iff_eval_ne_zero a).mpr
    (deriv_reciprocalGamma_neg_nat_ne_zero n)
  let u := ha.unit
  have hu : (↑u⁻¹ : AnalyticGerm (z : ℂ)) * a = 1 :=
    (congrArg ((↑u⁻¹ : AnalyticGerm (z : ℂ)) * ·) ha.unit_spec.symm).trans u.inv_val
  have hEq : ofAnalytic (↑u⁻¹ : AnalyticGerm (z : ℂ)) * -germ z meromorphicDigamma =
      germ z meromorphicGamma := by
    rw [meromorphicDigamma, map_neg, neg_neg, map_mul, germ_ofAnalyticOn, ← mul_assoc, ← map_mul]
    change ofAnalytic ((↑u⁻¹ : AnalyticGerm (z : ℂ)) * a) * _ = _
    rw [hu, map_one, one_mul]
  have hRegular : z ∈ regularLocus meromorphicGamma := by
    rw [regularLocus, mem_ofPred_eq, ← hEq]
    exact (regularSubring (z : ℂ)).mul_mem ⟨_, rfl⟩ ((regularSubring (z : ℂ)).neg_mem hs)
  exact (mem_regularLocus_meromorphicGamma_iff _).mp hRegular n rfl

open MeromorphicSection MeromorphicGerm AnalyticGerm in
@[simp] theorem eval_meromorphicDigamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    MeromorphicSection.eval meromorphicDigamma
      ⟨⟨s, mem_univ s⟩, mem_regularLocus_meromorphicDigamma hs⟩ = digamma s hs := by
  rw [digamma_eq_neg_deriv_reciprocalGamma_mul_Gamma hs]
  let g := ofFun (-(deriv reciprocalGamma * Gamma))
    (((analyticOnNhd_deriv_reciprocalGamma s (mem_univ s)).mul (analyticAt_Gamma hs)).neg)
  trans AnalyticGerm.eval g
  · apply Eq.trans _ (eval_ofAnalytic g)
    exact congrArg MeromorphicGerm.eval (Subtype.ext (germ_meromorphicDigamma_of_regular hs))
  · rfl

end Complex

/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The functional equation for the logarithmic derivative of the Riemann zeta function

Differentiating the functional equation `riemannZeta_one_sub` logarithmically gives an identity
relating `ζ'/ζ (s)` and `ζ'/ζ (1 - s)`, involving the digamma function `ψ` and a tangent term.

## Main statements

* `logDeriv_riemannZeta_one_sub`: for `s` not an integer with `ζ s ≠ 0`,
  `ζ'/ζ (s) = -ζ'/ζ (1 - s) + log (2 π) - ψ s + (π / 2) * tan (π s / 2)`.
-/

@[expose] public section

open scoped Real
open Complex Filter Set Topology

private theorem regular_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (n : ℕ) : s ≠ -n := by
  exact_mod_cast hs (-(n : ℤ))

private theorem ne_one_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : s ≠ 1 := by
  simpa only [Int.cast_one] using hs 1

private theorem one_sub_ne_one_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) : 1 - s ≠ 1 := by
  intro h
  apply regular_of_not_int hs 0
  norm_num
  linear_combination -h

private theorem cos_pi_mul_div_two_ne_zero_of_not_int {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    cos (π * s / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h
  apply hs (2 * k + 1)
  push_cast
  apply mul_left_cancel₀
    (div_ne_zero (b := (2 : ℂ)) (hb := (two_ne_zero : (2 : ℂ) ≠ 0).isUnit)
      (ofReal_ne_zero.mpr Real.pi_ne_zero))
  linear_combination hk

private theorem riemannZeta_one_sub_isUnit {s : ℂ} (hs : ∀ n : ℤ, s ≠ n)
    (hz : IsUnit (riemannZeta s (ne_one_of_not_int hs))) :
    IsUnit (riemannZeta (1 - s) (one_sub_ne_one_of_not_int hs)) := by
  rw [riemannZeta_one_sub (regular_of_not_int hs) (ne_one_of_not_int hs)]
  have hp : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact (((two_ne_zero.isUnit.mul (cpow_ne_zero_iff.mpr (.inl hp)).isUnit).mul
    (Gamma_ne_zero (regular_of_not_int hs)).isUnit).mul
    (cos_pi_mul_div_two_ne_zero_of_not_int hs).isUnit).mul hz

local notation "D" => {z : ℂ // z ≠ 1}
local notation "ζ" => (fun z : D ↦ riemannZeta z (Subtype.property z))
local notation "coord" => (fun z : D ↦ (z : ℂ))

private theorem existsUnique_hasDerivAt_riemannZeta (z : D) : ∃! d, HasDerivAt ζ d z coord :=
  (differentiableAt_riemannZeta z.2).existsUnique_hasDerivAt
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal

/-- **The functional equation for the Riemann zeta function, in logarithmic-derivative form.**
For `s` not an integer with `riemannZeta s ≠ 0`,
`ζ'/ζ (s) = -ζ'/ζ (1 - s) + log (2 π) - ψ s + (π / 2) * tan (π s / 2)`, where `ψ` is the digamma
function. -/
theorem logDeriv_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n)
    (hz : riemannZeta s (by exact ne_one_of_not_int hs) ≠ 0) :
    logDeriv ζ ⟨s, by exact ne_one_of_not_int hs⟩ coord
        (by exact existsUnique_hasDerivAt_riemannZeta _) hz.isUnit =
      -logDeriv ζ ⟨1 - s, by exact one_sub_ne_one_of_not_int hs⟩ coord
        (by exact existsUnique_hasDerivAt_riemannZeta _)
        (by exact riemannZeta_one_sub_isUnit hs hz.isUnit) +
        log (2 * π) - digamma s (by exact regular_of_not_int hs) +
          (π : ℂ) / 2 * tan (π * s / 2) (by exact cos_pi_mul_div_two_ne_zero_of_not_int hs) := by
  have h0 : s ≠ 0 := by simpa using hs 0
  have h1 := ne_one_of_not_int hs
  have h1' := one_sub_ne_one_of_not_int hs
  have hΓ := Gamma_ne_zero (regular_of_not_int hs)
  have hcos := cos_pi_mul_div_two_ne_zero_of_not_int hs
  have hζ := isUnit_riemannZeta₁ h1 (hζ := hz.isUnit)
  have hζ' := isUnit_riemannZeta₁ h1' (hζ := riemannZeta_one_sub_isUnit hs hz.isUnit)
  have h2π : 2 * (π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  let P (z : ℂ) := (2 * (π : ℂ)) ^ (-z)
  let C (z : ℂ) := cos (π * z / 2)
  let F (z : ℂ) := 2 * P z * Gamma z * C z
  have hP : P s ≠ 0 := cpow_ne_zero_iff.mpr (.inl h2π)
  have hC : C s ≠ 0 := hcos
  have hF : F s ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hP) hΓ) hC
  have hR {z : ℂ} (hz : z ≠ 1) : riemannZeta₁ z = (z - 1) * riemannZeta z hz := by
    rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀, one_mul]
  have hEq : (fun z : ℂ ↦ riemannZeta₁ (1 - z) * (z - 1)) =ᶠ[𝓝 s]
      (fun z ↦ -z * F z * riemannZeta₁ z) := by
    filter_upwards [isClosed_range_intCast.isOpen_compl.mem_nhds (by grind)] with z hz'
    have hint : ∀ n : ℤ, z ≠ n := by simpa [Set.mem_range, eq_comm] using hz'
    rw [hR (ne_one_of_not_int hint), hR (one_sub_ne_one_of_not_int hint),
      riemannZeta_one_sub (regular_of_not_int hint) (ne_one_of_not_int hint)]
    dsimp only [F, P, C]
    ring
  have dP : HasDerivAt P (-(log (2 * π)) * P s) s := by
    have hh := (hasDerivAt_neg' s).const_cpow (c := 2 * π) (Or.inl h2π)
    change HasDerivAt P (P s * log (2 * π) * (-1)) s at hh
    convert hh using 1
    ring
  have dC : HasDerivAt C (-((π : ℂ) / 2) * sin (π * s / 2)) s := by
    have h := ((hasDerivAt_id' s).const_mul (π : ℂ)).div_const (2 : ℂ)
      (hd := (two_ne_zero : (2 : ℂ) ≠ 0).isUnit)
    have hd := HasDerivAt.comp (h := fun z : ℂ ↦ π * z / 2) (coord' := id) s
      (hasDerivAt_cos (π * s / 2)) h
    change HasDerivAt C (-sin (π * s / 2) * ((π : ℂ) * 1 / 2)) s at hd
    convert hd using 1
    ring
  let dF := (2 * (-(log (2 * π)) * P s) * Gamma s + 2 * P s * deriv Gamma s) * C s +
    2 * P s * Gamma s * (-((π : ℂ) / 2) * sin (π * s / 2))
  have hdΓ := (differentiableAt_Gamma s (regular_of_not_int hs)).hasDerivAt
  have hdF : HasDerivAt F dF s :=
    ((dP.const_mul 2).fun_mul hdΓ).fun_mul dC
  have dL := (HasDerivAt.comp (h := fun z : ℂ ↦ 1 - z) (coord' := id) s
    (differentiable_riemannZeta₁ (1 - s)).hasDerivAt ((hasDerivAt_id' s).const_sub 1)).fun_mul
      ((hasDerivAt_id' s).sub_const 1)
  have dR := (((hasDerivAt_neg' s).fun_mul hdF).fun_mul
    (differentiable_riemannZeta₁ s).hasDerivAt)
  have hD := (dL.congr_of_eventuallyEq hEq.symm).unique dR
  simp only [Function.comp_apply, mul_one] at hD
  have hlogarithmic :
      -(deriv riemannZeta₁ (1 - s) / riemannZeta₁ (1 - s)) + (s - 1)⁻¹ =
        s⁻¹ - log (2 * π) + deriv Gamma s / Gamma s -
          (π : ℂ) / 2 * (sin (π * s / 2) / cos (π * s / 2)) +
          deriv riemannZeta₁ s / riemannZeta₁ s := by
    calc
      _ = (deriv riemannZeta₁ (1 - s) * (-1) * (s - 1) + riemannZeta₁ (1 - s)) /
          (riemannZeta₁ (1 - s) * (s - 1)) := by field
      _ = ((-1 * F s + -s * dF) * riemannZeta₁ s + -s * F s * deriv riemannZeta₁ s) /
          (-s * F s * riemannZeta₁ s) := by
        simp only [hEq.eq_of_nhds, hD]
      _ = _ := by
        dsimp only [F, dF, C]
        field
  rw [logDeriv_apply, logDeriv_apply, log_deriv_riemannZeta_eq_neg_inv_sub_add_at h1,
    log_deriv_riemannZeta_eq_neg_inv_sub_add_at h1', digamma_def, logDeriv_apply,
    tan_eq_sin_div_cos]
  simp only [sub_sub_cancel_left, inv_neg₀, neg_neg]
  linear_combination -hlogarithmic

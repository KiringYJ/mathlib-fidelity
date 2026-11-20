/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/
module

public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a Gaussian.

## Results

* `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
  The Hermite polynomial is (up to sign) the polynomial factor occurring in the
  `n`th derivative of a Gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

public section


noncomputable section

open Polynomial

namespace Polynomial

/-- `hermite n` is (up to sign) the factor appearing in `deriv^[n]` of a Gaussian. -/
theorem deriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  rw [mul_assoc]
  induction n generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
  | succ n ih =>
    have ih' := _root_.funext ih
    have hGauss : HasDerivAt (fun y => Real.exp (-(y ^ 2 / 2)))
        (-x * Real.exp (-(x ^ 2 / 2))) x := by
      have h := (((hasDerivAt_id' x).fun_pow 2).div_const (2 : ℝ)
        (hd := (two_ne_zero : (2 : ℝ) ≠ 0).isUnit)).fun_neg.exp
      convert h using 1
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring
    rw [Function.iterate_succ_apply', ih', deriv_const_mul_field, deriv_fun_mul, pow_succ (-1 : ℝ),
      hGauss.deriv, hermite_succ, map_sub, map_mul, aeval_X, Polynomial.deriv_aeval]
    · ring
    · apply Polynomial.differentiable_aeval
    · exact hGauss.differentiableAt

theorem hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / Real.exp (-(x ^ 2 / 2)) := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  field_simp
  rw [← pow_mul]
  simp

theorem hermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  rw [hermite_eq_deriv_gaussian, div_eq_iff]
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Polynomial

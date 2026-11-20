/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Exp on the upper half plane

This file contains lemmas about the exponential function on the upper half plane. Useful for
q-expansions of modular forms.
-/

public section

open Real Complex UpperHalfPlane

theorem UpperHalfPlane.norm_exp_two_pi_I_lt_one (τ : ℍ) :
    ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have hre : (2 * (π : ℂ) * Complex.I * τ).re = -(2 * π) * τ.im := by
    simp [Complex.mul_re, Complex.mul_im, neg_mul]
  rw [hre]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.two_pi_pos) τ.im_pos

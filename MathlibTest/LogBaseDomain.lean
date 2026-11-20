/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Domain checks for the absolute-value logarithm in a base. -/

noncomputable section

-- The base domain retains negative bases whose absolute value is distinct from one.
example : Real.logb (-2) (-2) = 1 := Real.logb_self_eq_one

example : Real.logb (-2) (-8) = Real.logb 2 8 := by
  rw [Real.logb_neg_base_eq_logb, Real.logb_neg_eq_logb]

-- A base logarithm and its inverse use the evidence already carried by their terms.
example (a b : ℝ) {ha0 : a ≠ 0} {hb0 : b ≠ 0}
    {ha : IsUnit (Real.log a)} {hab : IsUnit (Real.logb a b)} :
    (Real.logb a b)⁻¹ =
      Real.logb b a (hb := (Real.logb_ne_zero_iff.mp hab.ne_zero).isUnit) :=
  Real.inv_logb a b

example (b : ℝ) {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    Function.Surjective (fun x : {x : ℝ // x ≠ 0} => Real.logb b x.1 (hx := x.2)) :=
  Real.logb_surjective

-- A vanishing logarithm of the base cannot supply an admissible divisor.
example : ¬ IsUnit (Real.log (1 : ℝ)) := by simp
example : ¬ IsUnit (Real.log (-1 : ℝ)) := by simp

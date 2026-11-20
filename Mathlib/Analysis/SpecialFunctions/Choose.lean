/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Binomial coefficients and factorial variants

This file proves asymptotic theorems for binomial coefficients and factorial variants.

## Main statements

* `isEquivalent_descFactorial` is the proof that `n.descFactorial k ~ n^k` as `n → ∞`.
* `isEquivalent_choose` is the proof that `n.choose k ~ n^k / k!` as `n → ∞`.
* `isTheta_choose` is the proof that `n.choose k = Θ(n^k)` as `n → ∞`.
-/

public section


open Asymptotics Filter Nat Topology

/-- `n.descFactorial k` is asymptotically equivalent to `n^k`. -/
lemma isEquivalent_descFactorial (k : ℕ) :
    (fun (n : ℕ) ↦ (n.descFactorial k : ℝ)) ~[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [descFactorial_succ, cast_mul, _root_.pow_succ']
    refine IsEquivalent.mul ?_ h
    have hnorm : Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) atTop atTop :=
      tendsto_natCast_atTop_atTop.congr' (by simp)
    have hsub : (fun n : ℕ ↦ (n : ℝ) - k) ~[atTop] fun n ↦ (n : ℝ) := by
      simpa only [sub_eq_add_neg] using
        (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm (c := -(k : ℝ)))
    apply hsub.congr_left
    filter_upwards [eventually_ge_atTop k] with n hn
    change (n : ℝ) - k = ((n - k : ℕ) : ℝ)
    exact (Nat.cast_sub hn).symm

/-- `n.choose k` is asymptotically equivalent to `n^k / k!`. -/
theorem isEquivalent_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ)) ~[atTop] (fun (n : ℕ) ↦ (n ^ k / k.factorial : ℝ)) := by
  conv_lhs =>
    intro n
    rw [choose_eq_descFactorial_div_factorial,
      cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

/-- `n.choose k` is big-theta `n^k`. -/
theorem isTheta_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ)) =Θ[atTop] (fun (n : ℕ) ↦ (n ^ k : ℝ)) := by
  apply (isEquivalent_choose k).trans_isTheta
  have hk : IsUnit (k.factorial : ℝ) := (Nat.cast_ne_zero.mpr k.factorial_ne_zero).isUnit
  have ht : (fun n : ℕ ↦ Checked.inv (k.factorial : ℝ) hk * (n ^ k : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n ^ k : ℝ)) :=
    isTheta_rfl.const_mul_left (inv_ne_zero (ha := hk))
  simpa only [div_eq_mul_inv₀, mul_comm] using ht

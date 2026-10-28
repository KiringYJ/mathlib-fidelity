/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Diophantine Approximation using continued fractions

## Main statements

There are two versions of Legendre's Theorem.`Real.exists_rat_eq_convergent`,
defined in `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`, uses `Real.convergent`,
a simple recursive definition of the convergents that is also defined in that file.
This file provides `Real.exists_convs_eq_rat`, using `GenContFract.convs` of `GenContFract.of ξ`.
-/

public section

section Convergent

namespace Real

open Int

/-!
Our `convergent`s agree with `GenContFract.convs`.
-/

open GenContFract

/-- The `n`th convergent of the `GenContFract.of ξ` agrees with `ξ.convergent n`. -/
theorem convs_eq_convergent (ξ : ℝ) (n : ℕ) :
    (GenContFract.of ξ).convs n = ξ.convergent n := by
  induction n generalizing ξ with
  | zero => simp only [zeroth_conv_eq_h, of_h_eq_floor, convergent_zero, Rat.cast_intCast]
  | succ n ih =>
    rcases eq_or_ne (fract ξ) 0 with hξ | hξ
    · -- `ξ` is an integer, so its continued fraction terminates at once
      have hterm : (GenContFract.of ξ).TerminatedAt 0 :=
        of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
          (IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero ξ) hξ)
      rw [← of_correctness_of_terminatedAt (terminated_stable (Nat.zero_le (n + 1)) hterm),
        convergent_succ_of_fract_eq_zero _ _ hξ, Rat.cast_intCast]
      exact eq_of_sub_eq_zero hξ
    · rw [convs_succ hξ, convergent_succ _ _ hξ]
      simp only [ih, one_div₀, Rat.cast_add, Rat.cast_inv, Rat.cast_intCast]

end Real

end Convergent

namespace Real

variable {ξ : ℝ}

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This is the version using `GenContFract.convs`. -/
theorem exists_convs_eq_rat {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) : ∃ n, (GenContFract.of ξ).convs n = q := by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact ⟨n, hn.symm ▸ convs_eq_convergent ξ n⟩

end Real

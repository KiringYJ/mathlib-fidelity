/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.PSeries
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Convergence of `p`-series (complex case)

Here we show convergence of `∑ n : ℕ+, 1 / n ^ p` for complex `p`. This is done in a separate file
rather than in `Analysis.PSeries` in order to keep the prerequisites of the former relatively light.

## Tags

p-series, Cauchy condensation test
-/

public section

lemma Complex.summable_one_div_nat_cpow {p : ℂ} :
    Summable (fun n : ℕ+ ↦ Checked.div 1 (((n : ℕ) : ℂ) ^ p)
      (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit) ↔
      1 < re p := by
  rw [← summable_norm_iff]
  have hterm (n : ℕ+) :
      ‖Checked.div 1 (((n : ℕ) : ℂ) ^ p)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit‖ =
      Checked.div 1 (((n : ℕ) : ℝ) ^ p.re)
        (Real.rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) p.re).isUnit := by
    simp only [norm_div, norm_one, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr n.pos)]
  simp_rw [hterm]
  exact Real.summable_one_div_nat_rpow

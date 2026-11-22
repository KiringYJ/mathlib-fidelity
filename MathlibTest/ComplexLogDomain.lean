/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral

/-! Positive-index logarithmic series and their actual-domain limit consumers. -/

open Filter
open scoped Topology

noncomputable section

-- The Taylor index still bounds the degree strictly, and includes the linear term at two.
example (z : ℂ) : Complex.logTaylor 2 z = z := by
  simp [Complex.logTaylor]

example (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ (n + 1) / ((n : ℂ) + 1)) (-Complex.log (1 - z)) :=
  Complex.hasSum_taylorSeries_neg_log hz

-- Taking even and odd terms of the shifted logarithmic series preserves the arctangent series.
example : HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ (2 * n + 1) / (2 * (n : ℝ) + 1))
    (Real.arctan (1 / 2)) := by
  have hs := Real.hasSum_arctan (x := (1 / 2 : ℝ)) (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hs

-- A usual natural sequence is recovered by the positive-index map, without a value at zero.
example (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 + t / (n + 1 : ℝ)) ^ (n + 1)) atTop (𝓝 (Real.exp t)) := by
  have hshift : Tendsto
      (fun n : ℕ ↦ (⟨n + 1, n.succ_ne_zero⟩ : {n : ℕ // n ≠ 0})) atTop
      (comap Subtype.val atTop) := tendsto_comap_iff.2 (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def] using (Real.tendsto_one_add_div_pow_exp t).comp hshift

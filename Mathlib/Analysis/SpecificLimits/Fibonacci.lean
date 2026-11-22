/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The ratio of consecutive Fibonacci numbers

We prove that the ratio of consecutive Fibonacci numbers tends to the golden ratio.
-/

public section

open Nat Real Filter Tendsto
open scoped Topology goldenRatio

/-- The limit of `fib (n + 1) / fib n` as `n → ∞` is the golden ratio. -/
theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      Checked.div (fib ((n : ℕ) + 1) : ℝ) (fib (n : ℕ) : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.fib_pos.mpr (Nat.pos_of_ne_zero n.property)).ne').isUnit)
      (comap Subtype.val atTop) (𝓝 φ) := by
  have hψ : |ψ| < 1 := abs_lt.mpr ⟨neg_one_lt_goldenConj, goldenConj_neg.trans zero_lt_one⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ψ) hψ).comp tendsto_comap)
  have h₁ : (1 : ℝ) ≤ (fib (n : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.fib_pos.mpr (Nat.pos_of_ne_zero n.property))
  have hn : (fib (n : ℕ) : ℝ) ≠ 0 := (zero_lt_one.trans_le h₁).ne'
  have he : (fib ((n : ℕ) + 1) : ℝ) / (fib (n : ℕ) : ℝ) - φ =
      ψ ^ (n : ℕ) / (fib (n : ℕ) : ℝ) := by
    apply eq_div_iff.2
    rw [sub_mul, div_mul_cancel₀, fib_succ_sub_goldenRatio_mul_fib]
  rw [he, Real.norm_eq_abs, abs_div, abs_pow, div_le_iff₀ (abs_pos.mpr hn)]
  exact le_mul_of_one_le_right (by positivity) (h₁.trans (le_abs_self _))

/-- The limit of `fib n / fib (n + 1)` as `n → ∞` is the negative conjugate of the golden ratio. -/
theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n ↦ Checked.div (fib n : ℝ) (fib (n + 1) : ℝ)
      (Nat.cast_ne_zero.mpr (Nat.fib_pos.mpr (Nat.succ_pos n)).ne').isUnit) atTop (𝓝 (-ψ)) := by
  have hnum (n : {n : ℕ // n ≠ 0}) : (fib ((n : ℕ) + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.fib_pos.mpr (Nat.succ_pos _)).ne'
  have hinv := tendsto_fib_succ_div_fib_atTop.inv₀
    (h0 := fun n ↦ (div_ne_zero (hnum n)).isUnit) (ha := goldenRatio_ne_zero.isUnit)
  have hshift : Tendsto (fun n : ℕ ↦ (⟨n + 1, n.succ_ne_zero⟩ : {n : ℕ // n ≠ 0})) atTop
      (comap Subtype.val atTop) := tendsto_comap_iff.2 (tendsto_add_atTop_nat 1)
  apply (tendsto_add_atTop_iff_nat 1).mp
  rw [← inv_goldenRatio]
  simpa only [Function.comp_def, inv_div₀] using hinv.comp hshift

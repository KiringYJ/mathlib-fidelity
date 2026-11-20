/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Asymptotics Filter
open scoped Topology

-- The bounded function need not have an ambient extension or a value at the missing point.
example {a : ℝ} {f : {x : ℝ // x ≠ a} → ℝ}
    (h : IsBoundedUnder (· ≤ ·) (comap Subtype.val (𝓝[≠] a)) (norm ∘ f)) :
    f =o[comap Subtype.val (𝓝[≠] a)]
      (fun x : {x : ℝ // x ≠ a} ↦ Checked.inv ((x : ℝ) - a)
        (sub_ne_zero.mpr x.2).isUnit) :=
  h.isLittleO_sub_self_inv tendsto_comap

-- A zero exponent in the denominator retains zero in the quotient domain.
example :
    Tendsto (fun x : {x : ℝ // x ^ 0 ≠ 0} ↦
      Checked.div ((x : ℝ) ^ 1) ((x : ℝ) ^ 0) x.2.isUnit)
      (comap Subtype.val atTop) atTop :=
  tendsto_pow_div_pow_atTop_atTop (by decide : 0 < 1)

example :
    let x : {x : ℝ // x ^ 0 ≠ 0} := ⟨0, by simp⟩
    Checked.div ((x : ℝ) ^ 1) ((x : ℝ) ^ 0) x.2.isUnit = 0 := by
  simp [div_one₀]

-- Positive denominator powers are evaluated on their actual nonzero domain.
example :
    Tendsto (fun x : {x : ℝ // x ^ 1 ≠ 0} ↦
      Checked.div ((x : ℝ) ^ 0) ((x : ℝ) ^ 1) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) :=
  tendsto_pow_div_pow_atTop_zero (by decide : 0 < 1)

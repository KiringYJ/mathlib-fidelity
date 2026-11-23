/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-! Zero terms and characteristic two matter when a quotient limit uses a restricted domain. -/

open Filter
open scoped Topology

-- The geometric series includes its exponent-zero term even at base zero.
example : HasSum (fun n : ℕ ↦ (0 : ℝ) ^ n) 1 := by
  simpa using hasSum_geometric_of_abs_lt_one (r := (0 : ℝ)) (by norm_num)

-- The denominator at index zero can vanish in characteristic two.
example {R : Type*} [Field R] (h2 : (2 : R) = 0) :
    1 + (0 : R) ^ (0 : ℕ) = 0 := by
  simpa only [pow_zero, one_add_one_eq_two] using h2

-- An empty ratio domain has every limit, while the zero sequence remains summable.
example : Tendsto
    (fun n : {_n : ℕ // ‖(0 : ℝ)‖ ≠ 0} ↦
      Checked.div ‖(0 : ℝ)‖ ‖(0 : ℝ)‖ n.2.isUnit)
    (comap Subtype.val (atTop : Filter ℕ)) (𝓝 (2 : ℝ)) := by
  let : IsEmpty {_n : ℕ // ‖(0 : ℝ)‖ ≠ 0} := ⟨fun n ↦ n.2 (norm_zero)⟩
  exact tendsto_of_isEmpty

example : Summable (fun _ : ℕ ↦ (0 : ℝ)) := summable_zero

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example : ℝ := (0 : ℝ)⁻¹

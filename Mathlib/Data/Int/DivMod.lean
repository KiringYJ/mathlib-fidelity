/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public import Mathlib.Lean.Elab.NativeDivision

/-!
# Basic lemmas about division and modulo for integers

-/

public section

namespace Int

/-! ### `ediv` and `fdiv` -/

theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 ≤ a) (b : Int) {c : Int} (hc : 0 < c) :
    a * Int.euclideanDiv b c (Int.ne_of_gt hc) ≤ Int.euclideanDiv (a * b) c (Int.ne_of_gt hc) := by
  rw [Int.euclideanDiv_eq_core, Int.euclideanDiv_eq_core, Int.le_ediv_iff_mul_le hc, Int.mul_assoc]
  exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hc)) ha

theorem fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) :
    (m.fdiv n).fdiv k = m.fdiv (n * k) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn,
    Int.fdiv_eq_ediv_of_nonneg _ hk,
    Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk),
    ediv_ediv_of_nonneg hn]

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (sub_emod_right a b).symm

end Int

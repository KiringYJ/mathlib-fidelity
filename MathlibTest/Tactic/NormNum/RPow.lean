/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
module
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/- Tests for `Real.rpow` -/

example : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num1
example : (1 : ℝ) ^ (20 : ℝ) = 1 := by norm_num1
example : (-2 : ℝ) ^ (3 : ℝ) = -8 := by norm_num1
example : (1/5 : ℝ) ^ (2 : ℝ) = 1/25 := by norm_num1
example : (-1/3 : ℝ) ^ (-3 : ℝ) = -27 := by norm_num1
example : (1/2 : ℝ) ^ (-3 : ℝ) = 8 := by norm_num1
example : (2 : ℝ) ^ (-3 : ℝ) = 1/8 := by norm_num1
example : (-2 : ℝ) ^ (-3 : ℝ) = -1/8 := by norm_num1

example : (8 : ℝ) ^ (2 / 6 : ℝ) = 2 := by norm_num1
example : (0 : ℝ) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (8 / 27 : ℝ) ^ (1 / 3 : ℝ) = 2 / 3 := by norm_num1
example : (8 : ℝ) ^ (-1 / 3 : ℝ) = 1 / 2 := by norm_num1
example : (8 / 27 : ℝ) ^ (-1 / 3 : ℝ) = 3 / 2 := by norm_num1
example : (1 / 27 : ℝ) ^ (-1 / 3 : ℝ) = 3 := by norm_num1

example : (0 : ℝ) ^ (0 : ℝ) = 1 := by norm_num1
example : (0 : ℝ) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (0 : ℝ) ^ (-1 / 3 : ℝ) = 0 := by norm_num1

-- The following example is incorrect with the current Mathlib definition.
/--
error: unsolved goals
⊢ (-8) ^ (1 / 3) = -2
-/
#guard_msgs in
example : (-8 : ℝ) ^ (1 / 3 : ℝ) = -2 := by
  norm_num1

/- Tests for `NNReal.rpow` -/

open NNReal

example : (2 : ℝ≥0) ^ (3 : ℝ) = 8 := by norm_num1
example : (1 : ℝ≥0) ^ (20 : ℝ) = 1 := by norm_num1
example : (1/5 : ℝ≥0) ^ (2 : ℝ) = 1/25 := by norm_num1
example : (1/2 : ℝ≥0) ^ (-3 : ℝ) = 8 := by norm_num1
example : (2 : ℝ≥0) ^ (-3 : ℝ) = 1/8 := by norm_num1

example : (8 : ℝ≥0) ^ (2 / 6 : ℝ) = 2 := by norm_num1
example : (0 : ℝ≥0) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (8 / 27 : ℝ≥0) ^ (1 / 3 : ℝ) = 2 / 3 := by norm_num1
example : (8 : ℝ≥0) ^ (-1 / 3 : ℝ) = 1 / 2 := by norm_num1
example : (8 / 27 : ℝ≥0) ^ (-1 / 3 : ℝ) = 3 / 2 := by norm_num1
example : (1 / 27 : ℝ≥0) ^ (-1 / 3 : ℝ) = 3 := by norm_num1

example : (0 : ℝ≥0) ^ (0 : ℝ) = 1 := by norm_num1
example : (0 : ℝ≥0) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (0 : ℝ≥0) ^ (-1 / 3 : ℝ) = 0 := by norm_num1

-- Other `norm_num` extensions consume the raw natural-number literal in this result.
open Lean Qq Mathlib.Meta.NormNum in
run_meta do
  let check {α : Q(Type)} (e : Q($α)) : MetaM Unit := do
    match ← derive e with
    | .isNat _ (.lit (.natVal 0)) _ => pure ()
    | _ => throwError "expected a raw zero literal for {e}"
  check q((0 : ℝ) ^ (-1 / 3 : ℝ))
  check q((0 : ℝ) ^ (-3 : ℝ))
  check q((0 : ℝ≥0) ^ (-1 / 3 : ℝ))
  check q((0 : ℝ≥0) ^ (-3 : ℝ))

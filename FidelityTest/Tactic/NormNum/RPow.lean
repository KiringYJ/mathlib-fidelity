/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
module
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped NNReal

-- Other `norm_num` extensions consume the raw natural-number literal in this result.
open Lean Qq Mathlib.Meta.NormNum in
run_meta do
  let check {α : Q(Type)} (e : Q($α)) : MetaM Unit := do
    match ← derive e with
    | .isNat _ (.lit (.natVal 0)) _ => pure ()
    | _ => throwError "expected a raw zero literal for {e}"
  check q((0 : ℝ) ^ ((-1 : ℝ) / (3 : ℝ)))
  check q((0 : ℝ) ^ (-3 : ℝ))
  check q((0 : ℝ≥0) ^ ((-1 : ℝ) / (3 : ℝ)))
  check q((0 : ℝ≥0) ^ (-3 : ℝ))

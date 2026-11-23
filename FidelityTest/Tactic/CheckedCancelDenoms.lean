/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Tactic.CancelDenoms
import Mathlib.Tactic.Ring

variable {K : Type*} [Field K] (a b : K)

-- These hypotheses admit positive-characteristic fields; no global rational cast is needed.
example (h2 : (2 : K) ≠ 0) : a / 2 + a / 2 = a := by
  cancel_denoms
  ring

example (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (a / 2 + b / 3) * 6 = 3 * a + 2 * b := by
  cancel_denoms
  ring

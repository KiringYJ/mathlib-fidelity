/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Analysis.Complex.Periodic

/-! Regression tests for the domains of the q-parameter and its logarithmic inverse. -/

open Function.Periodic

noncomputable section

/--
error: could not synthesize default value for parameter 'hh' using tactics
---
error: a nonzero denominator proof is required
⊢ 0 ≠ 0
-/
#guard_msgs in
example : ℂ := qParam 0 0

/--
error: could not synthesize default value for parameter '_hq' using tactics
---
error: a nonzero denominator proof is required
⊢ 0 ≠ 0
-/
#guard_msgs in
example : ℂ := invQParam 1 0

example : qParam 1 (invQParam 1 1 one_ne_zero one_ne_zero) one_ne_zero = 1 :=
  qParam_right_inv one_ne_zero one_ne_zero

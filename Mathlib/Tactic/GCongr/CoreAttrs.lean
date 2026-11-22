/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Elab.NativeDivision
public import Mathlib.Tactic.GCongr.Core

/-!
# gcongr attributes for lemmas up in the import chain

In this file we add `gcongr` attribute to lemmas in `Lean.Init`.
We may add lemmas from other files imported by `Mathlib/Tactic/GCongr/Core` later.
-/

public section

/-- Taking natural quotients by the same nonzero divisor preserves order. -/
@[gcongr] theorem Nat.euclideanDiv_le_euclideanDiv_right {a b c : Nat} {hc : c ≠ 0} (hab : a ≤ b) :
    Nat.euclideanDiv a c hc ≤ Nat.euclideanDiv b c hc := by
  rw [Nat.euclideanDiv_eq_core, Nat.euclideanDiv_eq_core]
  exact Nat.div_le_div_right hab

end

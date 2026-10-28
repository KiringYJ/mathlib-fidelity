/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Tactic.NormNum

/-! # Integer powers of `-1` in a field -/

public section

namespace Int

lemma cast_negOnePow (K : Type*) (n : ℤ) [Ring K] :
    n.negOnePow = (((-1 : Kˣ) ^ n : Kˣ) : K) := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [zpow_mul, zpow_ofNat]
  · rw [zpow_add, zpow_mul, zpow_ofNat]
    simp

end Int

/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Dynamics.BirkhoffSum.Average

/-! The orbit length in a Birkhoff average must be invertible in its coefficient field. -/

noncomputable section

-- The empty orbit segment has no average over the rationals.
/--
error: Tactic `assumption` failed

h : ¬IsUnit ↑0
⊢ IsUnit ↑0
-/
#guard_msgs in
example : ℚ :=
  birkhoffAverage ℚ (id : ℚ → ℚ) id 0 (by
    have h : ¬ IsUnit ((0 : ℕ) : ℚ) := by
      simpa only [Nat.cast_zero] using (not_isUnit_zero : ¬ IsUnit (0 : ℚ))
    assumption) 0

-- A positive length can still cast to zero in the coefficient field.
/--
error: Tactic `assumption` failed

h : ¬IsUnit ↑2
⊢ IsUnit ↑2
-/
#guard_msgs in
example : ZMod 2 :=
  birkhoffAverage (ZMod 2) (id : ZMod 2 → ZMod 2) id 2 (by
    have h : ¬ IsUnit ((2 : ℕ) : ZMod 2) := by
      rw [ZMod.natCast_self]
      exact not_isUnit_zero
    assumption) 0

-- Length three is admissible over `ZMod 2`, and its unit witness is proof-irrelevant.
example (f : ℕ → ℕ) (g : ℕ → ZMod 2) (h : IsUnit ((3 : ℕ) : ZMod 2)) :
    birkhoffAverage (ZMod 2) f g 3 h =
      birkhoffAverage (ZMod 2) f g 3 ((by decide : ((3 : ℕ) : ZMod 2) ≠ 0).isUnit) := rfl

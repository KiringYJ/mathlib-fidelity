/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Cast.Defs

example {K : Type*} [DivisionRing K] (h2 : (2 : K) ≠ 0) :
    ∃ hd : ((Rat.fraction 1 2 (by decide)).den : K) ≠ 0,
      Rat.eval (Rat.fraction 1 2 (by decide)) hd +
      Rat.eval (Rat.fraction 1 2 (by decide)) hd = (1 : K) := by
  have hd : ((Rat.fraction 1 2 (by decide)).den : K) ≠ 0 := by
    change (Nat.cast 2 : K) ≠ 0
    simpa only [Nat.cast_ofNat] using h2
  refine ⟨hd, ?_⟩
  have hsum := Rat.add_den_ne_zero (Rat.fraction 1 2 (by decide))
    (Rat.fraction 1 2 (by decide)) hd hd
  have he : Rat.fraction 1 2 (by decide) + Rat.fraction 1 2 (by decide) = (1 : ℚ) := by
    decide +kernel
  have h1 : ((1 : ℚ).den : K) ≠ 0 := by
    simpa only [Rat.den_ofNat, Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  calc
    _ = Rat.eval (Rat.fraction 1 2 (by decide) + Rat.fraction 1 2 (by decide)) hsum :=
      (Rat.eval_add _ _ hd hd hsum).symm
    _ = Rat.eval 1 h1 := by simp only [he]
    _ = 1 := (Rat.eval_natCast (α := K) 1 h1).trans Nat.cast_one

example {K : Type*} [DivisionRing K] (h3 : (Nat.cast 3 : K) = 0) :
    ¬ ((Rat.fraction 1 3 (by decide)).den : K) ≠ 0 := by
  change ¬ (Nat.cast 3 : K) ≠ 0
  intro h
  exact h h3

example {K : Type*} [DivisionRing K] :
    ∃ h : ((Rat.fraction 3 3 (by decide)).den : K) ≠ 0,
      Rat.eval (Rat.fraction 3 3 (by decide)) h = 1 := by
  have he : Rat.fraction 3 3 (by decide) = (1 : ℚ) := by decide +kernel
  simp only [he]
  have h1 : ((1 : ℚ).den : K) ≠ 0 := by
    simpa only [Rat.den_ofNat, Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  exact ⟨h1, (Rat.eval_natCast (α := K) 1 h1).trans Nat.cast_one⟩

-- The zero numerator does not discharge the original divisor's domain condition.
example {K : Type*} [DivisionRing K] (h3 : (Nat.cast 3 : K) = 0)
    (hd : ((3 : ℚ).den : K) ≠ 0) : ¬ Rat.eval (3 : ℚ) hd ≠ 0 := by
  intro h
  apply h
  exact (Rat.eval_natCast (α := K) 3 hd).trans h3

example : Rat.quotient 0 3 (by decide +kernel) = 0 := by decide +kernel

section CharacteristicFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : Rat.eval (Rat.fractionInt 6 (-4) (by decide)) (by decide) = (1 : ZMod 5) := by
  rw [Rat.eval_fractionInt 6 (-4) (by decide) (by decide : ((-4 : ℤ) : ZMod 5) ≠ 0)]
  exact div_eq_of_eq_mul (by decide)

example : Rat.eval (Rat.fraction 6 4 (by decide)) (by decide) = (4 : ZMod 5) := by
  rw [Rat.eval_fraction 6 4 (by decide) (by decide : (4 : ZMod 5) ≠ 0)]
  exact div_eq_of_eq_mul (by decide)

end CharacteristicFive

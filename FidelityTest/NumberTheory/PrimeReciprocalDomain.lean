/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! Prime denominators carry natural nonzeroness, with characteristic-sensitive scalar casts. -/

noncomputable section

example (p : Nat.Primes) : (p : ℚ) * (p : ℚ)⁻¹ = 1 := mul_inv_cancel₀

example (p q : Nat.Primes) : ℝ := ((p : ℝ) / (q : ℝ))⁻¹

-- Natural nonzeroness does not make the denominator invertible in every characteristic.
example : ¬ IsUnit (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ZMod 2) := by
  norm_num; decide

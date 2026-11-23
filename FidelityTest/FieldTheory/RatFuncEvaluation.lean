import Mathlib.FieldTheory.RatFunc.AsPolynomial

open Polynomial

noncomputable section

private def cancelled : RatFunc ℚ :=
  Checked.div RatFunc.X RatFunc.X RatFunc.X_ne_zero.isUnit

example : RatFunc.eval (RingHom.id ℚ) 0 cancelled (by simp [cancelled, div_self]) = 1 := by
  simp [cancelled, div_self]

private def pole : RatFunc ℚ := Checked.inv RatFunc.X RatFunc.X_ne_zero.isUnit

example : ¬ IsUnit (pole.denom.eval₂ (RingHom.id ℚ) 0) := by
  have hcross : pole.num * Polynomial.X = 1 * pole.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff Polynomial.X_ne_zero).mpr
      (by simp [pole, RatFunc.algebraMap_X, one_div₀])
  have hzero : pole.denom.eval₂ (RingHom.id ℚ) 0 = 0 := by
    simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_zero, Polynomial.eval₂_one, one_mul]
      using (congrArg (Polynomial.eval₂ (RingHom.id ℚ) 0) hcross).symm
  rw [hzero]
  exact not_isUnit_zero

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: unsolved goals
⊢ ¬pole.denom.coeff 0 = 0
-/
#guard_msgs in
example : ℚ := RatFunc.eval (RingHom.id ℚ) 0 pole
